/-
MachCSL: **relational runs of the native walker** (`RelRun`): two runs of the same computation from
states whose register files are related register by register (`Rv`) stay in lock-step, with equal
results and related states.

* `relRun_of_eqRead` (**congruence**, `uxnRun_congr`): if every register the footprint reads is
  related only to itself (`Rv r v w → v = w` when `D.Dr r`), every computation runs in lock-step.
* `relRun_bind`: relational runs compose (so a computation can be cut into stretches, each proven
  relational on its own: the generic congruence for stretches that read only equal registers, and
  a per-function argument for the stretches that read registers whose two values differ, e.g. the
  `mstatus`/`mie`/`mip` of Miralis's payload phase, design note 09 §9).
-/
import MachCSL.UNative

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- A register-by-register relation on register values. -/
abbrev RegRel := (r : Register) → RegisterType r → RegisterType r → Prop

/-- Two native-walker states related by `Rv`: the register files related register by register,
the same memory, dirty bytes and reservation. -/
structure NRel (Rv : RegRel) (s1 s2 : NSt) : Prop where
  file  : ∀ r, Rv r (s1.u.file r) (s2.u.file r)
  T     : s1.T = s2.T
  dirty : s1.dirty = s2.dirty
  rv    : s1.u.rv = s2.u.rv

/-- Two walk results related by `Rv`: the same kind, value (or exit privilege and continuation),
oracle left, and related states. -/
def NResRel {X : Type} (Rv : RegRel) : NRes X → NRes X → Prop
  | .done x1 s1 o1, .done x2 s2 o2 => x1 = x2 ∧ o1 = o2 ∧ NRel Rv s1 s2
  | .exit p1 k1 s1 o1, .exit p2 k2 s2 o2 => p1 = p2 ∧ k1 = k2 ∧ o1 = o2 ∧ NRel Rv s1 s2
  | _, _ => False

/-- **A relational computation** under `(D, B)` and `Rv`: from related states, a run of the first
gives a run of the second with a related result. -/
def RelRun (D : UFoot) (B : Privilege → Bool) (Rv : RegRel) {X : Type} (m : SailM X) : Prop :=
  ∀ (orc : UOrc) (s1 s2 : NSt) (res1 : NRes X), NRel Rv s1 s2 → uxnRun D B orc s1 m = some res1 →
    ∃ res2, uxnRun D B orc s2 m = some res2 ∧ NResRel Rv res1 res2

section rel
variable {D : UFoot} {B : Privilege → Bool} {Rv : RegRel}

/-! ## §1 The bind law of the native walker -/

/-- **The bind law**: a native walk of `m >>= f` is a walk of `m`, then (at a landing) a walk of
`f`; at an exit of `m`, the walk of `m >>= f` exits with the bound continuation. -/
theorem uxnRun_bind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ (orc : UOrc) (s : NSt),
      uxnRun D B orc s (m >>= f) =
        match uxnRun D B orc s m with
        | some (.done x s' o') => uxnRun D B o' s' (f x)
        | some (.exit p k s' o') => some (.exit p (fun u => k u >>= f) s' o')
        | none => none := by
  induction m with
  | pure x => intro orc s; rfl
  | impure c k ih =>
    intro orc s
    change uxnRun D B orc s (FreeM.impure c fun v => k v >>= f) = _
    cases hown : nOwn c with
    | false =>
      rw [uxnw_node D B orc s c _ hown, uxnw_node D B orc s c k hown]
      cases runRW D orc s.u (FreeM.impure c FreeM.pure) with
      | none => rfl
      | some r => exact ih r.1 r.2.2 _
    | true =>
    rcases c with e | op
    · simp [nOwn] at hown
    cases op with
    | regWrite reg p =>
      by_cases hreg : reg = .cur_privilege
      rotate_left
      · cases reg <;> first | exact absurd rfl hreg | simp [nOwn] at hown
      subst hreg
      cases h0 : B (s.u.file .cur_privilege) with
      | false => rw [uxnw_priv_out D B _ s p _ h0, uxnw_priv_out D B _ s p _ h0]
      | true =>
      cases h1 : B p with
      | true =>
        rw [uxnw_priv_quiet D B _ s p _ h0 h1, uxnw_priv_quiet D B _ s p _ h0 h1]
        exact ih () _ _
      | false =>
        rw [uxnw_priv_exit D B _ s p _ h0 h1, uxnw_priv_exit D B _ s p _ h0 h1]
        rfl
    | memRead n vasize req =>
      rw [uxnw_read, uxnw_read]
      split
      · split
        · split
          · exact ih _ _ _
          · split
            · exact ih _ _ _
            · exact ih _ _ _
        · rfl
      · rfl
    | memWrite n vasize req =>
      rw [uxnw_write, uxnw_write]
      split
      · split
        · split
          · exact ih _ _ _
          · rfl
        · rfl
      · rfl
    | _ => simp [nOwn] at hown

/-! ## §2 Relational runs -/

theorem relRun_pure {X : Type} (x : X) : RelRun D B Rv (FreeM.pure x : SailM X) := by
  intro orc s1 s2 res1 hrel h
  simp only [uxnRun, Option.some.injEq] at h
  subst h
  exact ⟨_, rfl, rfl, rfl, hrel⟩

/-- **Relational runs compose.** The exit continuations of `m` must be the same in both runs
(`NResRel`), so the bound exit continuations are equal too. -/
theorem relRun_bind {X Y : Type} {m : SailM X} {f : X → SailM Y} (hm : RelRun D B Rv m)
    (hf : ∀ x, RelRun D B Rv (f x)) : RelRun D B Rv (m >>= f) := by
  intro orc s1 s2 res1 hrel h
  rw [uxnRun_bind] at h ⊢
  cases h1 : uxnRun D B orc s1 m with
  | none => rw [h1] at h; cases h
  | some r1 =>
    rw [h1] at h
    obtain ⟨r2, h2, hr⟩ := hm orc s1 s2 r1 hrel h1
    rw [h2]
    cases r1 with
    | done x1 s1' o1 =>
      cases r2 with
      | done x2 s2' o2 =>
        obtain ⟨rfl, rfl, hrel'⟩ := hr
        exact hf x1 o1 s1' s2' res1 hrel' h
      | exit => exact hr.elim
    | exit p1 k1 s1' o1 =>
      cases r2 with
      | done => exact hr.elim
      | exit p2 k2 s2' o2 =>
        obtain ⟨rfl, rfl, rfl, hrel'⟩ := hr
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, rfl, rfl, rfl, hrel'⟩

/-- Related files stay related under the same register write (`Rv` reflexive). -/
theorem nrel_setPin (hrefl : ∀ r v, Rv r v v) {s1 s2 : NSt} (hrel : NRel Rv s1 s2) (r : Register)
    (v : RegisterType r) :
    NRel Rv { s1 with u := { s1.u with pin := s1.u.pin.set r v } }
      { s2 with u := { s2.u with pin := s2.u.pin.set r v } } where
  file r' := by
    show Rv r' (({ s1.u with pin := s1.u.pin.set r v } : UWSt).file r')
      (({ s2.u with pin := s2.u.pin.set r v } : UWSt).file r')
    rw [UWSt.file_setPin, UWSt.file_setPin]
    unfold RegFile.set BootRegs.set
    by_cases h : r' = r
    · subst h; simp only [dite_true]; exact hrefl _ _
    · simp only [h, dite_false]; exact hrel.file r'
  T := hrel.T
  dirty := hrel.dirty
  rv := hrel.rv

/-- **One `runRW` node, relationally**: when every register the footprint reads is related only to
itself, a node gives the same value and leaves related states. -/
theorem runRW_node_rel (hrefl : ∀ r v, Rv r v v) (heq : ∀ r, D.Dr r = true → ∀ v w, Rv r v w → v = w)
    (c : Eff RegisterType exception) (hown : nOwn c = false) (orc : UOrc) (s1 s2 : NSt)
    (hrel : NRel Rv s1 s2) (r1 : ArchSem.Effect.ret c × UWSt × UOrc)
    (h : runRW D orc s1.u (FreeM.impure c FreeM.pure) = some r1) :
    ∃ u2, runRW D orc s2.u (FreeM.impure c FreeM.pure) = some (r1.1, u2, r1.2.2) ∧
      NRel Rv { s1 with u := r1.2.1 } { s2 with u := u2 } := by
  rcases c with e | op
  · simp [runRW] at h
  · cases op with
    | regRead reg =>
      cases hd : D.Dr reg with
      | true =>
        have hv : s1.u.file reg = s2.u.file reg := heq reg hd _ _ (hrel.file reg)
        have e1 : runRW D orc s1.u (FreeM.impure (.ok (.regRead reg)) FreeM.pure) =
            some (s1.u.file reg, s1.u, orc) := by
          simp only [runRW, hd, if_true]; unfold UWSt.file; split <;> simp_all
        have e2 : runRW D orc s2.u (FreeM.impure (.ok (.regRead reg)) FreeM.pure) =
            some (s2.u.file reg, s2.u, orc) := by
          simp only [runRW, hd, if_true]; unfold UWSt.file; split <;> simp_all
        rw [e1] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨s2.u, by rw [e2, hv], hrel⟩
      | false =>
        cases ha : D.Dany reg with
        | false => simp [runRW, hd, ha] at h
        | true =>
          simp only [runRW, hd, ha, Bool.false_eq_true, if_false, if_true, Option.some.injEq] at h
          subst h
          refine ⟨s2.u, ?_, hrel⟩
          simp only [runRW, hd, ha, Bool.false_eq_true, if_false, if_true]
    | regWrite reg v =>
      cases hd : D.Dw reg with
      | false => simp [runRW, hd] at h
      | true =>
        simp only [runRW, hd, if_true, Option.some.injEq] at h
        subst h
        refine ⟨{ s2.u with pin := s2.u.pin.set reg v }, ?_, nrel_setPin hrefl hrel reg v⟩
        simp only [runRW, hd, if_true]
    | memRead => simp [nOwn] at hown
    | memWrite => simp [nOwn] at hown
    | choose p =>
      simp only [runRW, Option.some.injEq] at h
      subst h
      exact ⟨s2.u, by simp only [runRW], hrel⟩
    | readRam => simp [runRW] at h
    | writeRam => simp [runRW] at h
    | _ =>
      simp only [runRW, Option.some.injEq] at h
      subst h
      exact ⟨s2.u, by simp only [runRW], hrel⟩

/-- **The congruence of the native walker** (`uxnRun_congr`): when every register the footprint
reads is related only to itself (and `cur_privilege`, which the walker reads, too), every
computation runs in lock-step from related states. -/
theorem relRun_of_eqRead (hrefl : ∀ r v, Rv r v v)
    (heq : ∀ r, D.Dr r = true → ∀ v w, Rv r v w → v = w)
    (hpriv : ∀ v w, Rv .cur_privilege v w → v = w) {X : Type} (m : SailM X) : RelRun D B Rv m := by
  induction m with
  | pure x => exact relRun_pure x
  | impure c k ih =>
    intro orc s1 s2 res1 hrel h
    cases hown : nOwn c with
    | false =>
      rw [uxnw_node D B orc s1 c k hown] at h
      rw [uxnw_node D B orc s2 c k hown]
      cases h1 : runRW D orc s1.u (FreeM.impure c FreeM.pure) with
      | none => rw [h1] at h; cases h
      | some r1 =>
        rw [h1] at h
        obtain ⟨u2, h2, hrel'⟩ := runRW_node_rel hrefl heq c hown orc s1 s2 hrel r1 h1
        rw [h2]
        exact ih r1.1 r1.2.2 _ _ res1 hrel' h
    | true =>
    rcases c with e | op
    · simp [nOwn] at hown
    have hp : s1.u.file .cur_privilege = s2.u.file .cur_privilege := hpriv _ _ (hrel.file _)
    cases op with
    | regWrite reg p =>
      by_cases hreg : reg = .cur_privilege
      rotate_left
      · cases reg <;> first | exact absurd rfl hreg | simp [nOwn] at hown
      subst hreg
      cases h0 : B (s1.u.file .cur_privilege) with
      | false => rw [uxnw_priv_out D B _ s1 p k h0] at h; cases h
      | true =>
      have h0' : B (s2.u.file .cur_privilege) = true := by rw [← hp]; exact h0
      cases h1 : B p with
      | true =>
        rw [uxnw_priv_quiet D B _ s1 p k h0 h1] at h
        rw [uxnw_priv_quiet D B _ s2 p k h0' h1]
        exact ih () orc _ _ res1 (nrel_setPin hrefl hrel _ p) h
      | false =>
        rw [uxnw_priv_exit D B _ s1 p k h0 h1] at h
        rw [uxnw_priv_exit D B _ s2 p k h0' h1]
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, rfl, rfl, rfl, hrel⟩
    | memRead n vasize req =>
      rw [uxnw_read] at h
      rw [uxnw_read, ← hrel.T, ← hrel.dirty]
      split at h
      · rename_i hn
        rw [if_pos hn]
        split at h
        · rename_i w hw
          try rw [hw]
          try dsimp only
          split at h
          · rename_i hd
            rw [if_pos hd]
            exact ih _ _ s1 s2 res1 hrel h
          · rename_i hd
            rw [if_neg hd]
            split at h
            · rename_i hx
              rw [if_pos hx]
              exact ih _ orc { s1 with u := { s1.u with rv := true } } _ res1 ⟨hrel.file, rfl, rfl, rfl⟩ h
            · rename_i hx
              rw [if_neg hx]
              exact ih _ _ s1 s2 res1 hrel h
        · cases h
      · cases h
    | memWrite n vasize req =>
      rw [uxnw_write] at h
      rw [uxnw_write, ← hrel.T]
      split at h
      · rename_i hn
        rw [if_pos hn]
        split at h
        · rename_i w' hv
          try rw [hv]
          try dsimp only
          split at h
          · rename_i ho
            rw [if_pos ho]
            exact ih _ orc ⟨{ s1.u with rv := false }, bmWrite s1.T req.pa n w', dirtyAdd s1.dirty req.pa n⟩ _
              res1 ⟨hrel.file, rfl, by rw [hrel.dirty], rfl⟩ h
          · cases h
        · cases h
      · cases h
    | _ => simp [nOwn] at hown

/-! ## §3 Heterogeneous relational runs: reads of registers with different values -/

/-- **A heterogeneous relational pair**: from related states, a run of `m1` gives a run of `m2`
with a related result. A register read whose two values differ continues with two different
computations (`k v`, `k w`), hence the two sides. -/
def RelRun2 (D : UFoot) (B : Privilege → Bool) (Rv : RegRel) {X : Type} (m1 m2 : SailM X) : Prop :=
  ∀ (orc : UOrc) (s1 s2 : NSt) (res1 : NRes X), NRel Rv s1 s2 → uxnRun D B orc s1 m1 = some res1 →
    ∃ res2, uxnRun D B orc s2 m2 = some res2 ∧ NResRel Rv res1 res2

theorem relRun2_of_relRun {X : Type} {m : SailM X} (h : RelRun D B Rv m) : RelRun2 D B Rv m m := h

/-- Heterogeneous pairs compose; the exit continuations must coincide, so both sides must exit
with the same continuation (`NResRel`), which is why `f` is shared. -/
theorem relRun2_bind {X Y : Type} {m1 m2 : SailM X} {f : X → SailM Y} (hm : RelRun2 D B Rv m1 m2)
    (hf : ∀ x, RelRun D B Rv (f x)) : RelRun2 D B Rv (m1 >>= f) (m2 >>= f) := by
  intro orc s1 s2 res1 hrel h
  rw [uxnRun_bind] at h ⊢
  cases h1 : uxnRun D B orc s1 m1 with
  | none => rw [h1] at h; cases h
  | some r1 =>
    rw [h1] at h
    obtain ⟨r2, h2, hr⟩ := hm orc s1 s2 r1 hrel h1
    rw [h2]
    cases r1 with
    | done x1 s1' o1 =>
      cases r2 with
      | done x2 s2' o2 =>
        obtain ⟨rfl, rfl, hrel'⟩ := hr
        exact hf x1 o1 s1' s2' res1 hrel' h
      | exit => exact hr.elim
    | exit p1 k1 s1' o1 =>
      cases r2 with
      | done => exact hr.elim
      | exit p2 k2 s2' o2 =>
        obtain ⟨rfl, rfl, rfl, hrel'⟩ := hr
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, rfl, rfl, rfl, hrel'⟩

/-- **A read of a register whose two values may differ** (readable by `D`): the pair is
relational when, for every two related values, the continuations are a relational pair. -/
theorem relRun2_regRead {X : Type} (r : Register) (hd : D.Dr r = true) (hr : r ≠ .cur_privilege)
    (k1 k2 : RegisterType r → SailM X)
    (hk : ∀ v w, Rv r v w → RelRun2 D B Rv (k1 v) (k2 w)) :
    RelRun2 D B Rv (FreeM.impure (.ok (.regRead r)) k1) (FreeM.impure (.ok (.regRead r)) k2) := by
  intro orc s1 s2 res1 hrel h
  have hown : nOwn (.ok (.regRead r) : Eff RegisterType exception) = false := rfl
  have e : ∀ (s : NSt) (k : RegisterType r → SailM X),
      uxnRun D B orc s (FreeM.impure (.ok (.regRead r)) k) = uxnRun D B orc s (k (s.u.file r)) := by
    intro s k
    rw [uxnw_node D B orc s _ k hown]
    have : runRW D orc s.u (FreeM.impure (.ok (.regRead r)) FreeM.pure) =
        some (s.u.file r, s.u, orc) := by
      simp only [runRW, hd, if_true]; unfold UWSt.file; split <;> simp_all
    rw [this]
    rfl
  rw [e] at h
  rw [e]
  exact hk _ _ (hrel.file r) orc s1 s2 res1 hrel h

/-- Equal computations whose reads all go through equal registers. -/
theorem relRun2_refl_of_eqRead (hrefl : ∀ r v, Rv r v v)
    (heq : ∀ r, D.Dr r = true → ∀ v w, Rv r v w → v = w)
    (hpriv : ∀ v w, Rv .cur_privilege v w → v = w) {X : Type} (m : SailM X) :
    RelRun2 D B Rv m m :=
  relRun_of_eqRead hrefl heq hpriv m

end rel

end MachCSL
