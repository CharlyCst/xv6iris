/-
MachCSL: **monotonicity of the native walker** in its footprint and untrusted set
(`uxnRun_mono`), and the **unrestricted** native walker (`fullFoot`, `uxnFull`): the pure semantics
of one Sail step on a register file and a memory, with every register readable and writable and
every privilege write taken.

This is the bridge between the walk rule (`swp_uxnRun`, over a restricted footprint `D` and the
untrusted set `B`) and a client's reference semantics stated with the unrestricted walker: a walk
that lands under `(D, B)` lands identically under `(fullFoot, all)`, and a walk that stops at an
exit node under `(D, B)` is, under `(fullFoot, all)`, the walk from that node on.
(Miralis states its payload reference step `refStepP` with `prRun`, which is meant to be
`uxnFull` once the submodule moves; see Miralis `Payload/NativeStep.lean`.)
-/
import MachCSL.UNative

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `D` is below `D'`: every register `D` reads or writes, `D'` does too, and `D` answers no
register from the oracle (so the two walks read the same values). -/
structure UFootLe (D D' : UFoot) : Prop where
  rd : ∀ r, D.Dr r = true → D'.Dr r = true
  wr : ∀ r, D.Dw r = true → D'.Dw r = true
  noAny : ∀ r, D.Dr r = false → D.Dany r = false

/-- **One `runRW` node is monotone in the footprint.** -/
theorem runRW_node_mono {D D' : UFoot} (hle : UFootLe D D') (c : Eff RegisterType exception)
    (orc : UOrc) (s : UWSt) (r : ArchSem.Effect.ret c × UWSt × UOrc)
    (h : runRW D orc s (FreeM.impure c FreeM.pure) = some r) :
    runRW D' orc s (FreeM.impure c FreeM.pure) = some r := by
  rcases c with e | op
  · simp [runRW] at h
  · cases op with
    | regRead reg =>
      cases hd : D.Dr reg with
      | true =>
        simp only [runRW, hd, if_true] at h
        simp only [runRW, hle.rd reg hd, if_true]
        exact h
      | false =>
        simp only [runRW, hd, hle.noAny reg hd, Bool.false_eq_true, if_false] at h
        cases h
    | regWrite reg v =>
      cases hd : D.Dw reg with
      | true =>
        simp only [runRW, hd, if_true] at h
        simp only [runRW, hle.wr reg hd, if_true]
        exact h
      | false =>
        simp only [runRW, hd, Bool.false_eq_true, if_false] at h
        cases h
    | _ => simpa only [runRW] using h

/-- **The native walker is monotone in its footprint and untrusted set**: a landing under
`(D, B)` is a landing under `(D', B')`; an exit under `(D, B)` continues under `(D', B')` as the
walk from the exit node. -/
theorem uxnRun_mono {D D' : UFoot} (hle : UFootLe D D') {B B' : Privilege → Bool}
    (hB : ∀ p, B p = true → B' p = true) {X : Type} (m : SailM X) :
    ∀ (orc : UOrc) (s : NSt) (res : NRes X), uxnRun D B orc s m = some res →
      match res with
      | .done x s' o' => uxnRun D' B' orc s m = some (.done x s' o')
      | .exit p k s' o' => uxnRun D' B' orc s m =
          uxnRun D' B' o' s' (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) := by
  induction m with
  | pure x =>
    intro orc s res h
    simp only [uxnRun, Option.some.injEq] at h
    subst h
    rfl
  | impure c k ih =>
    intro orc s res h
    cases hown : nOwn c with
    | false =>
      rw [uxnw_node D B orc s c k hown] at h
      rw [uxnw_node D' B' orc s c k hown]
      cases hr : runRW D orc s.u (FreeM.impure c FreeM.pure) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        rw [runRW_node_mono hle c orc s.u r hr]
        exact ih r.1 r.2.2 { s with u := r.2.1 } res h
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
      | false => rw [uxnw_priv_out D B _ s p k h0] at h; cases h
      | true =>
      have h0' := hB _ h0
      cases h1 : B p with
      | true =>
        rw [uxnw_priv_quiet D B _ s p k h0 h1] at h
        rw [uxnw_priv_quiet D' B' _ s p k h0' (hB p h1)]
        exact ih () orc _ res h
      | false =>
        rw [uxnw_priv_exit D B _ s p k h0 h1] at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
    | memRead n vasize req =>
      rw [uxnw_read] at h
      rw [uxnw_read]
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
            exact ih _ _ _ res h
          · rename_i hd
            rw [if_neg hd]
            split at h
            · rename_i hx
              rw [if_pos hx]
              exact ih _ _ _ res h
            · rename_i hx
              rw [if_neg hx]
              exact ih _ _ _ res h
        · cases h
      · cases h
    | memWrite n vasize req =>
      rw [uxnw_write] at h
      rw [uxnw_write]
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
            exact ih _ _ _ res h
          · cases h
        · cases h
      · cases h
    | _ => simp [nOwn] at hown

/-- The unrestricted footprint: every register readable, every register but `cur_privilege`
writable by a node (privilege writes are the walker's own arm), none from the oracle. -/
def fullFoot : UFoot where
  Dr _ := true
  Dw r := r != .cur_privilege
  Dany _ := false
  noPriv := by decide

theorem uFootLe_full (D : UFoot) (hD : ∀ r, D.Dr r = false → D.Dany r = false) :
    UFootLe D fullFoot where
  rd _ _ := rfl
  wr r h := by
    show (r != .cur_privilege) = true
    by_cases hr : r = .cur_privilege
    · subst hr; rw [D.noPriv] at h; cases h
    · simp [hr]
  noAny := hD

/-- **The unrestricted native walker**: Sail on a register file and a memory, every privilege
write taken (never an exit). -/
abbrev uxnFull {X : Type} : UOrc → NSt → SailM X → Option (NRes X) :=
  uxnRun fullFoot (fun _ => true)

/-- The unrestricted walker never stops at an exit. -/
theorem uxnFull_no_exit {X : Type} (m : SailM X) :
    ∀ (orc : UOrc) (s : NSt) (p : Privilege) (k : PUnit → SailM X) (s' : NSt) (o' : UOrc),
      uxnFull orc s m ≠ some (.exit p k s' o') := by
  induction m with
  | pure x => intro orc s p k s' o' h; simp [uxnRun] at h
  | impure c k' ih =>
    intro orc s p k s' o' h
    change uxnRun fullFoot (fun _ => true) orc s (FreeM.impure c k') = _ at h
    cases hown : nOwn c with
    | false =>
      rw [uxnw_node fullFoot (fun _ => true) orc s c k' hown] at h
      cases hr : runRW fullFoot orc s.u (FreeM.impure c FreeM.pure) with
      | none => rw [hr] at h; cases h
      | some r => rw [hr] at h; exact ih r.1 r.2.2 _ p k s' o' h
    | true =>
    rcases c with e | op
    · simp [nOwn] at hown
    cases op with
    | regWrite reg v =>
      by_cases hreg : reg = .cur_privilege
      rotate_left
      · cases reg <;> first | exact absurd rfl hreg | simp [nOwn] at hown
      subst hreg
      rw [uxnw_priv_quiet fullFoot (fun _ => true) _ s v k' rfl rfl] at h
      exact ih () _ _ p k s' o' h
    | memRead n vasize req =>
      rw [uxnw_read] at h
      split at h
      · split at h
        · split at h
          · exact ih _ _ _ p k s' o' h
          · split at h
            · exact ih _ _ _ p k s' o' h
            · exact ih _ _ _ p k s' o' h
        · cases h
      · cases h
    | memWrite n vasize req =>
      rw [uxnw_write] at h
      split at h
      · split at h
        · split at h
          · exact ih _ _ _ p k s' o' h
          · cases h
        · cases h
      · cases h
    | _ => simp [nOwn] at hown

/-- **The bridge**: a walk landing under `(D, B)` (with no oracle-answered register) lands
identically under the unrestricted walker. -/
theorem uxnFull_of_done {D : UFoot} (hD : ∀ r, D.Dr r = false → D.Dany r = false)
    {B : Privilege → Bool} {X : Type} (m : SailM X) (orc : UOrc) (s : NSt) (x : X) (s' : NSt)
    (o' : UOrc) (h : uxnRun D B orc s m = some (.done x s' o')) :
    uxnFull orc s m = some (.done x s' o') :=
  uxnRun_mono (uFootLe_full D hD) (fun _ _ => rfl) m orc s _ h

/-- **The bridge at an exit**: a walk stopping at an exit node under `(D, B)` is, under the
unrestricted walker, the walk from that node on. -/
theorem uxnFull_of_exit {D : UFoot} (hD : ∀ r, D.Dr r = false → D.Dany r = false)
    {B : Privilege → Bool} {X : Type} (m : SailM X) (orc : UOrc) (s : NSt) (p : Privilege)
    (k : PUnit → SailM X) (s' : NSt) (o' : UOrc) (h : uxnRun D B orc s m = some (.exit p k s' o')) :
    uxnFull orc s m = uxnFull o' s' (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) :=
  uxnRun_mono (uFootLe_full D hD) (fun _ _ => rfl) m orc s _ h

end MachCSL
