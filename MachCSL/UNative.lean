/-
MachCSL: **the native walker** (`uxnRun`) for an untrusted hart that may change privilege inside
an untrusted set `B` (Miralis's payload: `B = {S, U}`), and its walk rule (`swp_uxnRun`,
`wpLoop_uxnStep`: rule R-native).

`uxdRun D T dirty` (MachCSL/URunD) walks a hart's computation over a footprint `D` that never
writes `cur_privilege` (`UFoot.noPriv`) and with a *fixed* text map. A native S/U payload changes
privilege on its own (delegated traps U→S, `sret` S→U), translates through page tables it owns,
and stores into the same memory it fetches from. `uxnRun` therefore:

* carries the hart's memory in its state (`NSt`: a byte map `T` owned as `uxdOwn`, and its dirty
  bytes): every data read (plain or exclusive), every page-table read and every instruction fetch
  is answered from `T` (a fetch of a window with a dirty byte draws its value from the oracle, as in
  `uxdRun`), and every store writes `T` and marks its window dirty (`uxdOwn_store`);
* takes a write of `cur_privilege` between two privileges of `B` as a **quiet** step (its rule is a
  client-supplied `QuietPriv`, which the language's observation boundary must make silent: today,
  with the `privUser` boundary, `B` must not mix `User` with other privileges; with the boundary
  generalized to an untrusted set (design note 09, M5), `B` is that set);
* **ends** the walk at a write of `cur_privilege` leaving `B` (a trap into M-mode), returning the
  node (`NRes.exit`), where the client continues with the boundary rules (`swp_writeReg_uexit`)
  and the M-mode rules;
* hands every other node to one `runRW` node.
-/
import MachCSL.URunDSwp
import MachCSL.UCycleSwp
import MachCSL.UxdExcl
import MachCSL.WpPtWalkOwn

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## §1 The walker -/

/-- The native walker's state: the walker state (registers, reservation), the owned memory `T`
and its dirty bytes. -/
structure NSt where
  u     : UWSt
  T     : BMap
  dirty : PAddr → Bool

/-- Where a native walk stops: at the end of the computation, or at a privilege write leaving the
untrusted set (with the privilege written and the continuation after it). -/
inductive NRes (X : Type) where
  | done (x : X) (s : NSt) (orc : UOrc)
  | exit (p : Privilege) (k : PUnit → SailM X) (s : NSt) (orc : UOrc)

/-- The privilege a node writes, if it is a write of `cur_privilege`. -/
def privW : Eff RegisterType exception → Option Privilege
  | .ok (.regWrite .cur_privilege p) => some p
  | _ => none

/-- The nodes the native walker answers itself: privilege writes, memory reads and writes. -/
def nOwn : Eff RegisterType exception → Bool
  | .ok (.regWrite .cur_privilege _) => true
  | .ok (.memRead _ _ _) => true
  | .ok (.memWrite _ _ _) => true
  | _ => false

/-- The store's dirty bytes: the old ones and the window `[pa, pa + n)`. -/
abbrev dirtyAdd (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) : PAddr → Bool :=
  fun a => dirty a || decide (a ∈ ubWin pa n)

/-- **The native walker** over the footprint `D` (for the registers but `cur_privilege`) and the
untrusted set `B`. -/
def uxnRun {X : Type} (D : UFoot) (B : Privilege → Bool) : UOrc → NSt → SailM X → Option (NRes X)
  | orc, s, .pure x => some (.done x s orc)
  | orc, s, .impure (.ok (.regWrite .cur_privilege p)) k =>
    if B (s.u.file .cur_privilege) then
      if B p then
        uxnRun D B orc { s with u := { s.u with pin := s.u.pin.set .cur_privilege p } } (k ())
      else some (.exit p k s orc)
    else none
  | orc, s, .impure (.ok (.memRead n _ req)) k =>
    if n < 2 ^ 64 then
      match bmRead s.T req.pa n with
      | some w =>
        if akIfetch req.access_kind && winDirty s.dirty req.pa n then
          uxnRun D B orc.tail s
            (k (.Ok (bmMerge s.dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
        else if akExcl req.access_kind then
          uxnRun D B orc { s with u := { s.u with rv := true } } (k (.Ok (w, none)))
        else uxnRun D B orc s (k (.Ok (w, none)))
      | none => none
    else none
  | orc, s, .impure (.ok (.memWrite n _ req)) k =>
    if n < 2 ^ 64 then
      match req.value with
      | some w' =>
        if bmOwned s.T req.pa n then
          uxnRun D B orc
            ⟨{ s.u with rv := false }, bmWrite s.T req.pa n w', dirtyAdd s.dirty req.pa n⟩
            (k (.Ok (some true)))
        else none
      | none => none
    else none
  | orc, s, .impure c k =>
    (runRW D orc s.u (FreeM.impure c FreeM.pure)).bind fun r =>
      uxnRun D B r.2.2 { s with u := r.2.1 } (k r.1)

section walker
variable (D : UFoot) (B : Privilege → Bool)

theorem uxnw_priv_quiet {X : Type} (orc : UOrc) (s : NSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.u.file .cur_privilege) = true) (h1 : B p = true) :
    uxnRun D B orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
      uxnRun D B orc { s with u := { s.u with pin := s.u.pin.set .cur_privilege p } } (k ()) := by
  simp only [uxnRun, h0, h1, if_true]

theorem uxnw_priv_exit {X : Type} (orc : UOrc) (s : NSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.u.file .cur_privilege) = true) (h1 : B p = false) :
    uxnRun D B orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
      some (.exit p k s orc) := by
  simp only [uxnRun, h0, h1, if_true, Bool.false_eq_true, if_false]

theorem uxnw_priv_out {X : Type} (orc : UOrc) (s : NSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.u.file .cur_privilege) = false) :
    uxnRun D B orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) = none := by
  simp only [uxnRun, h0, Bool.false_eq_true, if_false]

theorem uxnw_read {X : Type} (orc : UOrc) (s : NSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X) :
    uxnRun D B orc s (FreeM.impure (.ok (.memRead n vasize req)) k) =
      if n < 2 ^ 64 then
        match bmRead s.T req.pa n with
        | some w =>
          if akIfetch req.access_kind && winDirty s.dirty req.pa n then
            uxnRun D B orc.tail s
              (k (.Ok (bmMerge s.dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
          else if akExcl req.access_kind then
            uxnRun D B orc { s with u := { s.u with rv := true } } (k (.Ok (w, none)))
          else uxnRun D B orc s (k (.Ok (w, none)))
        | none => none
      else none := by
  simp only [uxnRun]

theorem uxnw_write {X : Type} (orc : UOrc) (s : NSt) {n vasize : Nat}
    (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) :
    uxnRun D B orc s (FreeM.impure (.ok (.memWrite n vasize req)) k) =
      if n < 2 ^ 64 then
        match req.value with
        | some w' =>
          if bmOwned s.T req.pa n then
            uxnRun D B orc
              ⟨{ s.u with rv := false }, bmWrite s.T req.pa n w', dirtyAdd s.dirty req.pa n⟩
              (k (.Ok (some true)))
          else none
        | none => none
      else none := by
  simp only [uxnRun]

/-- Any other node: one `runRW` node, then the continuation. -/
theorem uxnw_node {X : Type} (orc : UOrc) (s : NSt) (c : Eff RegisterType exception)
    (k : ArchSem.Effect.ret c → SailM X) (hc : nOwn c = false) :
    uxnRun D B orc s (FreeM.impure c k) =
      (runRW D orc s.u (FreeM.impure c FreeM.pure)).bind fun r =>
        uxnRun D B r.2.2 { s with u := r.2.1 } (k r.1) := by
  rcases c with e | op
  · simp only [uxnRun]
  · cases op with
    | memRead n vasize req => simp [nOwn] at hc
    | memWrite n vasize req => simp [nOwn] at hc
    | regWrite r v =>
      by_cases hr : r = .cur_privilege
      · subst hr; simp [nOwn] at hc
      · cases r <;> first | exact absurd rfl hr | simp only [uxnRun]
    | _ => simp only [uxnRun]

end walker

theorem privW_some {c : Eff RegisterType exception} {p : Privilege} (h : privW c = some p) :
    c = .ok (.regWrite .cur_privilege p) := by
  rcases c with e | op
  · simp [privW] at h
  · cases op with
    | regWrite r v =>
      by_cases hr : r = .cur_privilege
      · subst hr; simp only [privW, Option.some.injEq] at h; subst h; rfl
      · cases r <;> first | exact absurd rfl hr | simp [privW] at h
    | _ => simp [privW] at h

/-! ## §2 The walk rule -/

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} {D : UFoot} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)
variable (B : Privilege → Bool)

/-- The register frame owns the privilege cell in full and takes any update of it. -/
def URegFramePriv (RF : URegFrame GF cpu D) : Prop :=
  ∀ f : RegFile, RF.F f ⊢ Register.cur_privilege ↦ᵣ[cpu] f .cur_privilege ∗
    ∀ p : Privilege, Register.cur_privilege ↦ᵣ[cpu] p -∗ RF.F (f.set .cur_privilege p)

/-- **The quiet-privilege rule** the walk needs for the untrusted set `B`: a write of
`cur_privilege` between two privileges of `B` is a silent step. Today
(`swp_writeReg_priv_quiet`) it holds when `privUser` agrees on `B`; with the observation boundary
generalized to an untrusted set (design note 09, M5), for that set. -/
def QuietPriv (cpu : CPU) (B : Privilege → Bool) : Prop :=
  ∀ (p p' : Privilege) (Ψ : PUnit → IProp GF), B p = true → B p' = true →
    Register.cur_privilege ↦ᵣ[cpu] p ∗ ▷ (Register.cur_privilege ↦ᵣ[cpu] p' -∗ Ψ ()) ⊢
      swp cpu (writeReg Register.cur_privilege p') Ψ

/-- The rule holds today for any `B` on which `privUser` is constant. -/
theorem quietPriv_of_privUser (cpu : CPU) (B : Privilege → Bool)
    (hB : ∀ p p', B p = true → B p' = true → privUser p = privUser p') :
    QuietPriv (GF := GF) cpu B := by
  intro p p' Ψ hp hp'
  iintro ⟨Hr, HΨ⟩
  iapply swp_writeReg_priv_quiet cpu p p' Ψ
  iframe Hr HΨ
  ipureintro
  exact hB p p' hp hp'

/-- The resources a native walk from `s` runs on, beside the instruction view: the walker frames
and the owned memory. -/
def nFr (K : Nat) (DT : List PAddr) (s : NSt) : IProp GF :=
  iprop(uFr RF BF s.u ∗ uxdOwn ξ K DT s.dirty s.T)

/-- The obligation after a native walk from `s`: at a landing, the resources give `Φd`; at an
exit, they give `Ψe` of the privilege written and the continuation. -/
def uxnPost {X : Type} (K : Nat) (DT : List PAddr) (s : NSt) (m : SailM X)
    (Φd : X → IProp GF) (Ψe : Privilege → (PUnit → SailM X) → IProp GF) : IProp GF :=
  iprop(∀ (orc : UOrc) (res : NRes X), ⌜uxnRun D B orc s m = some res⌝ -∗
    match res with
    | .done x s' _ => nFr RF BF K DT s' -∗ Φd x
    | .exit p k s' _ => nFr RF BF K DT s' -∗ Ψe p k)

theorem uxnPost_step {X : Type} (K : Nat) (DT : List PAddr) (s s'' : NSt) (m m' : SailM X)
    (Φd : X → IProp GF) (Ψe : Privilege → (PUnit → SailM X) → IProp GF)
    (hstep : ∀ orc', ∃ orc, uxnRun D B orc s m = uxnRun D B orc' s'' m') :
    uxnPost RF BF B K DT s m Φd Ψe ⊢ uxnPost RF BF B K DT s'' m' Φd Ψe := by
  unfold uxnPost
  iintro HP %orc' %res %h
  obtain ⟨orc, e⟩ := hstep orc'
  iapply HP $$ %orc %res %(e.trans h)

theorem uxn_hok_step {X : Type} (s s'' : NSt) (m m' : SailM X)
    (hok : ∀ orc, (uxnRun D B orc s m).isSome = true)
    (hstep : ∀ orc', ∃ orc, uxnRun D B orc s m = uxnRun D B orc' s'' m') :
    ∀ orc', (uxnRun D B orc' s'' m').isSome = true := fun orc' => by
  obtain ⟨orc, e⟩ := hstep orc'
  rw [← e]; exact hok orc

end iris

end MachCSL
