/-
MachCSL: **the native walker** (`uxnRun`) for an untrusted hart that may change privilege inside
an untrusted set `B` (Miralis's payload: `B = {S, U}`), and its walk rule (`swp_uxnRun`).

`uxdRun D T dirty` (MachCSL/URunD) walks a hart's computation over a footprint `D` that never
writes `cur_privilege` (`UFoot.noPriv`): a privilege write is an observed event of the user
boundary, which needs the client's consent. An untrusted S/U payload changes privilege on its own
(delegated traps U→S, `sret` S→U). `uxnRun` adds two arms to `uxdRun`:

* a write of `cur_privilege` from a privilege in `B` to a privilege in `B` is **quiet**: the walk
  takes it (its walk rule is a client-supplied `QuietPriv` rule, which the observation boundary of
  the language must make silent: with today's `privUser` boundary, `B` must not mix `User` with
  other privileges; with the boundary generalized to an untrusted set (design note 09, M5), `B`
  is that set);
* a write of `cur_privilege` leaving `B` (a trap into M-mode, into Miralis) **ends** the walk at
  that node (`NRes.exit`): the client continues with the boundary rules (`swp_writeReg_uexit`)
  and the M-mode rules.

Every other node is `uxdRun`'s (instruction fetches answered by the stamped text map with dirty
bytes, everything else by one `runRW` node).
-/
import MachCSL.URunDSwp
import MachCSL.UCycleSwp

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## §1 The walker -/

/-- Where a native walk stops: at the end of the computation, or at a privilege write leaving the
untrusted set (with the privilege written and the continuation after it). -/
inductive NRes (X : Type) where
  | done (x : X) (s : UWSt) (orc : UOrc)
  | exit (p : Privilege) (k : PUnit → SailM X) (s : UWSt) (orc : UOrc)

/-- The privilege a node writes, if it is a write of `cur_privilege`. -/
def privW : Eff RegisterType exception → Option Privilege
  | .ok (.regWrite .cur_privilege p) => some p
  | _ => none

/-- **The native walker** over the footprint `D` (for every register but `cur_privilege`), the
untrusted set `B`, the stamped text map `T` and the dirty bytes `dirty`. -/
def uxnRun {X : Type} (D : UFoot) (B : Privilege → Bool) (T : BMap) (dirty : PAddr → Bool) :
    UOrc → UWSt → SailM X → Option (NRes X)
  | orc, s, .pure x => some (.done x s orc)
  | orc, s, .impure (.ok (.regWrite .cur_privilege p)) k =>
    if B (s.file .cur_privilege) then
      if B p then uxnRun D B T dirty orc { s with pin := s.pin.set .cur_privilege p } (k ())
      else some (.exit p k s orc)
    else none
  | orc, s, .impure (.ok (.memRead n vasize req)) k =>
    if uxTextRead T req then
      match bmRead T req.pa n with
      | some w =>
        if akIfetch req.access_kind && winDirty dirty req.pa n then
          uxnRun D B T dirty orc.tail s
            (k (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
        else uxnRun D B T dirty orc s (k (.Ok (w, none)))
      | none => none
    else
      (runRW D orc s (FreeM.impure (.ok (.memRead n vasize req)) FreeM.pure)).bind
        fun r => uxnRun D B T dirty r.2.2 r.2.1 (k r.1)
  | orc, s, .impure c k =>
    (runRW D orc s (FreeM.impure c FreeM.pure)).bind fun r => uxnRun D B T dirty r.2.2 r.2.1 (k r.1)

section walker
variable (D : UFoot) (B : Privilege → Bool) (T : BMap) (dirty : PAddr → Bool)

/-- A quiet privilege write: inside `B`, the walk takes it. -/
theorem uxnw_priv_quiet {X : Type} (orc : UOrc) (s : UWSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.file .cur_privilege) = true) (h1 : B p = true) :
    uxnRun D B T dirty orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
      uxnRun D B T dirty orc { s with pin := s.pin.set .cur_privilege p } (k ()) := by
  simp only [uxnRun, h0, h1, if_true]

/-- A privilege write leaving `B`: the walk stops there. -/
theorem uxnw_priv_exit {X : Type} (orc : UOrc) (s : UWSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.file .cur_privilege) = true) (h1 : B p = false) :
    uxnRun D B T dirty orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
      some (.exit p k s orc) := by
  simp only [uxnRun, h0, h1, if_true, Bool.false_eq_true, if_false]

/-- A privilege write from outside `B`: the walk refuses it. -/
theorem uxnw_priv_out {X : Type} (orc : UOrc) (s : UWSt) (p : Privilege) (k : PUnit → SailM X)
    (h0 : B (s.file .cur_privilege) = false) :
    uxnRun D B T dirty orc s (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) = none := by
  simp only [uxnRun, h0, Bool.false_eq_true, if_false]

/-- A read the text map answers (as in `uxdRun`). -/
theorem uxnw_text {X : Type} (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (hk : uxTextRead T req = true) :
    uxnRun D B T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) k) =
      match bmRead T req.pa n with
      | some w =>
        if akIfetch req.access_kind && winDirty dirty req.pa n then
          uxnRun D B T dirty orc.tail s
            (k (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
        else uxnRun D B T dirty orc s (k (.Ok (w, none)))
      | none => none := by
  simp only [uxnRun, hk, if_true]

/-- Any other node: one `runRW` node, then the continuation. -/
theorem uxnw_node {X : Type} (orc : UOrc) (s : UWSt) (c : Eff RegisterType exception)
    (k : ArchSem.Effect.ret c → SailM X) (hc : uxwIsText T c = false) (hp : privW c = none) :
    uxnRun D B T dirty orc s (FreeM.impure c k) =
      (runRW D orc s (FreeM.impure c FreeM.pure)).bind fun r =>
        uxnRun D B T dirty r.2.2 r.2.1 (k r.1) := by
  rcases c with e | op
  · simp only [uxnRun]
  · cases op with
    | memRead n vasize req =>
      simp only [uxwIsText] at hc
      simp only [uxnRun, hc, Bool.false_eq_true, if_false]
    | regWrite r v =>
      by_cases hr : r = .cur_privilege
      · subst hr; simp [privW] at hp
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

/-- The obligation after a native walk from `s`: at a landing, the frames give `Φd`; at an exit,
they give `Ψe` of the privilege written and the continuation. -/
def uxnPost {X : Type} (T : BMap) (dirty : PAddr → Bool) (s : UWSt) (m : SailM X)
    (Φd : X → IProp GF) (Ψe : Privilege → (PUnit → SailM X) → IProp GF) : IProp GF :=
  iprop(∀ (orc : UOrc) (res : NRes X), ⌜uxnRun D B T dirty orc s m = some res⌝ -∗
    match res with
    | .done x s' _ => uFr RF BF s' -∗ Φd x
    | .exit p k s' _ => uFr RF BF s' -∗ Ψe p k)

theorem uxnPost_step {X : Type} (T : BMap) (dirty : PAddr → Bool) (s s'' : UWSt) (m m' : SailM X)
    (Φd : X → IProp GF) (Ψe : Privilege → (PUnit → SailM X) → IProp GF)
    (hstep : ∀ orc', ∃ orc, uxnRun D B T dirty orc s m = uxnRun D B T dirty orc' s'' m') :
    uxnPost RF BF B T dirty s m Φd Ψe ⊢ uxnPost RF BF B T dirty s'' m' Φd Ψe := by
  unfold uxnPost
  iintro HP %orc' %res %h
  obtain ⟨orc, e⟩ := hstep orc'
  iapply HP $$ %orc %res %(e.trans h)

/-- **The native walk rule.** From the frames of `s`, the text map and the instruction view, a
computation every oracle's native walk runs through (to its end or to an exit node) satisfies
`swp` with postcondition `Φ`, given the obligation at every landing (`Φ` after giving back the
text map) and at every exit (the `swp` of the exit node and its continuation). -/
theorem swp_uxnRun (hRP : URegFramePriv RF) (hq : QuietPriv (GF := GF) cpu B)
    {X : Type} (K : Nat) (DT : List PAddr) (T : BMap) (dirty : PAddr → Bool) (m : SailM X) :
    ∀ (s : UWSt), (∀ orc, (uxnRun D B T dirty orc s m).isSome = true) → ∀ Φ : X → IProp GF,
      uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
        uxnPost RF BF B T dirty s m (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x))
          (fun p k => iprop(uxdOwn ξ K DT dirty T -∗
            swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) Φ)) ⊢ swp cpu m Φ := by
  induction m with
  | pure x =>
    intro s _ Φ
    iintro ⟨Hfr, Htx, _, HP⟩
    iapply swp_ret
    unfold uxnPost
    ihave HΦ := HP $$ %(UOrc.dflt s.rs) %(NRes.done x s (UOrc.dflt s.rs)) %rfl
    iapply HΦ $$ Hfr Htx
  | impure c k ih =>
    intro s hok Φ
    cases hpw : privW c with
    | some p =>
      obtain rfl := privW_some hpw
      cases h0 : B (s.file .cur_privilege) with
      | false =>
        have h := hok (UOrc.dflt s.rs)
        rw [uxnw_priv_out D B T dirty _ s p k h0] at h
        cases h
      | true =>
      cases h1 : B p with
      | false =>
        -- an exit: hand the node to the client
        iintro ⟨Hfr, Htx, _, HP⟩
        unfold uxnPost
        ihave HΨ := HP $$ %(UOrc.dflt s.rs) %(NRes.exit p k s (UOrc.dflt s.rs))
          %(uxnw_priv_exit D B T dirty _ s p k h0 h1)
        iapply HΨ $$ Hfr Htx
      | true =>
        -- a quiet privilege write
        have hst : ∀ o : UOrc, ∃ o₀, uxnRun D B T dirty o₀ s
            (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
            uxnRun D B T dirty o { s with pin := s.pin.set .cur_privilege p } (k ()) :=
          fun o => ⟨o, uxnw_priv_quiet D B T dirty o s p k h0 h1⟩
        have hok' : ∀ o, (uxnRun D B T dirty o { s with pin := s.pin.set .cur_privilege p }
            (k ())).isSome = true := fun o => by
          obtain ⟨o₀, h⟩ := hst o
          rw [← h]; exact hok o₀
        have e : (FreeM.impure (.ok (.regWrite .cur_privilege p)) k : SailM X) =
            (writeReg Register.cur_privilege p >>= k) := rfl
        iintro ⟨Hfr, Htx, #Hiv, HP⟩
        ihave HP := uxnPost_step RF BF B T dirty s _ _ _ _ _ hst $$ HP
        rw [e]
        unfold uFr
        icases Hfr with ⟨HF, HB, Hc, Hr⟩
        icases hRP s.file $$ HF with ⟨Hpc, Hupd⟩
        iapply swp_bind
        iapply hq (s.file .cur_privilege) p (fun u => swp cpu (k u) Φ) h0 h1
        iframe Hpc
        inext
        iintro Hpc
        ihave HF := Hupd $$ %p Hpc
        iapply ih () { s with pin := s.pin.set .cur_privilege p } hok' Φ
        iframe Htx Hiv HP
        unfold uFr
        rw [UWSt.file_setPin]
        iframe
    | none =>
    cases hc : uxwIsText T c with
    | true =>
      obtain ⟨n, vasize, req, rfl, htx⟩ := uxwIsText_true T hc
      have htx' := htx
      simp only [uxTextRead, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at htx'
      obtain ⟨⟨⟨_, hn⟩, hex⟩, _⟩ := htx'
      obtain ⟨w, hw⟩ : ∃ w, bmRead T req.pa n = some w := by
        cases hr : bmRead T req.pa n with
        | some w => exact ⟨w, rfl⟩
        | none =>
          have h := hok (UOrc.dflt s.rs)
          rw [uxnw_text D B T dirty _ s req k htx, hr] at h
          cases h
      have hcont : ∀ w' : BitVec (8 * n),
          (∀ j, j < n → dirty (bAddr req.pa j) = false → nthByte w' j = nthByte w j) →
          (akIfetch req.access_kind = false → w' = w) →
          ∀ o : UOrc, ∃ o₀, uxnRun D B T dirty o₀ s (FreeM.impure (.ok (.memRead n vasize req)) k) =
            uxnRun D B T dirty o s (k (.Ok (w', none))) := by
        intro w' hag hpl o
        cases hd : (akIfetch req.access_kind && winDirty dirty req.pa n) with
        | false =>
          have hww : w' = w := by
            cases hif : akIfetch req.access_kind with
            | false => exact hpl hif
            | true =>
              rw [hif, Bool.true_and] at hd
              exact bv_eq_of_bytes _ _ (fun j hj => hag j hj (winDirty_false hd j hj))
          subst hww
          refine ⟨o, ?_⟩
          rw [uxnw_text D B T dirty o s req k htx, hw]
          simp only [hd, Bool.false_eq_true, if_false]
        | true =>
          refine ⟨uxdOrc o (8 * n) w', ?_⟩
          rw [uxnw_text D B T dirty _ s req k htx, hw]
          simp only [hd, if_true]
          rw [uxdOrc_tail, uxdOrc_ch, bmMerge_eq dirty req.pa n w w' hag]
      show uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
          uxnPost RF BF B T dirty s (FreeM.impure (.ok (.memRead n vasize req)) k)
            (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x))
            (fun p k => iprop(uxdOwn ξ K DT dirty T -∗
              swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) Φ)) ⊢
        swp cpu (ConcurrencyInterfaceV1.sail_mem_read req >>= k) Φ
      iintro ⟨Hfr, Htx, #Hiv, HP⟩
      icases uxdOwn_acc ξ K DT dirty T req.pa n w hn hw $$ Htx with ⟨Hb, Hcl⟩
      iapply swp_bind
      cases hif : akIfetch req.access_kind with
      | true =>
        iapply swp_sail_mem_read_ifetch_d cpu req ξ K dirty w hif (fun v => swp cpu (k v) Φ)
        iframe Hb Hiv
        inext
        iintro %w' %hag Hb
        have hst := hcont w' hag (fun h => absurd h (by rw [hif]; decide))
        have hok' : ∀ o, (uxnRun D B T dirty o s (k (.Ok (w', none)))).isSome = true := fun o => by
          obtain ⟨o₀, h0⟩ := hst o
          rw [← h0]; exact hok o₀
        ihave HP := uxnPost_step RF BF B T dirty s s _ _ _ _ hst $$ HP
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w', none)) s hok' Φ
        iframe Hfr Htx Hiv HP
      | false =>
        have hpl : akPlain req.access_kind = true := by simp [akPlain, hif, hex]
        have hst := hcont w (fun _ _ _ => rfl) (fun _ => rfl)
        have hok' : ∀ o, (uxnRun D B T dirty o s (k (.Ok (w, none)))).isSome = true := fun o => by
          obtain ⟨o₀, h0⟩ := hst o
          rw [← h0]; exact hok o₀
        ihave HP := uxnPost_step RF BF B T dirty s s _ _ _ _ hst $$ HP
        unfold uFr
        icases Hfr with ⟨HF, HB, Hc, Hr⟩
        iapply swp_sail_mem_read_plain_d cpu req ξ K dirty w hpl (fun v => swp cpu (k v) Φ)
        iframe Hc Hb
        inext
        iintro Hc Hb
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w, none)) s hok' Φ
        iframe Htx Hiv HP
        unfold uFr
        iframe
    | false =>
      have hok1 : ∀ orc, (runRW D orc s (FreeM.impure c FreeM.pure)).isSome = true := fun orc => by
        have h := hok orc
        rw [uxnw_node D B T dirty orc s c k hc hpw] at h
        revert h
        cases runRW D orc s (FreeM.impure c FreeM.pure) with
        | none => intro h; simp at h
        | some _ => intro _; rfl
      show uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
          uxnPost RF BF B T dirty s (FreeM.impure c k) (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x))
            (fun p k => iprop(uxdOwn ξ K DT dirty T -∗
              swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) Φ)) ⊢
        swp cpu ((FreeM.impure c FreeM.pure : SailM (ArchSem.Effect.ret c)) >>= k) Φ
      iintro ⟨Hfr, Htx, #Hiv, HP⟩
      iapply swp_bind
      iapply swp_runRW RF BF (FreeM.impure c FreeM.pure) s hok1 (fun v => swp cpu (k v) Φ)
      iframe Hfr
      unfold uPost
      iintro %orc %v %s' %orc' %h HF HB Hc Hr
      have hre : ∀ o, ∃ orc₀, uxnRun D B T dirty orc₀ s (FreeM.impure c k) =
          uxnRun D B T dirty o s' (k v) :=
        fun o => by
          obtain ⟨orc₀, h0⟩ := uft_runRW_node_shift D c s orc v s' orc' h o
          refine ⟨orc₀, ?_⟩
          rw [uxnw_node D B T dirty orc₀ s c k hc hpw, h0]; rfl
      have hok' : ∀ o, (uxnRun D B T dirty o s' (k v)).isSome = true := fun o => by
        obtain ⟨orc₀, h0⟩ := hre o
        rw [← h0]; exact hok orc₀
      iapply ih v s' hok' Φ
      isplitl [HF HB Hc Hr]
      · unfold uFr; iframe
      iframe Htx Hiv
      iapply uxnPost_step RF BF B T dirty s s' _ _ _ _ hre $$ HP

/-- **One machine step of a native hart** (rule R-native): the whole cycle `try_step 0 false` is one
native walk, then the optional clock tick. At a landing, the client continues the loop; at an
exit (a trap into M-mode), the client runs the exit node and the rest of the cycle with the
boundary and M-mode rules. -/
theorem wpLoop_uxnStep [BndTriv (hlc := hlc) (GF := GF)] (hRP : URegFramePriv RF)
    (hq : QuietPriv (GF := GF) cpu B) (K : Nat) (DT : List PAddr) (T : BMap) (dirty : PAddr → Bool)
    (s : UWSt) (hok : ∀ orc, (uxnRun D B T dirty orc s (try_step 0 false)).isSome = true) :
    uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
      ▷ (∀ tick : Bool,
        uxnPost RF BF B T dirty s (try_step 0 false)
          (fun _ => iprop(uxdOwn ξ K DT dirty T -∗
            swp cpu (if tick then tick_clock () else pure ()) (fun _ => wpLoop cpu)))
          (fun p k => iprop(uxdOwn ξ K DT dirty T -∗
            swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k)
              (fun _ => swp cpu (if tick then tick_clock () else pure ()) (fun _ => wpLoop cpu)))))
    ⊢ wpLoop cpu := by
  iintro ⟨Hfr, Htx, #Hiv, HK⟩
  iapply wpLoop_ucStep
  iintro %tick
  inext
  ispecialize HK $$ %tick
  iapply swp_uxnRun RF BF B hRP hq K DT T dirty (try_step 0 false) s hok
  iframe Hfr Htx Hiv HK

end iris

end MachCSL
