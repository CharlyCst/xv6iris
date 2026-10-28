/-
MachCSL: **a fetched word's tail with an Iris execute step, and `fence.i` at
User** (the user-mode twin of `UIcacheFencei.execSpecF_fencei_x`).

`UCycleSwp.swp_ucAfterFetch_base` runs a fetched word's tail as one `runRW`
walk, so its `execute` is a walk too.  The `fence.i` step cannot be one: the
walker steps over barriers silently (`urw_barrier`), and the step that raises
the instruction view and stamps the bytes is a ghost step at the barrier
(`swp_sail_barrier_fencei`).  So:

* `swp_ucAfterFetch_base_spec` -- the tail (decode, no landing pad,
  `nextPC := PC + 4`) with `uxaExecAs i` given as an Iris fact;
* `swp_uxaExecAs_fencei` -- `uxaExecAs (FENCEI …)` runs the client's
  `ifenceStep` at the barrier and retires, handing out `iviewLb cpu K`.
-/
import MachCSL.UCycleSwp
import MachCSL.UIcacheFence

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Register Step ExecutionResult FetchResult

section swp
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} {D : UFoot} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)

/-- **A fetched word's tail, with an Iris execute step**: decoded to `i` (a
walk that does not move the state), no landing pad, `nextPC := PC + 4`, then
`uxaExecAs i` as the given Iris fact. -/
theorem swp_ucAfterFetch_base_spec (hD : UcFoot D) (s : UWSt) (w : BitVec 32) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : ∀ orc, runRW D orc s (ext_decode w) = some (i, s, orc))
    (R : IProp GF) (Ψ : Step → IProp GF)
    (Hex : uFr RF BF (ucNpcS s 4) ∗ R ⊢
      swp cpu (uxaExecAs i) (fun r => Ψ (Step_Execute (r, zero_extend (m := 32) w)))) :
    uFr RF BF s ∗ R ⊢ swp cpu (ucAfterFetch (F_Base w)) Ψ := by
  have hlp : ∀ orc, runRW D orc s (is_landing_pad_expected ()) = some (false, s, orc) := fun orc => by
    have h := uc_lpad orc s hrd hv (fun b => (pure b : SailM Bool))
    simp only [bind_pure] at h
    exact h
  simp only [ucAfterFetch, ext_fetch_hook]
  iintro ⟨Hfr, HR⟩
  iapply swp_bind
  iapply swp_ucWalk RF BF (ext_decode w) s (fun orc => (i, s, orc)) hdec
  iframe Hfr
  iintro %orc Hfr
  dsimp only
  iapply swp_bind
  iapply swp_ucWalk RF BF (is_landing_pad_expected ()) s (fun orc => (false, s, orc)) hlp
  iframe Hfr
  iintro %orc' Hfr
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  iapply swp_bind
  iapply swp_ucWalk RF BF (readReg .PC) s (fun orc => (s.file .PC, s, orc))
    (fun orc => utr_readReg D orc s .PC hD.rd_pc)
  iframe Hfr
  iintro %o2 Hfr
  dsimp only
  iapply swp_bind
  iapply swp_ucWalk RF BF (writeReg .nextPC (BitVec.addInt (s.file .PC) 4)) s
    (fun orc => ((), ucNpcS s 4, orc))
    (fun orc => ucRW_writeReg_pure D orc s .nextPC _ hD.wr_npc)
  iframe Hfr
  iintro %o3 Hfr
  dsimp only
  iapply swp_bind
  iapply swp_mono cpu (uxaExecAs i) (fun r => Ψ (Step_Execute (r, zero_extend (m := 32) w)))
  isplitl []
  · iintro %r HΨ
    iapply swp_ret
    iexact HΨ
  iapply Hex
  iframe Hfr HR

/-- **A fetched halfword's tail, with an Iris execute step** (the `Ext_Zca`
gate open): as the base one, `nextPC := PC + 2`. -/
theorem swp_ucAfterFetch_rvc_spec (hD : UcFoot D) (s : UWSt) (h : BitVec 16) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : ∀ orc, runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (R : IProp GF) (Ψ : Step → IProp GF)
    (Hex : uFr RF BF (ucNpcS s 2) ∗ R ⊢
      swp cpu (uxaExecAs i) (fun r => Ψ (Step_Execute (r, zero_extend (m := 32) h)))) :
    uFr RF BF s ∗ R ⊢ swp cpu (ucAfterFetch (F_RVC h)) Ψ := by
  have hlp : ∀ orc, runRW D orc s (is_landing_pad_expected ()) = some (false, s, orc) := fun orc => by
    have h := uc_lpad orc s hrd hv (fun b => (pure b : SailM Bool))
    simp only [bind_pure] at h
    exact h
  have hz : ∀ orc, runRW D orc s (currentlyEnabled extension.Ext_Zca) = some (true, s, orc) := fun orc => by
    have h := uc_currentlyEnabled_Zca hm orc (fun b => (pure b : SailM Bool))
    simp only [bind_pure] at h
    exact h
  simp only [ucAfterFetch, ext_fetch_hook]
  iintro ⟨Hfr, HR⟩
  iapply swp_bind
  iapply swp_ucWalk RF BF (ext_decode_compressed h) s (fun orc => (i, s, orc)) hdec
  iframe Hfr
  iintro %orc Hfr
  dsimp only
  iapply swp_bind
  iapply swp_ucWalk RF BF (is_landing_pad_expected ()) s (fun orc => (false, s, orc)) hlp
  iframe Hfr
  iintro %orc' Hfr
  simp only [Bool.false_eq_true, if_false]
  iapply swp_bind
  iapply swp_ucWalk RF BF (currentlyEnabled extension.Ext_Zca) s (fun orc => (true, s, orc)) hz
  iframe Hfr
  iintro %o1 Hfr
  simp only [if_true]
  iapply swp_bind
  iapply swp_ucWalk RF BF (readReg .PC) s (fun orc => (s.file .PC, s, orc))
    (fun orc => utr_readReg D orc s .PC hD.rd_pc)
  iframe Hfr
  iintro %o2 Hfr
  dsimp only
  iapply swp_bind
  iapply swp_ucWalk RF BF (writeReg .nextPC (BitVec.addInt (s.file .PC) 2)) s
    (fun orc => ((), ucNpcS s 2, orc))
    (fun orc => ucRW_writeReg_pure D orc s .nextPC _ hD.wr_npc)
  iframe Hfr
  iintro %o3 Hfr
  dsimp only
  iapply swp_bind
  iapply swp_mono cpu (uxaExecAs i) (fun r => Ψ (Step_Execute (r, zero_extend (m := 32) h)))
  isplitl []
  · iintro %r HΨ
    iapply swp_ret
    iexact HΨ
  iapply Hex
  iframe Hfr HR

/-- **`fence.i` at User**: `uxaExecAs (FENCEI …)` runs the client's ghost step
`ifenceStep cpu P Q` at the barrier (at the raised instruction view `K`, whose
receipt it hands out) and retires. -/
theorem swp_uxaExecAs_fencei (imm : BitVec 12) (rs rd : regidx) (P : IProp GF) (Q : Nat → IProp GF)
    (Φ : ExecutionResult → IProp GF) :
    ifenceStep cpu P Q ∗ P ∗ ▷ (∀ K, iviewLb cpu K -∗ Q K -∗ Φ RETIRE_SUCCESS) ⊢
      swp cpu (uxaExecAs (.FENCEI (imm, rs, rd))) Φ := by
  have e : uxaExecAs (.FENCEI (imm, rs, rd)) =
      (ConcurrencyInterfaceV1.sail_barrier .Barrier_RISCV_i >>= fun _ => (pure RETIRE_SUCCESS : SailM _)) := by
    simp only [uxaExecAs, execute, execute_FENCEI, bind_assoc, pure_bind]
    rfl
  rw [e]
  iintro ⟨Hs, HP, HΦ⟩
  iapply swp_bind
  iapply swp_sail_barrier_fencei cpu P Q
  iframe Hs HP
  inext
  iintro %K Hiv HQ
  iapply swp_ret
  iapply HΦ $$ %K Hiv HQ

end swp

end MachCSL
