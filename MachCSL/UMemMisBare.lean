/-
MachCSL: **a plain load/store under Bare translation, aligned or not**
(additive; the Bare twin of `UMemMisVmemR`/`UMemMisVmemW`, which are stated
under Sv39).

Under Bare translation (`translationMode ep = Bare`), `vmem_read_addr`/
`vmem_write_addr` never split at a page boundary, so a misaligned plain access
is one translation and one physical access of the full width, which
`checked_mem_read`/`checked_mem_write` split into chunks (`UMemMisExact`).
The read side is stated for any `UmxRun` walker (`runRW`, or `uxdRun`, whose
plain reads answer from its map: `umb_uxd_read_ram_plain`).  The effective
privilege `ep` is a parameter (the caller supplies
`effectivePrivilege … = pure ep` and the Bare mode), so the facts serve a
User-mode hart with Bare `satp` and a Machine-mode hart alike.
-/
import MachCSL.UMemMisExact
import MachCSL.UMemMisVmemR
import MachCSL.URunD
import MachCSL.UMemMisPma

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Whatever the page window, `split_on_page_boundary` is a pure pair. -/
theorem umb_split_pure (a : BitVec 64) (w : Nat) (h0 : 0 < w) (h8 : w ≤ 8) :
    ∃ p : Int × Int, split_on_page_boundary a w = (pure p : SailM (Int × Int)) := by
  by_cases hp : ummInPage a w
  · exact ⟨_, umm_split_on_page_boundary_intra a w h0 h8 hp⟩
  · exact ⟨_, umm_split_on_page_boundary_straddle a w h8 hp⟩

/-- The page-split condition under Bare translation, closed. -/
theorem umb_ite_false {α : Type} (a b : α) : (if false = true then a else b) = b := rfl

/-- **`vmem_read_addr` of a plain load under Bare translation**, aligned or not: no misaligned
exception (`umm_plat_load`), no page split (the split needs a non-Bare mode), so one
`translate_and_read_value` of the full width. -/
theorem umb_vmem_read_addr_bare {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)}
    (hR : UmxRun run) (orc : UOrc) (s : UWSt) (va : BitVec 64) (w : Nat) (h0 : 0 < w) (h8 : w ≤ 8)
    (hms : run orc s (readReg Register.mstatus) = some (s.file .mstatus, s, orc))
    (hcp : run orc s (readReg Register.cur_privilege) = some (s.file .cur_privilege, s, orc)) (ep : Privilege)
    (hep : effectivePrivilege (.Load .Data) (s.file .mstatus) (s.file .cur_privilege) = pure ep)
    (htm : run orc s (translationMode ep) = some (.Bare, s, orc))
    (pa : physaddr) (v : BitVec (8 * w)) (s' : UWSt) (orc' : UOrc)
    (htr : run orc s (translate_and_read_value (.Virtaddr va) w (.Load .Data) false false false) =
      some (.Ok (pa, v), s', orc')) :
    run orc s (vmem_read_addr (.Virtaddr va) w (.Load .Data) false false false) = some (.Ok v, s', orc') := by
  obtain ⟨p, hsplit⟩ := umb_split_pure va w h0 h8
  unfold vmem_read_addr
  simp only [umm_plat_load]
  sail_norm
  try simp only [ite_self]
  sail_norm
  simp only [hR.bind, hsplit, hR.pure, Option.bind_some]
  rw [hms, Option.bind_some]
  dsimp only
  rw [hcp, Option.bind_some]
  dsimp only
  rw [hep, hR.pure, Option.bind_some]
  dsimp only
  rw [htm, Option.bind_some]
  dsimp only
  generalize hc : (SATPMode.Bare != SATPMode.Bare && p.snd >b 0) = c
  have hc' : c = false := hc ▸ rfl
  subst hc'
  dsimp only [umb_ite_false]
  simp only [Int.toNat_natCast, htr, Option.bind_some]
  sail_norm
  simp only [hR.pure, Option.bind_some]
  congr 3
  ext t ht
  have e1 : (8 * (w : Int) - 1).toNat = 8 * w - 1 := by omega
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.getElem_or, BitVec.getElem_and,
    BitVec.getElem_not, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_allOnes, e1]
  have : t < 8 * w - 1 - 0 + 1 := by omega
  have : t < 8 * w - 1 + 1 := by omega
  simp [*]

/-- **`vmem_write_addr` of a plain store under Bare translation**, aligned or not: one translation,
the announce (`mem_write_ea`) and the write (`mem_write_value`) of the full width. -/
theorem umb_vmem_write_addr_bare (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (w : Nat) (h0 : 0 < w)
    (h8 : w ≤ 8) (data : BitVec (8 * w)) (hms : D.Dr .mstatus = true) (hcpD : D.Dr .cur_privilege = true)
    (ep : Privilege)
    (hep : effectivePrivilege (.Store .Data) (s.file .mstatus) (s.file .cur_privilege) = pure ep)
    (htm : runRW D orc s (translationMode ep) = some (.Bare, s, orc))
    (pa : physaddr) (pbmt : page_based_mem_type)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Store .Data)) = some (.Ok (pa, pbmt, ()), s, orc))
    (hea : runRW D orc s (mem_write_ea pa w (.Store .Data) pbmt false false false) = some (.Ok (), s, orc))
    (s' : UWSt)
    (hwv : runRW D orc s (mem_write_value pa w data (.Store .Data) pbmt false false false) =
      some (.Ok true, s', orc)) :
    runRW D orc s (vmem_write_addr (.Virtaddr va) w data (.Store .Data) false false false) =
      some (.Ok true, s', orc) := by
  obtain ⟨p, hsplit⟩ := umb_split_pure va w h0 h8
  unfold vmem_write_addr
  simp only [umm_plat_store]
  sail_norm
  try simp only [ite_self]
  sail_norm
  simp only [runRW_bind, hsplit, runRW_pure, Option.bind_some]
  rw [utr_readReg D _ _ _ hms, Option.bind_some, utr_readReg D _ _ _ hcpD, Option.bind_some]
  dsimp only
  rw [hep, runRW_pure, Option.bind_some]
  dsimp only
  rw [htm, Option.bind_some]
  dsimp only
  generalize hc : (SATPMode.Bare != SATPMode.Bare && p.snd >b 0) = c
  have hc' : c = false := hc ▸ rfl
  subst hc'
  dsimp only [umb_ite_false]
  have hd : BitVec.setWidth (8 * (w : Int).toNat) (BitVec.extractLsb' 0 ((8 * (w : Int) - 1).toNat + 1) data) =
      data := by
    have e1 : (8 * (w : Int) - 1).toNat = 8 * w - 1 := by omega
    ext t ht
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb', e1]
    have : t < 8 * w - 1 + 1 := by omega
    simp only [this, decide_true, Bool.true_and, Nat.zero_add]
    exact BitVec.getLsbD_eq_getElem (by omega)
  rw [hd]
  simp only [Int.toNat_natCast]
  rw [htr, Option.bind_some]
  dsimp only
  simp only [utr_assert_true, ExceptT.run_bind, run_liftM, runRW_bind, hea, hwv, runRW_pure, Option.bind_some]
  rfl

/-- `mem_read` at effective privilege `ep` is its `checked_mem_read` (any `UmxRun` walker). -/
theorem umb_mem_read {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)}
    (hR : UmxRun run) (orc : UOrc) (s : UWSt) (W : Nat) (pa : BitVec 64)
    (pbmt : page_based_mem_type) (v : BitVec (8 * W))
    (hms : run orc s (readReg Register.mstatus) = some (s.file .mstatus, s, orc))
    (hcp : run orc s (readReg Register.cur_privilege) = some (s.file .cur_privilege, s, orc)) (ep : Privilege)
    (hep : effectivePrivilege (.Load .Data) (s.file .mstatus) (s.file .cur_privilege) = pure ep)
    (hc : run orc s (checked_mem_read (.Load .Data) pbmt ep (.Physaddr pa) W false false false false) =
      some (.Ok (v, ()), s, orc)) :
    run orc s (mem_read (.Load .Data) pbmt (.Physaddr pa) W false false false) = some (.Ok v, s, orc) := by
  unfold mem_read mem_read_priv mem_read_priv_meta
  sail_norm
  rw [hR.bind, hms, Option.bind_some]
  dsimp only
  rw [hR.bind, hcp, Option.bind_some]
  dsimp only
  rw [hep, hR.bind, hR.pure, Option.bind_some]
  dsimp only
  rw [hR.bind, hc, Option.bind_some]
  rw [hR.pure]
  rfl

/-- `translate_and_read_value`: the translation, then the physical read (`uma_translate_and_read_value`
for any `UmxRun` walker). -/
theorem umb_translate_and_read_value {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)}
    (hR : UmxRun run) (orc : UOrc) (s : UWSt) (va : BitVec 64) (w : Nat) (pa : BitVec 64)
    (pbmt : page_based_mem_type) (v : BitVec (8 * w))
    (htr : run orc s (translateAddr (.Virtaddr va) (.Load .Data)) = some (.Ok (.Physaddr pa, pbmt, ()), s, orc))
    (hmr : run orc s (mem_read (.Load .Data) pbmt (.Physaddr pa) w false false false) = some (.Ok v, s, orc)) :
    run orc s (translate_and_read_value (.Virtaddr va) w (.Load .Data) false false false) =
      some (.Ok (.Physaddr pa, v), s, orc) := by
  unfold translate_and_read_value
  rw [hR.bind, htr, Option.bind_some]
  dsimp only
  rw [hR.bind, hmr, Option.bind_some]
  dsimp only
  rw [hR.pure]

/-! ## The walker over a memory with dirty bytes -/

theorem umxRun_uxdRun (D : UFoot) (T : BMap) (dirty : PAddr → Bool) : UmxRun (uxdRun D T dirty) :=
  ⟨fun _ _ _ => rfl, fun m f orc s => uxdw_bind D T dirty m f orc s⟩

/-- **A plain RAM read answered from the map** of `uxdRun` (owned bytes, any dirtiness). -/
theorem umb_uxd_read_ram_plain (D : UFoot) (T : BMap) (dirty : PAddr → Bool) (orc : UOrc) (s : UWSt)
    (pa : BitVec 64) (n : Nat) (h0 : 0 < n) (hn : n < 2 ^ 64) (v : BitVec (8 * n)) (h : bmRead T pa n = some v) :
    uxdRun D T dirty orc s (read_ram .Read_plain (.Physaddr pa) n false) = some ((v, ()), s, orc) := by
  unfold read_ram
  sail_norm
  rw [uxdw_bind_some D T dirty _ _ orc orc s s _ (uxdw_sail_mem_read_text D T dirty orc s _ ?hk v h rfl)]
  case hk =>
    simp only [uxTextRead, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h0, hn⟩, rfl⟩, bmOwned_of_read T pa n v h⟩
  rfl

/-- `mem_write_value` at effective privilege `ep` is its `checked_mem_write`. -/
theorem umb_mem_write_value (D : UFoot) (orc : UOrc) (s : UWSt) (W : Nat) (pa : BitVec 64)
    (pbmt : page_based_mem_type) (v : BitVec (8 * W)) (b : Bool) (s' : UWSt) (hms : D.Dr .mstatus = true)
    (hcpD : D.Dr .cur_privilege = true) (ep : Privilege)
    (hep : effectivePrivilege (.Store .Data) (s.file .mstatus) (s.file .cur_privilege) = pure ep)
    (hc : runRW D orc s (checked_mem_write (.Physaddr pa) W v (.Store .Data) pbmt ep () false false false) =
      some (.Ok b, s', orc)) :
    runRW D orc s (mem_write_value (.Physaddr pa) W v (.Store .Data) pbmt false false false) =
      some (.Ok b, s', orc) := by
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  sail_norm
  rw [runRW_bind, utr_readReg D _ _ _ hms, Option.bind_some]
  dsimp only
  rw [runRW_bind, utr_readReg D _ _ _ hcpD, Option.bind_some]
  dsimp only
  rw [hep, runRW_bind, runRW_pure, Option.bind_some]
  dsimp only
  exact hc

/-- **The announce** at effective privilege `ep` (`umm_mem_write_ea` at any privilege). -/
theorem umb_mem_write_ea (D : UFoot) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (pbmt : page_based_mem_type) (info : Phys_Mem_Access_Info) (h0 : 0 < W) (hW : W ≤ 8)
    (hms : D.Dr .mstatus = true) (hcpD : D.Dr .cur_privilege = true) (ep : Privilege)
    (hep : effectivePrivilege (.Store .Data) (s.file .mstatus) (s.file .cur_privilege) = pure ep)
    (hpma : runRW D orc s (check_pma_with_pmp_priority (.Store .Data) pbmt ep (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hpmp : ∀ j c, 0 < c → j + c ≤ W →
      runRW D orc s (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Store .Data) ep) = some (none, s, orc)) :
    runRW D orc s (mem_write_ea (.Physaddr pa) W (.Store .Data) pbmt false false false) =
      some (.Ok (), s, orc) := by
  obtain ⟨N, b, hN, hb, hNb, hsp⟩ := umm_split_misaligned_plan pa W info.granule_size_exp info.splittable h0 hW
  unfold mem_write_ea
  sail_norm
  simp only [runRW_bind, utr_readReg D _ _ _ hms, utr_readReg D _ _ _ hcpD, Option.bind_some, hep, runRW_pure,
    hpma]
  sail_norm
  simp only [runRW_bind, runRW_pure, Option.bind_some, hsp, write_kind_of_flags]
  sail_norm
  simp only [Option.bind_assoc]
  refine umm_loop_bind (α := Bool × Nat) D orc N hN (fun x => x.1) _
    (fun k x st => st = s ∧ (k < N → x.1 = false ∧ x.2 = k)) _ s ?h0 ?hf _
    (fun o => o = some (Result.Ok (), s, orc)) ?hG
  case h0 => exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  case hG =>
    intro x' st ⟨hs, _⟩
    subst hs
    rfl
  case hf =>
    intro k ⟨d, i⟩ st ⟨hs, hI⟩ hk
    obtain ⟨hf0, hik⟩ := hI hk
    simp only at hf0 hik hk
    subst hf0 hik hs
    have hk' : i < N := hk
    clear hk
    have hw := umm_chunk_le N b i W hNb hk'
    simp only [utr_assert_true, umm_ofInt_mul, ExceptT.run_bind, run_liftM, runRW_bind, hpmp (i * b) b hb hw,
      runRW_pure, Option.bind_some]
    sail_norm
    obtain ⟨e1, e2⟩ := umm_idx N i
    refine ⟨_, _, rfl, ⟨rfl, ?_⟩, ?_⟩ <;>
    · simp only [e1, e2]
      by_cases hi : i + 1 = N
      · have h1 : (i == N - 1) = true := by simp; omega
        simp only [h1, if_true, hi, beq_self_eq_true]
        try omega
      · have h1 : (i == N - 1) = false := by simp; omega
        have h2 : (i + 1 == N) = false := by simpa using hi
        simp only [h1, h2, Bool.false_eq_true, if_false]
        try simp

end MachCSL
