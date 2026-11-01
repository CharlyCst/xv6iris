import MachCSL.UNativeVmem
import MachCSL.UCycle

/-! # Relational lemmas for the memory subsystem and the page walk (S1(b) native-step simulation)

Every function on the S/U memory path — PMA/PMP checks, split accesses, RAM/MMIO dispatch,
`checked_mem_read`/`checked_mem_write`, PTE reads/writes, the leaf and permission checks, the A/D
update, the TLB, the recursive `pt_walk` and `translate` — is `RelRun` (same program, related
states, related results) under:

* equal `pma_regions`, `htif_tohost_base`, `menvcfg`, `tlb` (`EqRegs`) and the reset `misa`;
* **leaf premises** `pmpCheck` relational (discharged later from `G` and the vPMP models) and
  MMIO relational (`mmio_read`/`mmio_write`; to be discharged by the S2(a) no-MMIO premise).

`rel_auto` is a structural relational walk: SailME/ExceptT glue, join points, leaf lemmas from
the context (`solve_by_elim`, reducible), and only then `rel_step` (which inlines). Functions whose
body hides expensive pure computations in `match` scrutinees (`update_PTE_Bits`) or uses join
points are proved by explicit scripts. -/
namespace MachCSL
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
set_option linter.unusedSimpArgs false
section
variable {D : UFoot} {B : Privilege → Bool} {Rv : RegRel} {G : RegFile → RegFile → Prop}

/-- A read-only computation answered by a closed reference map fixed by the relation. -/
theorem relRun_of_runRead (dref : (r : Register) → Option (RegisterType r))
    (hdref : ∀ r v, dref r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    {X : Type} (m : SailM X) (h : (runRead dref m).isSome = true) : RelRun D B Rv G m := by
  obtain ⟨⟨x, b⟩, hx⟩ := Option.isSome_iff_exists.mp h
  have := relRun2_runRead_bind (D := D) (B := B) (G := G) dref hdref m x b hx pure pure (relRun2_pure x)
  simp only [bind_pure] at this
  exact this

/-- `currentlyEnabled e` for an extension decided by `misa` alone. -/
theorem relRun_currentlyEnabled
    (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    (e : extension) (h : (runRead ucDrefMisa (currentlyEnabled e)).isSome = true) :
    RelRun D B Rv G (currentlyEnabled e) :=
  relRun_of_runRead ucDrefMisa hmisa _ h

macro "rel_leafM " hE:ident hmisa:ident : tactic => `(tactic| (repeat (first
  | rel_step $hE
  | exact relRun_internal_error _ _ _
  | exact relRun2_fail _ _ _
  | exact relRun_assert _ _
  | (with_reducible_and_instances refine relRun_bind (relRun_assert _ _) (fun _ => ?_))
  | (with_reducible_and_instances refine relRun_bind (relRun_pure _) (fun _ => ?_))
  | (with_reducible_and_instances refine relRun_bind (relRun_currentlyEnabled $hmisa _ (by kernel_rfl)) (fun _ => ?_))
  | (with_reducible_and_instances exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
  | (refine relRun_ite _ ?_ ?_)
  | (with_reducible_and_instances refine relRun_bind (relRun_ite _ ?_ ?_) (fun _ => ?_))
  | split)))

macro "rel_leaf " hE:ident : tactic => `(tactic| (repeat (first
  | rel_step $hE
  | exact relRun_internal_error _ _ _
  | exact relRun2_fail _ _ _
  | exact relRun_assert _ _
  | (with_reducible_and_instances refine relRun_bind (relRun_assert _ _) (fun _ => ?_))
  | (with_reducible_and_instances refine relRun_bind (relRun_pure _) (fun _ => ?_))
  | (refine relRun_ite _ ?_ ?_)
  | (with_reducible_and_instances refine relRun_bind (relRun_ite _ ?_ ?_) (fun _ => ?_))
  | split)))

theorem relRun_read_kind_of_flags (hE : EqRegs D Rv []) (a b c : Bool) :
    RelRun D B Rv G (read_kind_of_flags a b c) := by
  unfold read_kind_of_flags; rel_leaf hE

theorem relRun_write_kind_of_flags (hE : EqRegs D Rv []) (a b c : Bool) :
    RelRun D B Rv G (write_kind_of_flags a b c) := by
  unfold write_kind_of_flags; rel_leaf hE

theorem relRun_accessFaultFromAccessType (hE : EqRegs D Rv []) (a : MemoryAccessType mem_payload) :
    RelRun D B Rv G (accessFaultFromAccessType a) := by
  unfold accessFaultFromAccessType; rel_leaf hE

theorem relRun_alignmentFaultFromAccessType (hE : EqRegs D Rv []) (a : MemoryAccessType mem_payload) :
    RelRun D B Rv G (alignmentFaultFromAccessType a) := by
  unfold alignmentFaultFromAccessType; rel_leaf hE

theorem relRun_split_misaligned (hE : EqRegs D Rv []) (p : physaddr) (w e : Nat) (s : Splittability) :
    RelRun D B Rv G (split_misaligned p w e s) := by
  unfold split_misaligned split_access; rel_leaf hE

theorem relRun_within_mmio_readable (hE : EqRegs D Rv [.htif_tohost_base]) (p : physaddr) (w : Nat) :
    RelRun D B Rv G (within_mmio_readable p w) := by
  unfold within_mmio_readable within_clint within_sig within_htif_readable within_htif_writable; rel_leaf hE

theorem relRun_within_mmio_writable (hE : EqRegs D Rv [.htif_tohost_base]) (p : physaddr) (w : Nat) :
    RelRun D B Rv G (within_mmio_writable p w) := by
  unfold within_mmio_writable within_clint within_sig within_htif_writable; rel_leaf hE

theorem relRun_mag_pma_check (hE : EqRegs D Rv []) (pma : PMA) (a : MemoryAccessType mem_payload) (p : physaddr) (w : Nat) :
    RelRun D B Rv G (mag_pma_check pma a p w) := by
  unfold mag_pma_check is_mag_applicable_access pma_misaligned_exception; rel_leaf hE

theorem relRun_pte_is_invalid (hE : EqRegs D Rv [.menvcfg])
    (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    (f : BitVec 8) (e : BitVec 10) :
    RelRun D B Rv G (pte_is_invalid f e) := by
  unfold pte_is_invalid; rel_leafM hE hmisa

theorem relRun_read_ram (hE : EqRegs D Rv []) (rk : read_kind) (p : physaddr) (w : Nat) (m : Bool) :
    RelRun D B Rv G (read_ram rk p w m) := by
  unfold read_ram; rel_leaf hE

theorem relRun_write_ram (hE : EqRegs D Rv []) (wk : write_kind) (p : physaddr) (w : Nat) (d : BitVec (8 * w)) (m : Unit) :
    RelRun D B Rv G (write_ram wk p w d m) := by
  unfold write_ram; rel_leaf hE


theorem relRun_untilFuelM {ε α : Type} (cond : α → ExceptT ε SailM Bool) (f : α → ExceptT ε SailM α)
    (hc : ∀ x, RelRun D B Rv G (cond x : SailM (Except ε Bool)))
    (hf : ∀ x, RelRun D B Rv G (f x : SailM (Except ε α))) (n : Nat) (x : α) :
    RelRun D B Rv G (untilFuelM (m := ExceptT ε SailM) n cond x f : SailM (Except ε α)) := by
  unfold untilFuelM
  induction n generalizing x with
  | zero => exact relRun_epure _
  | succ n ih =>
    unfold untilFuelM.go
    refine relRun_ebind (hf x) (fun y => ?_)
    refine relRun_ebind (hc y) (fun b => ?_)
    refine relRun_ite _ (relRun_epure _) (ih y)

theorem relRun_fbind {X Y : Type} {m : SailM X} {f : X → SailM Y} (hm : RelRun D B Rv G m)
    (hf : ∀ x, RelRun D B Rv G (f x)) : RelRun D B Rv G (FreeM.bind m f) := relRun_bind hm hf

theorem relRun_bindCont {ε X Y : Type} {f : X → SailM (Except ε Y)} (hf : ∀ a, RelRun D B Rv G (f a))
    (x : Except ε X) : RelRun D B Rv G (ExceptT.bindCont f x) := by
  cases x
  · exact relRun_pure _
  · exact hf _

theorem relRun_SailME_run {α : Type} {m : SailME α α}
    (hm : RelRun D B Rv G (m : SailM (Except (Error exception ⊕ α) α))) :
    RelRun D B Rv G (SailME.run m) := by
  unfold SailME.run PreSail.PreSailME.run
  refine relRun_bind hm (fun x => ?_)
  rcases x with (e | e) | e
  · exact relRun2_fail _ _ _
  · exact relRun_pure _
  · exact relRun_pure _

theorem relRun_eite {ε X : Type} (c : Prop) {_ : Decidable c} {a b : ExceptT ε SailM X}
    (ha : RelRun D B Rv G (a : SailM (Except ε X))) (hb : RelRun D B Rv G (b : SailM (Except ε X))) :
    RelRun D B Rv G ((if c then a else b : ExceptT ε SailM X) : SailM (Except ε X)) := by
  split
  · exact ha
  · exact hb

/-- A join point (`have jp := J; body jp`): relational if `J` is and `body` is for any relational `jp`. -/
theorem relRun_jp {α Y X : Type} (J : α → SailM Y) (body : (α → SailM Y) → SailM X)
    (hJ : ∀ a, RelRun D B Rv G (J a)) (hb : ∀ j : α → SailM Y, (∀ a, RelRun D B Rv G (j a)) → RelRun D B Rv G (body j)) :
    RelRun D B Rv G (have j := J; body j) := hb J hJ

syntax "rel_auto " ident ident : tactic
macro_rules
  | `(tactic| rel_auto $hE $hmisa) => `(tactic| (repeat (first
    | (with_reducible_and_instances refine relRun_SailME_run ?_)
    | (set_option simprocs false in dsimp only)
    | (with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_); with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun_fbind ?_ (fun _ => ?_); with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun2_of_relRun ?_)
    | (with_reducible_and_instances refine relRun_ite _ ?_ ?_)
    | (with_reducible_and_instances refine relRun_eite _ ?_ ?_)
    | (with_reducible_and_instances refine relRun_ebind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_liftM ?_)
    | (with_reducible_and_instances refine relRun_monadLift ?_)
    | (with_reducible_and_instances refine relRun_untilFuelM _ _ (fun _ => ?_) (fun _ => ?_) _ _)
    | (with_reducible exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_); with_reducible exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (dsimp only [FreeM.bind])
    | rel_step $hE
    | (simp only [Function.comp, FreeM.bind, ExceptT.bindCont])
    | (with_reducible_and_instances exact relRun_internal_error _ _ _)
    | (with_reducible_and_instances exact relRun_assert _ _)
    | (with_reducible_and_instances exact relRun_ExceptT_pure _)
    | (with_reducible_and_instances exact relRun_epure _)
    | (with_reducible_and_instances exact relRun_SailME_throw _)
    | (with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_fbind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_bindCont (fun _ => ?_) _)
    | split
    | exact relRun2_fail _ _ _
    | exact relRun_SailME_throw _
    | exact relRun_ExceptT_pure _)))

syntax "rel_autoW " ident ident ident ident ident : tactic
macro_rules
  | `(tactic| rel_autoW $hE $hmisa $hW $hrefl $hG) => `(tactic| (repeat (first
    | (with_reducible_and_instances refine relRun_SailME_run ?_)
    | (set_option simprocs false in dsimp only)
    | (with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_); with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun_fbind ?_ (fun _ => ?_); with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances refine relRun2_of_relRun ?_)
    | (with_reducible_and_instances refine relRun_ite _ ?_ ?_)
    | (with_reducible_and_instances refine relRun_eite _ ?_ ?_)
    | (with_reducible_and_instances refine relRun_ebind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_liftM ?_)
    | (with_reducible_and_instances refine relRun_monadLift ?_)
    | (with_reducible_and_instances refine relRun_untilFuelM _ _ (fun _ => ?_) (fun _ => ?_) _ _)
    | (with_reducible exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_); with_reducible exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (dsimp only [FreeM.bind])
    | rel_stepW $hE $hW $hrefl $hG
    | (simp only [Function.comp, FreeM.bind, ExceptT.bindCont])
    | (with_reducible_and_instances exact relRun_internal_error _ _ _)
    | (with_reducible_and_instances exact relRun_assert _ _)
    | (with_reducible_and_instances exact relRun_ExceptT_pure _)
    | (with_reducible_and_instances exact relRun_epure _)
    | (with_reducible_and_instances exact relRun_SailME_throw _)
    | (with_reducible solve_by_elim (maxDepth := 2) only [*])
    | (with_reducible_and_instances exact relRun_currentlyEnabled $hmisa _ (by kernel_rfl))
    | (with_reducible_and_instances refine relRun_bind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_fbind ?_ (fun _ => ?_))
    | (with_reducible_and_instances refine relRun_bindCont (fun _ => ?_) _)
    | split
    | exact relRun2_fail _ _ _
    | exact relRun_SailME_throw _
    | exact relRun_ExceptT_pure _)))

theorem relRun_page_based_mem_type_forwards (b : BitVec 2) :
    RelRun D B Rv G (page_based_mem_type_forwards b) := by
  have hE0 : EqRegs D Rv [] := fun r h => by simp at h
  unfold page_based_mem_type_forwards; rel_leaf hE0

theorem relRun_pmaCheck (hE : EqRegs D Rv [.pma_regions])
    (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    (p : physaddr) (w : Nat) (a : MemoryAccessType mem_payload) (pb : page_based_mem_type) (rc : Bool) :
    RelRun D B Rv G (pmaCheck p w a pb rc) := by
  have hE0 : EqRegs D Rv [] := fun r h => by simp at h
  unfold pmaCheck
  have l1 := relRun_accessFaultFromAccessType (B := B) (G := G) hE0
  have l2 := relRun_alignmentFaultFromAccessType (B := B) (G := G) hE0
  have l3 := relRun_mag_pma_check (B := B) (G := G) hE0
  rel_auto hE hmisa

section memrel
variable (hE : EqRegs D Rv [.pma_regions, .htif_tohost_base])
  (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
  (hpmp : ∀ p w a pr, RelRun D B Rv G (pmpCheck p w a pr))
  (hmmr : ∀ a p w, RelRun D B Rv G (mmio_read a p w))
  (hmmw : ∀ p w d, RelRun D B Rv G (mmio_write p w d))
include hE hmisa hpmp

theorem relRun_check_pma_with_pmp_priority (a : MemoryAccessType mem_payload) (pb : page_based_mem_type)
    (pr : Privilege) (p : physaddr) (w : Nat) (rc : Bool) :
    RelRun D B Rv G (check_pma_with_pmp_priority a pb pr p w rc) := by
  have hE1 : EqRegs D Rv [.pma_regions] := fun r h => hE r (by simp at h ⊢; simp [h])
  have l1 := relRun_pmaCheck (B := B) (G := G) hE1 hmisa
  unfold check_pma_with_pmp_priority
  rel_auto hE hmisa

theorem relRun_checked_mem_read (hmmr : ∀ a p w, RelRun D B Rv G (mmio_read a p w))
    (a : MemoryAccessType mem_payload) (pb : page_based_mem_type)
    (pr : Privilege) (p : physaddr) (w : Nat) (aq rl res m : Bool) :
    RelRun D B Rv G (checked_mem_read a pb pr p w aq rl res m) := by
  have hE0 : EqRegs D Rv [] := fun r h => by simp at h
  have hE2 : EqRegs D Rv [.htif_tohost_base] := fun r h => hE r (by simp at h ⊢; simp [h])
  have l1 := relRun_check_pma_with_pmp_priority hE hmisa hpmp
  have l2 := relRun_split_misaligned (B := B) (G := G) hE0
  have l3 := relRun_read_kind_of_flags (B := B) (G := G) hE0
  have l4 := relRun_within_mmio_readable (B := B) (G := G) hE2
  have l5 := relRun_read_ram (B := B) (G := G) hE0
  unfold checked_mem_read
  rel_auto hE hmisa

theorem relRun_checked_mem_write (hmmw : ∀ p w d, RelRun D B Rv G (mmio_write p w d))
    (p : physaddr) (w : Nat) (d : BitVec (8 * w)) (a : MemoryAccessType mem_payload) (pb : page_based_mem_type)
    (pr : Privilege) (m : Unit) (aq rl con : Bool) :
    RelRun D B Rv G (checked_mem_write p w d a pb pr m aq rl con) := by
  have hE0 : EqRegs D Rv [] := fun r h => by simp at h
  have hE2 : EqRegs D Rv [.htif_tohost_base] := fun r h => hE r (by simp at h ⊢; simp [h])
  have l1 := relRun_check_pma_with_pmp_priority hE hmisa hpmp
  have l2 := relRun_split_misaligned (B := B) (G := G) hE0
  have l3 := relRun_write_kind_of_flags (B := B) (G := G) hE0
  have l4 := relRun_within_mmio_writable (B := B) (G := G) hE2
  have l5 := relRun_write_ram (B := B) (G := G) hE0
  unfold checked_mem_write
  rel_auto hE hmisa

end memrel

section ptw
variable (hE : EqRegs D Rv [.pma_regions, .htif_tohost_base, .menvcfg, .tlb])
  (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
  (hpmp : ∀ p w a pr, RelRun D B Rv G (pmpCheck p w a pr))
  (hmmr : ∀ a p w, RelRun D B Rv G (mmio_read a p w))
  (hmmw : ∀ p w d, RelRun D B Rv G (mmio_write p w d))
  (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G)
include hE hmisa hpmp hmmr hmmw

theorem relRun_read_pte (p : physaddr) (n : Nat) : RelRun D B Rv G (read_pte p n) := by
  have hE1 : EqRegs D Rv [.pma_regions, .htif_tohost_base] := fun r h => hE r (by simp at h ⊢; rcases h with h | h <;> simp [h])
  have l1 := relRun_checked_mem_read hE1 hmisa hpmp hmmr
  unfold read_pte mem_read_priv
  refine relRun_bind ?_ (fun _ => relRun_pure _)
  unfold mem_read_priv_meta
  refine relRun_bind (l1 _ _ _ _ _ _ _ _ _) (fun _ => relRun_pure _)

theorem relRun_write_pte (p : physaddr) (n : Nat) (v : BitVec (n * 8)) : RelRun D B Rv G (write_pte p n v) := by
  have hE1 : EqRegs D Rv [.pma_regions, .htif_tohost_base] := fun r h => hE r (by simp at h ⊢; rcases h with h | h <;> simp [h])
  have l1 := relRun_checked_mem_write hE1 hmisa hpmp hmmw
  unfold write_pte mem_write_value_priv mem_write_value_priv_meta
  rel_auto hE hmisa

theorem relRun_read_pte_exclusive (p : physaddr) (n : Nat) : RelRun D B Rv G (read_pte_exclusive p n) := by
  have hE1 : EqRegs D Rv [.pma_regions, .htif_tohost_base] := fun r h => hE r (by simp at h ⊢; rcases h with h | h <;> simp [h])
  have l1 := relRun_checked_mem_read hE1 hmisa hpmp hmmr
  unfold read_pte_exclusive mem_read_priv
  refine relRun_bind ?_ (fun _ => relRun_pure _)
  unfold mem_read_priv_meta
  refine relRun_bind (l1 _ _ _ _ _ _ _ _ _) (fun _ => relRun_pure _)

theorem relRun_write_pte_conditional (p : physaddr) (n : Nat) (v : BitVec (n * 8)) : RelRun D B Rv G (write_pte_conditional p n v) := by
  have hE1 : EqRegs D Rv [.pma_regions, .htif_tohost_base] := fun r h => hE r (by simp at h ⊢; rcases h with h | h <;> simp [h])
  have l1 := relRun_checked_mem_write hE1 hmisa hpmp hmmw
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  rel_auto hE hmisa

theorem relRun_check_PTE_permission (a : MemoryAccessType mem_payload) (pr : Privilege) (mxr sum : Bool)
    (f : BitVec 8) (e : BitVec 10) (x : Unit) : RelRun D B Rv G (check_PTE_permission a pr mxr sum f e x) := by
  have hssa : ∀ acc, RelRun D B Rv G (is_shadow_stack_access acc) := by
    intro acc; unfold is_shadow_stack_access; split <;> first | exact relRun_pure _ | exact relRun_internal_error _ _ _
  unfold check_PTE_permission
  rel_auto hE hmisa

theorem relRun_check_leaf_pte (sv : Nat) (vpn : BitVec (sv - 12)) (a : MemoryAccessType mem_payload)
    (pr : Privilege) (mxr sum : Bool) (pte : BitVec (if decide (sv = 32) = true then 32 else 64))
    (pa : physaddr) (lvl : Nat) (x : Unit) :
    RelRun D B Rv G (check_leaf_pte sv vpn a pr mxr sum pte pa lvl x) := by
  have hE1 : EqRegs D Rv [.menvcfg] := fun r h => hE r (by simp at h ⊢; simp [h])
  have l1 := relRun_pte_is_invalid (B := B) (G := G) hE1 hmisa
  have l2 := relRun_check_PTE_permission hE hmisa hpmp hmmr hmmw
  have l3 := relRun_page_based_mem_type_forwards (D := D) (B := B) (Rv := Rv) (G := G)
  unfold check_leaf_pte
  rel_auto hE hmisa

theorem relRun_update_and_write_pte (sv : Nat) (vpn : BitVec (sv - 12)) (pa : physaddr)
    (pte : BitVec (if decide (sv = 32) = true then 32 else 64)) (lvl : Nat) (a : MemoryAccessType mem_payload)
    (pr : Privilege) (mxr sum : Bool) (x : Unit) :
    RelRun D B Rv G (update_and_write_pte sv vpn pa pte lvl a pr mxr sum x) := by
  have l1 := relRun_write_pte_conditional hE hmisa hpmp hmmr hmmw
  have l2 := relRun_read_pte_exclusive hE hmisa hpmp hmmr hmmw
  have l3 := relRun_check_leaf_pte hE hmisa hpmp hmmr hmmw
  unfold update_and_write_pte
  split
  · exact relRun_pure _
  refine relRun_bind (relRun_currentlyEnabled hmisa _ (by kernel_rfl)) (fun b => ?_)
  extract_lets pw jp2 jp
  have hjp2 : ∀ d, RelRun D B Rv G (jp2 d) := by
    intro d
    simp only [jp2, pw]
    refine relRun_ite _ ?_ (relRun_pure _)
    refine relRun_bind (l2 _ _) (fun r => ?_)
    split
    · exact relRun_pure _
    refine relRun_bind (l3 _ _ _ _ _ _ _ _ _ _) (fun r2 => ?_)
    split
    · exact relRun_pure _
    split
    · exact relRun_pure _
    refine relRun_bind (l1 _ _ _) (fun r3 => ?_)
    split
    all_goals first | exact relRun_pure _ | exact relRun_internal_error _ _ _
  clear_value jp2
  have hjp : ∀ c, RelRun D B Rv G (jp c) := by
    intro c
    simp only [jp]
    rel_auto hE hmisa
  clear_value jp
  rel_auto hE hmisa

theorem relRun_add_to_TLB (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G)
    (sv : Nat) (asid : BitVec 16) (vpn : BitVec (sv - 12))
    (ppn : BitVec (if decide (sv = 32) = true then 22 else 44)) (pte : BitVec (if decide (sv = 32) = true then 32 else 64))
    (pa : physaddr) (lvl : Nat) (g : Bool) :
    RelRun D B Rv G (add_to_TLB sv asid vpn ppn pte pa lvl g) := by
  unfold add_to_TLB
  rel_autoW hE hmisa hW hrefl hG

theorem relRun_write_TLB (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G)
    (i : Nat) (e : TLB_Entry) : RelRun D B Rv G (write_TLB i e) := by
  unfold write_TLB
  rel_autoW hE hmisa hW hrefl hG

theorem relRun_tlb_get_pbmt (e : TLB_Entry) : RelRun D B Rv G (tlb_get_pbmt e) := by
  unfold tlb_get_pbmt; exact relRun_page_based_mem_type_forwards _

theorem relRun_translate_TLB_hit (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G)
    (sv : Nat) (asid : BitVec 16) (vpn : BitVec (sv - 12)) (a : MemoryAccessType mem_payload) (pr : Privilege)
    (mxr sum : Bool) (x : Unit) (i : Nat) (ent : TLB_Entry) :
    RelRun D B Rv G (translate_TLB_hit sv asid vpn a pr mxr sum x i ent) := by
  have l1 := relRun_check_PTE_permission hE hmisa hpmp hmmr hmmw
  have l2 := relRun_update_and_write_pte hE hmisa hpmp hmmr hmmw
  have l3 := relRun_write_TLB hE hmisa hpmp hmmr hmmw hW hrefl hG
  have l4 := relRun_tlb_get_pbmt hE hmisa hpmp hmmr hmmw (B := B) (G := G)
  unfold translate_TLB_hit
  rel_auto hE hmisa

theorem relRun_pt_walk (sv : Nat) (vpn : BitVec (sv - 12)) (a : MemoryAccessType mem_payload) (pr : Privilege)
    (mxr sum : Bool) (x : Unit) (lvl : Nat) :
    ∀ (base : BitVec (if decide (sv = 32) = true then 22 else 44)) (g : Bool),
      RelRun D B Rv G (pt_walk sv vpn a pr mxr sum base lvl g x) := by
  have hE1 : EqRegs D Rv [.menvcfg] := fun r h => hE r (by simp at h ⊢; simp [h])
  have l1 := relRun_read_pte hE hmisa hpmp hmmr hmmw
  have l2 := relRun_pte_is_invalid (B := B) (G := G) hE1 hmisa
  have l3 := relRun_check_leaf_pte hE hmisa hpmp hmmr hmmw
  induction lvl using Nat.strongRecOn with
  | ind n ih =>
    intro base g
    rw [pt_walk]
    set_option simprocs false in dsimp only
    refine relRun_bind (relRun_assert _ _) (fun _ => ?_)
    refine relRun_bind (l1 _ _) (fun r => ?_)
    split
    · exact relRun_pure _
    refine relRun_bind (l2 _ _) (fun b => ?_)
    split
    · rename_i h
      have hn : 0 < n := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        omega
      exact ih _ (by omega) _ _
    · refine relRun_bind (l3 _ _ _ _ _ _ _ _ _ _) (fun r => ?_)
      split <;> exact relRun_pure _

theorem relRun_translate_TLB_miss (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G)
    (sv : Nat) (asid : BitVec 16) (ppn : BitVec (if decide (sv = 32) = true then 22 else 44)) (vpn : BitVec (sv - 12))
    (a : MemoryAccessType mem_payload) (pr : Privilege) (mxr sum : Bool) (x : Unit) :
    RelRun D B Rv G (translate_TLB_miss sv asid ppn vpn a pr mxr sum x) := by
  have l1 := relRun_pt_walk hE hmisa hpmp hmmr hmmw
  have l2 := relRun_update_and_write_pte hE hmisa hpmp hmmr hmmw
  have l3 := relRun_add_to_TLB hE hmisa hpmp hmmr hmmw hW hrefl hG
  unfold translate_TLB_miss
  set_option simprocs false in dsimp only
  refine relRun_bind (l1 _ _ _ _ _ _ _ _ _ _) (fun r => ?_)
  split
  · exact relRun_pure _
  refine relRun_bind (l2 _ _ _ _ _ _ _ _ _ _) (fun r2 => ?_)
  split
  all_goals first
    | exact relRun_pure _
    | (refine relRun_bind (l3 _ _ _ _ _ _ _ _) (fun _ => relRun_pure _))

/-- **The full page walk front end** (`translate`): TLB lookup, hit (permission check, A/D update,
TLB refill) and miss (page-table walk, A/D update, TLB fill), relational given relational PMP checks
and MMIO. -/
theorem relRun_translate_full (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v)
    (hG : GStable D Rv G) (sv : Nat) (asid : BitVec 16) (ppn : BitVec (if decide (sv = 32) = true then 22 else 44))
    (vpn : BitVec (sv - 12)) (a : MemoryAccessType mem_payload) (p : Privilege) (mxr sum : Bool) (ext : Unit) :
    RelRun D B Rv G (translate sv asid ppn vpn a p mxr sum ext) := by
  have hE1 : EqRegs D Rv [.tlb] := fun r h => hE r (by simp at h ⊢; simp [h])
  exact relRun_translate hE1 (relRun_translate_TLB_hit hE hmisa hpmp hmmr hmmw hW hrefl hG)
    (relRun_translate_TLB_miss hE hmisa hpmp hmmr hmmw hW hrefl hG) _ _ _ _ _ _ _ _ _

/-- **Address translation at S/U** (`translateAddr`), with no remaining relational premise on the
page walk: relational under `msRelSU`, equal `satp`/privilege/TLB/PMA/`menvcfg`, relational PMP
checks and MMIO. -/
theorem relRun_translateAddr_full (hW : ∀ r ∈ [Register.tlb], D.Dw r = true) (hrefl : ∀ r v, Rv r v v)
    (hG : GStable D Rv G) (hEs : EqRegs D Rv [.satp, .cur_privilege]) (hdms : D.Dr .mstatus = true)
    (hms : ∀ v w, Rv .mstatus v w ↔ msRelSU v w) (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    RelRun D B Rv G (translateAddr va acc) :=
  relRun_translateAddr hEs hdms hms (relRun_translate_full hE hmisa hpmp hmmr hmmw hW hrefl hG)
    relRun_translationException va acc

end ptw

end
end MachCSL
