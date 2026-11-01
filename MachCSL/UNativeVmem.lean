import MachCSL.UNativeFun

/-! # Relational lemmas for address translation (S1(b) native-step simulation)

`translateAddr` at S/U is relational under `msRelSU` on `mstatus` and equal `satp`/privilege, given
relational `translate` (the page walk) and `translationException`. Monadic glue for the `ExceptT`
layer (`SailME`) lives here too. -/
namespace MachCSL
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled
set_option linter.unusedSimpArgs false
section vmem_rel
variable {D : UFoot} {B : Privilege → Bool} {Rv : RegRel} {G : RegFile → RegFile → Prop}

theorem relRun_liftM {X ε : Type} {m : SailM X} (hm : RelRun D B Rv G m) :
    RelRun D B Rv G ((liftM m : ExceptT ε SailM X) : SailM (Except ε X)) := by
  simp only [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  exact relRun_map _ hm

theorem relRun_monadLift {X ε : Type} {m : SailM X} (hm : RelRun D B Rv G m) :
    RelRun D B Rv G ((monadLift m : ExceptT ε SailM X) : SailM (Except ε X)) := by
  simp only [monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  exact relRun_map _ hm

theorem relRun_assert (b : Bool) (msg : String) : RelRun D B Rv G (assert b msg) := by
  unfold assert PreSail.assert; split
  · exact relRun_pure _
  · exact relRun2_fail _ _ _

theorem relRun_satp_mode_width (m : SATPMode) : RelRun D B Rv G (satp_mode_width_forwards m) := by
  unfold satp_mode_width_forwards
  split
  all_goals first | exact relRun_pure _ | (simp only [assert, PreSail.assert, Bool.false_eq_true, if_false]; exact relRun2_fail _ _ _)

theorem relRun_ebind {ε X Y : Type} {m : ExceptT ε SailM X} {f : X → ExceptT ε SailM Y}
    (hm : RelRun D B Rv G (m : SailM (Except ε X))) (hf : ∀ x, RelRun D B Rv G (f x : SailM (Except ε Y))) :
    RelRun D B Rv G ((m >>= f : ExceptT ε SailM Y) : SailM (Except ε Y)) := by
  show RelRun D B Rv G (ExceptT.bind m f)
  unfold ExceptT.bind ExceptT.mk
  refine relRun_bind hm (fun x => ?_)
  cases x
  · exact relRun_pure _
  · exact hf _

theorem relRun_epure {ε X : Type} (x : X) :
    RelRun D B Rv G ((pure x : ExceptT ε SailM X) : SailM (Except ε X)) := relRun_pure _

theorem relRun_ExceptT_pure {ε X : Type} (x : X) :
    RelRun D B Rv G ((ExceptT.pure x : ExceptT ε SailM X) : SailM (Except ε X)) := relRun_pure _

theorem relRun_SailME_throw {α β : Type} (e : α) :
    RelRun D B Rv G ((SailME.throw e : SailME α β) : SailM (Except (Error exception ⊕ α) β)) := relRun_pure _

theorem relRun_ite {X : Type} (c : Prop) {_ : Decidable c} {a b : SailM X}
    (ha : RelRun D B Rv G a) (hb : RelRun D B Rv G b) : RelRun D B Rv G (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A lifted register read whose continuation is insensitive to the relation. -/
theorem relRun_liftM_read_bind {ε X : Type} (r : Register) (hd : D.Dr r = true)
    {f : RegisterType r → ExceptT ε SailM X} (hf : ∀ v w, Rv r v w → f v = f w)
    (hk : ∀ v, RelRun D B Rv G (f v : SailM (Except ε X))) :
    RelRun D B Rv G ((liftM (readReg r) >>= f : ExceptT ε SailM X) : SailM (Except ε X)) := by
  change RelRun D B Rv G (FreeM.impure (.ok (.regRead r)) (fun v => (f v : SailM (Except ε X))))
  apply relRun2_regRead r hd
  intro v w hvw
  rw [hf v w hvw]
  exact hk w

/-- **`translateAddr`** (the S/U address-translation front end): relational when `mstatus` is related
by `msRelSU` (MXR/SUM/SXL/UXL agree, MPRV clear so the effective privilege is the current one),
`satp` and the privilege are equal, and the page walk and exception mapping are relational. -/
theorem relRun_translateAddr
    (hE : EqRegs D Rv [.satp, .cur_privilege])
    (hdms : D.Dr .mstatus = true)
    (hms : ∀ v w, Rv .mstatus v w ↔ msRelSU v w)
    (htr : ∀ sv asid ppn vpn acc p mxr sum ext, RelRun D B Rv G (translate sv asid ppn vpn acc p mxr sum ext))
    (htex : ∀ acc e, RelRun D B Rv G (translationException acc e))
    (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    RelRun D B Rv G (translateAddr va acc) := by
  have hEs : EqRegs D Rv [.satp] := fun r hr => hE r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact .inl hr)
  have htm := fun p => relRun_translationMode (D := D) (B := B) (G := G) hdms
    (fun v w h => msRelSU_SXL ((hms v w).1 h)) (fun v w h => msRelSU_UXL ((hms v w).1 h)) hEs p
  have hssa : ∀ acc, RelRun D B Rv G (is_shadow_stack_access acc) := by
    intro acc; unfold is_shadow_stack_access; split <;> first | exact relRun_pure _ | exact relRun_internal_error _ _ _
  unfold translateAddr
  simp only [SailME.run, PreSail.PreSailME.run]
  rel_ms hdms hms
  rel_walk hE
  try simp only [Function.comp, FreeM.bind, ExceptT.bindCont]
  rel_walk hE
  show RelRun D B Rv G _
  refine relRun_bind ?_ (fun e0 => ?_)
  rotate_left
  · split <;> first | exact relRun_pure _ | exact relRun2_fail _ _ _
  refine relRun_ebind (relRun_liftM (relRun_pure _)) (fun effPriv => ?_)
  refine relRun_ebind (relRun_liftM (htm _)) (fun mode => ?_)
  refine relRun_ebind (relRun_liftM (hssa _)) (fun b => ?_)
  have hgs : ∀ n, RelRun D B Rv G (get_satp n) := by
    intro n; unfold get_satp
    refine relRun_bind (relRun_assert _ _) (fun _ => ?_)
    split
    · refine relRun_bind ?_ (fun _ => relRun_pure _)
      rel_walk hEs
    · rel_walk hEs
  refine relRun_ite _ ?_ ?_
  refine relRun_ebind (relRun_ite _ (relRun_SailME_throw _) (relRun_ExceptT_pure _)) (fun _ => ?_)
  all_goals
    refine relRun_ite _ (relRun_ExceptT_pure _) ?_
    refine relRun_ebind (relRun_liftM (relRun_satp_mode_width _)) (fun sw => ?_)
    refine relRun_ebind (relRun_liftM (hgs _)) (fun sx => ?_)
    refine relRun_ebind (relRun_liftM (relRun_assert _ _)) (fun _ => ?_)
    refine relRun_ite _ (relRun_ebind (relRun_liftM (htex _ _)) (fun _ => relRun_ExceptT_pure _)) ?_
    refine relRun_liftM_read_bind .mstatus hdms (fun v w h => ?_) (fun v1 => ?_)
    · simp only [msRelSU_MXR ((hms v w).1 h)]
    refine relRun_liftM_read_bind .mstatus hdms (fun v w h => ?_) (fun v2 => ?_)
    · simp only [msRelSU_SUM ((hms v w).1 h)]
    refine relRun_ebind (relRun_liftM (htr _ _ _ _ _ _ _ _ _)) (fun res => ?_)
    split
    · exact relRun_ExceptT_pure _
    · exact relRun_ebind (relRun_liftM (htex _ _)) (fun _ => relRun_ExceptT_pure _)
/-- `translationException`: a pure map. -/
theorem relRun_translationException (acc : MemoryAccessType mem_payload) (e : PTW_Error) :
    RelRun D B Rv G (translationException acc e) := by
  unfold translationException
  split
  all_goals (try split)
  all_goals first | exact relRun_pure _ | exact relRun_internal_error _ _ _

/-- `lookup_TLB`: one read of the (equal) software TLB. -/
theorem relRun_lookup_TLB (hE : EqRegs D Rv [.tlb]) (sv : Nat) (asid : BitVec 16) (vpn : BitVec (sv - 12)) :
    RelRun D B Rv G (lookup_TLB sv asid vpn) := by
  unfold lookup_TLB
  rel_walk hE
  all_goals (try split)
  all_goals (try split)
  all_goals (rel_walk hE)

/-- **`translate`**: TLB lookup, then the hit or miss path (both assumed relational). -/
theorem relRun_translate (hE : EqRegs D Rv [.tlb])
    (hhit : ∀ sv asid vpn acc p mxr sum ext i ent,
      RelRun D B Rv G (translate_TLB_hit sv asid vpn acc p mxr sum ext i ent))
    (hmiss : ∀ sv asid ppn vpn acc p mxr sum ext,
      RelRun D B Rv G (translate_TLB_miss sv asid ppn vpn acc p mxr sum ext))
    (sv : Nat) (asid : BitVec 16) (ppn : BitVec (if decide (sv = 32) = true then 22 else 44))
    (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr sum : Bool) (ext : Unit) :
    RelRun D B Rv G (translate sv asid ppn vpn acc p mxr sum ext) := by
  unfold translate
  refine relRun_bind (relRun_lookup_TLB hE _ _ _) (fun r => ?_)
  split
  · exact hhit _ _ _ _ _ _ _ _ _ _
  · exact hmiss _ _ _ _ _ _ _ _ _

end vmem_rel

end MachCSL
