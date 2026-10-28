/-
MachCSL: **`ukd_run`, the stepper for walks over a memory with dirty bytes**
(`URunD.uxdRun`) -- the twin of `UkfWalk.ukf_run` (same construction):

1. the goal `uxdRun D T dirty orc s m = rhs` is read as the `runRW` goal;
2. the stepper runs with the two LEAVES as sub-walk facts: `ukd_leaf` (a
   plain read, or a fetch of a clean window, of bytes in `T` answers `T`) and
   `ukd_leafD` (a fetch of a dirty window answers the merge of `T` with the
   oracle's head choice, the oracle advanced);
3. the proof term is carried back: `runRW` ↦ `ukdRun T dirty`, every step
   lemma ↦ its twin below.

A plain read the stepper would answer from the walker's map (`uwk_mrd`) has
no twin; the kernel re-checks the carried term.
-/
import MachCSL.URunD
import MachCSL.UWalkRun

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `uxdRun` with the map and the dirty bytes as the first arguments. -/
def ukdRun (T : BMap) (dirty : PAddr → Bool) {X : Type} (D : UFoot) :
    UOrc → UWSt → SailM X → Option (X × UWSt × UOrc) := uxdRun D T dirty

/-! ## The `ukdRun` twins of `UWalkRun`'s step lemmas (`T dirty`, then the same binders) -/

theorem ukd_pure (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (x : X) :
    ukdRun T dirty D orc s (FreeM.pure x : SailM X) = some (x, s, orc) := rfl

theorem ukd_bind (T : BMap) (dirty : PAddr → Bool) (X Y : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (m : SailM Y) (f : Y → SailM X)
    (y : Y) (s' : UWSt) (orc' : UOrc) (r : Option (X × UWSt × UOrc))
    (h1 : ukdRun T dirty D orc s m = some (y, s', orc')) (h2 : ukdRun T dirty D orc' s' (f y) = r) :
    ukdRun T dirty D orc s (FreeM.bind m f) = r := by
  rw [← h2]
  exact uxdw_bind_some D T dirty m f orc orc' s s' y h1

theorem ukd_bind_none (T : BMap) (dirty : PAddr → Bool) (X Y : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (m : SailM Y)
    (f : Y → SailM X) (h1 : ukdRun T dirty D orc s m = none) : ukdRun T dirty D orc s (FreeM.bind m f) = none :=
  uxdw_bind_none D T dirty m f orc s h1

theorem ukd_congr (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (m m' : SailM X)
    (r : Option (X × UWSt × UOrc)) (hm : m = m') (h : ukdRun T dirty D orc s m' = r) : ukdRun T dirty D orc s m = r := by
  rw [hm]; exact h

theorem ukd_ite_pos (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (c : Prop) (inst : Decidable c)
    (a b : SailM X) (r : Option (X × UWSt × UOrc)) (hc : c) (h : ukdRun T dirty D orc s a = r) :
    ukdRun T dirty D orc s (@ite _ c inst a b) = r := by
  rw [if_pos hc]; exact h

theorem ukd_ite_neg (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (c : Prop) (inst : Decidable c)
    (a b : SailM X) (r : Option (X × UWSt × UOrc)) (hc : ¬ c) (h : ukdRun T dirty D orc s b = r) :
    ukdRun T dirty D orc s (@ite _ c inst a b) = r := by
  rw [if_neg hc]; exact h

theorem ukd_dite_pos (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (c : Prop) (inst : Decidable c)
    (a : c → SailM X) (b : ¬ c → SailM X) (r : Option (X × UWSt × UOrc)) (hc : c)
    (h : ukdRun T dirty D orc s (a hc) = r) : ukdRun T dirty D orc s (@dite _ c inst a b) = r := by
  rw [dif_pos hc]; exact h

theorem ukd_dite_neg (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (c : Prop) (inst : Decidable c)
    (a : c → SailM X) (b : ¬ c → SailM X) (r : Option (X × UWSt × UOrc)) (hc : ¬ c)
    (h : ukdRun T dirty D orc s (b hc) = r) : ukdRun T dirty D orc s (@dite _ c inst a b) = r := by
  rw [dif_neg hc]; exact h

theorem ukd_error (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (e : Sail.Error exception)
    (k : Empty → SailM X) :
    ukdRun T dirty D orc s (FreeM.impure (Except.error e) k : SailM X) = none := rfl

/-- A node the text map does not answer, whose one-node walk is known. -/
theorem ukd_node_of {X : Type} (T : BMap) (dirty : PAddr → Bool) (D : UFoot) (orc : UOrc) (s : UWSt) (c : Eff RegisterType exception)
    (k : ArchSem.Effect.ret c → SailM X) (hc : uxwIsText T c = false) (v : ArchSem.Effect.ret c) (s' : UWSt)
    (o' : UOrc) (h1 : runRW D orc s (FreeM.impure c FreeM.pure) = some (v, s', o')) :
    ukdRun T dirty D orc s (FreeM.impure c k) = ukdRun T dirty D o' s' (k v) := by
  unfold ukdRun
  rw [uxdw_node D T dirty orc s c k hc, h1]; rfl

theorem ukd_rr (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (r : Register) (v : RegisterType r)
    (k : RegisterType r → SailM X) (res : Option (X × UWSt × UOrc))
    (hd : D.Dr r = true) (hv : s.file r = v) (h : ukdRun T dirty D orc s (k v) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.regRead r)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.regRead r)) k rfl v s orc (by rw [runRW_regRead_dr D orc s r _ hd, hv]; rfl)

theorem ukd_rr_any (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (r : Register)
    (k : RegisterType r → SailM X) (res : Option (X × UWSt × UOrc))
    (hd : D.Dr r = false) (ha : D.Dany r = true) (h : ukdRun T dirty D orc.tail s (k ((orc 0).reg r)) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.regRead r)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.regRead r)) k rfl ((orc 0).reg r) s orc.tail
    (by rw [runRW_regRead_any D orc s r _ hd ha]; rfl)

theorem ukd_rw (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (r : Register) (v : RegisterType r)
    (k : PUnit → SailM X) (res : Option (X × UWSt × UOrc))
    (hd : D.Dw r = true) (h : ukdRun T dirty D orc (UWSt.mk (s.pin.set r v) s.rs s.mm s.rv) (k ()) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.regWrite r v)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.regWrite r v)) k rfl PUnit.unit _ orc (by simp only [runRW, hd, if_true])

theorem ukd_isText_excl {n vasize : Nat} (T : BMap)
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak) (hex : akExcl req.access_kind = true) :
    uxwIsText T (.ok (.memRead n vasize req)) = false := by
  simp [uxwIsText, uxTextRead, hex]

theorem ukd_mrdxA (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (res : Option (X × UWSt × UOrc)) (w : BitVec (8 * n))
    (hif : akIfetch req.access_kind = false) (hn : n < 2 ^ 64) (hex : akExcl req.access_kind = true)
    (hr : bmRead s.mm req.pa n = some w)
    (h : ukdRun T dirty D orc (UWSt.mk s.pin s.rs s.mm true) (k (.Ok (w, none))) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.memRead n vasize req)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.memRead n vasize req)) k (ukd_isText_excl T req hex)
    (Result.Ok (w, none) : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) _ orc
    (by simp only [runRW, hif, hn, hex, hr, Bool.false_eq_true, ↓reduceIte])

theorem ukd_mrdx (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (res : Option (X × UWSt × UOrc)) (w : BitVec (8 * n))
    (hif : akIfetch req.access_kind = false) (hn : n < 2 ^ 64) (hex : akExcl req.access_kind = true)
    (_hacq : akAcq req.access_kind = false) (hr : bmRead s.mm req.pa n = some w)
    (h : ukdRun T dirty D orc (UWSt.mk s.pin s.rs s.mm true) (k (.Ok (w, none))) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.memRead n vasize req)) k) = res :=
  ukd_mrdxA T dirty X D orc s n vasize req k res w hif hn hex hr h

theorem ukd_mwrA (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X)
    (res : Option (X × UWSt × UOrc)) (w : BitVec (8 * n))
    (hn : n < 2 ^ 64) (hv : req.value = some w) (ho : bmOwned s.mm req.pa n = true)
    (h : ukdRun T dirty D orc (UWSt.mk s.pin s.rs (bmWrite s.mm req.pa n w) false) (k (.Ok (some true))) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.memWrite n vasize req)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.memWrite n vasize req)) k rfl
    (Result.Ok (some true) : Result (Option Bool) Arch.abort) _ orc
    (by simp only [runRW, hn, hv, ho, ↓reduceIte])

theorem ukd_mwr (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X)
    (res : Option (X × UWSt × UOrc)) (w : BitVec (8 * n))
    (hn : n < 2 ^ 64) (hv : req.value = some w) (ho : bmOwned s.mm req.pa n = true)
    (_hex : akExcl req.access_kind = false)
    (h : ukdRun T dirty D orc (UWSt.mk s.pin s.rs (bmWrite s.mm req.pa n w) false) (k (.Ok (some true))) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.memWrite n vasize req)) k) = res :=
  ukd_mwrA T dirty X D orc s n vasize req k res w hn hv ho h

theorem ukd_mwrx (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X)
    (res : Option (X × UWSt × UOrc)) (w : BitVec (8 * n))
    (hn : n < 2 ^ 64) (hv : req.value = some w) (ho : bmOwned s.mm req.pa n = true)
    (_hex : akExcl req.access_kind = true) (_hrv : s.rv = true)
    (h : ukdRun T dirty D orc (UWSt.mk s.pin s.rs (bmWrite s.mm req.pa n w) false) (k (.Ok (some true))) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.memWrite n vasize req)) k) = res :=
  ukd_mwrA T dirty X D orc s n vasize req k res w hn hv ho h

theorem ukd_choose (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (p : Sail.Primitive)
    (k : p.reflect → SailM X) (res : Option (X × UWSt × UOrc))
    (h : ukdRun T dirty D orc.tail s (k ((orc 0).ch p)) = res) :
    ukdRun T dirty D orc s (FreeM.impure (.ok (.choose p)) k) = res := by
  rw [← h]
  exact ukd_node_of T dirty D orc s (.ok (.choose p)) k rfl ((orc 0).ch p) s orc.tail rfl

theorem ukd_silent (T : BMap) (dirty : PAddr → Bool) (X : Type) (D : UFoot) (orc : UOrc) (s : UWSt) (m m' : SailM X)
    (res : Option (X × UWSt × UOrc)) (hdef : ukdRun T dirty D orc s m = ukdRun T dirty D orc s m')
    (h : ukdRun T dirty D orc s m' = res) : ukdRun T dirty D orc s m = res := hdef.trans h

/-- **The map leaf**, in the stepper's sub-fact shape: a plain read, or a
fetch of a clean window, of `n` bytes the map owns answers them. -/
theorem ukd_leaf (T : BMap) (dirty : PAddr → Bool) (D : UFoot) (o : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (hn0 : 0 < n) (hn : n < 2 ^ 64) (hex : akExcl req.access_kind = false) (ho : bmOwned T req.pa n = true)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = false) :
    ukdRun T dirty D o s (ConcurrencyInterfaceV1.sail_mem_read req) =
      some (.Ok ((bmRead T req.pa n).getD 0, none), s, o) := by
  have hk : uxTextRead T req = true := by
    simp only [uxTextRead, hn0, hn, hex, ho, decide_true, Bool.not_false, Bool.and_self]
  obtain ⟨w, hw⟩ := bmRead_of_owned T req.pa n ho
  unfold ukdRun
  rw [uxdw_sail_mem_read_text D T dirty o s req hk w hw hc, hw]
  rfl

/-- **The dirty leaf**: a fetch of a window with a dirty byte answers the
oracle's head choice on the dirty bytes, the map elsewhere. -/
theorem ukd_leafD (T : BMap) (dirty : PAddr → Bool) (D : UFoot) (o : UOrc) (s : UWSt) (n vasize : Nat)
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (hn0 : 0 < n) (hn : n < 2 ^ 64) (hex : akExcl req.access_kind = false) (ho : bmOwned T req.pa n = true)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = true) :
    ukdRun T dirty D o s (ConcurrencyInterfaceV1.sail_mem_read req) =
      some (.Ok (bmMerge dirty req.pa n ((bmRead T req.pa n).getD 0) ((o 0).ch (.bitvector (8 * n))), none),
        s, o.tail) := by
  have hk : uxTextRead T req = true := by
    simp only [uxTextRead, hn0, hn, hex, ho, decide_true, Bool.not_false, Bool.and_self]
  obtain ⟨w, hw⟩ := bmRead_of_owned T req.pa n ho
  unfold ukdRun
  rw [uxdw_sail_mem_read_dirty D T dirty o s req hk w hw hc, hw]
  rfl

/-! ## The tactic -/

namespace UkdWalk
open Lean Meta Elab Tactic

/-- The step lemmas and their twins. -/
def twins : List (Name × Name) :=
  [(``uwk_pure, ``ukd_pure), (``uwk_bind, ``ukd_bind),
   (``uwk_bind_none, ``ukd_bind_none), (``uwk_congr, ``ukd_congr), (``uwk_ite_pos, ``ukd_ite_pos),
   (``uwk_ite_neg, ``ukd_ite_neg), (``uwk_dite_pos, ``ukd_dite_pos), (``uwk_dite_neg, ``ukd_dite_neg),
   (``uwk_error, ``ukd_error), (``uwk_rr, ``ukd_rr), (``uwk_rr_any, ``ukd_rr_any), (``uwk_rw, ``ukd_rw),
   (``uwk_mrdx, ``ukd_mrdx), (``uwk_mrdxA, ``ukd_mrdxA), (``uwk_mwr, ``ukd_mwr), (``uwk_mwrx, ``ukd_mwrx),
   (``uwk_mwrA, ``ukd_mwrA), (``uwk_choose, ``ukd_choose), (``uwk_silent, ``ukd_silent)]

/-- `runRW` ↦ `ukdRun T dirty` and every step lemma ↦ its twin at `T dirty`. -/
def toUkd (T dirty e : Lean.Expr) : Lean.Expr :=
  e.replace fun
    | .const n us =>
      if n == ``runRW then some (mkApp2 (.const ``ukdRun us) T dirty)
      else (twins.lookup n).map fun n' => mkApp2 (.const n' us) T dirty
    | _ => none

/-- `ukdRun T dirty` / `uxdRun D T dirty` ↦ `runRW` (the stand-ins' statements). -/
partial def toRW (e : Lean.Expr) : Lean.Expr :=
  e.replace fun x =>
    let f := x.getAppFn
    let args := x.getAppArgs
    if f.isConstOf ``ukdRun && args.size ≥ 4 then
      -- `@ukdRun T dirty X D rest…`
      some (mkAppN (mkConst ``runRW) (#[args[2]!, args[3]!] ++ (args.extract 4 args.size).map toRW))
    else if f.isConstOf ``uxdRun && args.size ≥ 4 then
      -- `@uxdRun X D T dirty rest…`
      some (mkAppN (mkConst ``runRW) (#[args[0]!, args[1]!] ++ (args.extract 4 args.size).map toRW))
    else none

/-- Walk the `uxdRun` goal's left side: the result and the proof (about
`ukdRun T dirty`). -/
def run (lemmas : Array Syntax.Term) (lhs : Lean.Expr) (bv : Bool) : TacticM (Lean.Expr × Lean.Expr) := do
  let lhs ← instantiateMVars lhs
  let (T, dirty, D) ←
    if lhs.isAppOfArity ``uxdRun 7 then pure (lhs.getAppArgs[2]!, lhs.getAppArgs[3]!, lhs.getAppArgs[1]!)
    else if lhs.isAppOfArity ``ukdRun 7 then pure (lhs.getAppArgs[0]!, lhs.getAppArgs[1]!, lhs.getAppArgs[3]!)
    else throwError "ukd_run: not a walk over a memory with dirty bytes{indentExpr lhs}"
  let mut reals : Array Lean.Expr := #[]
  let mut decls : Array (Name × (Array Lean.Expr → TacticM Lean.Expr)) := #[]
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    if ty.containsFVar ld.fvarId then continue
    if (ty.find? fun e => e.isConstOf ``uxdRun || e.isConstOf ``ukdRun).isSome then
      reals := reals.push ld.toExpr
      let ty' := toRW ty
      decls := decls.push (ld.userName, fun _ => pure ty')
  for (nm, lf) in [(`ukdLeaf, ``ukd_leaf), (`ukdLeafD, ``ukd_leafD)] do
    let leaf := mkApp3 (mkConst lf) T dirty D
    reals := reals.push leaf
    let leafTy := toRW (← inferType leaf)
    decls := decls.push (nm, fun _ => pure leafTy)
  withLocalDeclsD decls fun fakes => do
    let (r, p) ← UWalkRun.run lemmas (toRW lhs) bv
    let p ← instantiateMVars p
    let r ← instantiateMVars r
    let p' := (toUkd T dirty p).replaceFVars fakes reals
    let r' := (toUkd T dirty r).replaceFVars fakes reals
    if (r'.find? fun e => e.isFVar && fakes.contains e).isSome then
      throwError "ukd_run: the result mentions a stand-in"
    return (r', p')

end UkdWalk

syntax (name := ukdRunTac) "ukd_run" ("-bv")? (" [" term,* "]")? : tactic

open Lean Elab Tactic Meta in
/-- `ukd_run [l₁, …]` on `uxdRun D T dirty orc s m = rhs` (or `ukdRun T dirty D …`):
walk `m` (through its reads of `T`), leave `r = rhs` (closed by `rfl` when
possible). -/
@[tactic ukdRunTac] def evalUkdRun : Tactic := fun stx => do
  let bv := stx[1].isNone
  let lemmas : Array Syntax.Term :=
    if stx[2].isNone then #[] else (stx[2][1].getSepArgs.map fun s => ⟨s⟩)
  withMainContext do
    let g ← getMainGoal
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    let some (_, lhs, rhs) := tgt.eq? | throwError "ukd_run: the goal is not an equation{indentExpr tgt}"
    let (r, p) ← UkdWalk.run lemmas lhs bv
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq r rhs)
    g.assign (← mkEqTrans p g')
    let saved ← saveState
    try
      if ← isDefEq r rhs then
        g'.mvarId!.assign (← mkEqRefl r)
        replaceMainGoal []
      else
        restoreState saved
        replaceMainGoal [g'.mvarId!]
    catch _ =>
      restoreState saved
      replaceMainGoal [g'.mvarId!]

end MachCSL
