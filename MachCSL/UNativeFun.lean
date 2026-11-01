/-
MachCSL: **per-function relational lemmas** for the native walker (`RelRun`): the Sail functions
an S/U step runs that read registers whose two values may differ (Miralis's payload phase:
`mstatus` outside `MPP`/`MIE`, `mie`, `mip`, `mideleg`; design note 09 §11). Each lemma is stated
for an arbitrary register relation `Rv`, under hypotheses on what `Rv` preserves (e.g. the `SXL`
and `UXL` fields of `mstatus`), so it is independent of the client's coupling and of the trust
boundary's encoding.
-/
import MachCSL.UNativeRel
import MachCSL.DecodeBridge
import MachCSL.UCycle

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSimpArgs false

/-- The registers of `L` are readable by `D` and related only to themselves. -/
def EqRegs (D : UFoot) (Rv : RegRel) (L : List Register) : Prop :=
  ∀ r ∈ L, D.Dr r = true ∧ ∀ v w, Rv r v w → v = w

/-- **One step of a relational symbolic walk**: a return, a read of a register of `hE`'s list, a
plain node or a memory access, on both sides. -/
macro "rel_step " hE:ident : tactic => `(tactic| first
  | exact relRun2_pure _
  | (apply relRun2_regRead_eq _ (($hE _ (by decide)).1) (($hE _ (by decide)).2); intro _)
  | (apply relRun2_plain _ rfl; intro _)
  | (apply relRun2_memRead; intro _)
  | (apply relRun2_memWrite; intro _))

/-- **A relational symbolic walk**: `rel_step` as long as it applies. -/
macro "rel_walk " hE:ident : tactic => `(tactic| repeat rel_step $hE)

/-- **One step of a relational symbolic walk with writes**: `rel_step`, a write of the same value on
both sides (a register of `hW`'s list), and the normalization of returns. -/
macro "rel_stepW " hE:ident hW:ident hrefl:ident hG:ident : tactic => `(tactic| first
  | exact relRun2_pure _
  | (apply relRun2_regRead_eq _ (($hE _ (by decide)).1) (($hE _ (by decide)).2); intro _)
  | (apply relRun2_plain _ rfl; intro _)
  | (apply relRun2_memRead; intro _)
  | (apply relRun2_memWrite; intro _)
  | (apply relRun2_regWrite $hG _ ($hW _ (by decide)) _ _ ($hrefl _ _))
  | (dsimp only [FreeM.bind])
  | (simp only [pure_bind]))

/-- The relation on `mstatus` that S- and U-mode code cannot observe: the two values agree outside
`MPP` (bits 11–12) and `MIE` (bit 3), and `MPRV` is clear (so `MPP` is not consulted by address
translation). -/
def msRelSU (v w : BitVec 64) : Prop :=
  v &&& ~~~0x1808#64 = w &&& ~~~0x1808#64 ∧ BitVec.extractLsb' 17 1 v = 0#1

section fun_rel
variable {D : UFoot} {B : Privilege → Bool} {Rv : RegRel} {G : RegFile → RegFile → Prop}

/-! ## §1 Generic tools -/

/-- A computation that fails at its first node runs nowhere: relational to anything. -/
theorem relRun2_fail {X : Type} (e : Error exception) (k : _ → SailM X) (m2 : SailM X) :
    RelRun2 D B Rv G (FreeM.impure (.error e) k) m2 := by
  intro orc s1 s2 res1 _ h
  rw [uxnw_node D B orc s1 _ k rfl] at h
  simp [runRW] at h

/-- `internal_error` runs nowhere. -/
theorem relRun_internal_error {X : Type} (f : String) (l : Int) (m : String) :
    RelRun D B Rv G (internal_error f l m : SailM X) :=
  relRun2_fail _ _ _

/-- Two equal pure returns, through a `match` on a closed value: relational. -/
theorem relRun2_pure_eq {X : Type} {x y : X} (h : x = y) :
    RelRun2 D B Rv G (FreeM.pure x) (FreeM.pure y) := by
  subst h; exact relRun2_pure x

/-- A heterogeneous pair of *equal* computations whose bodies are relational. -/
theorem relRun2_of_eq {X : Type} {m1 m2 : SailM X} (he : m1 = m2) (h : RelRun D B Rv G m1) :
    RelRun2 D B Rv G m1 m2 := by
  subst he; exact h

/-- **A read whose continuation depends only on a projection the relation preserves.** -/
theorem relRun2_regRead_proj {X Y : Type} (r : Register) (hd : D.Dr r = true)
    (π : RegisterType r → Y)
    (hπ : ∀ v w, Rv r v w → π v = π w) (k : Y → SailM X) (hk : ∀ y, RelRun D B Rv G (k y)) :
    RelRun2 D B Rv G (FreeM.impure (.ok (.regRead r)) (fun v => k (π v)))
      (FreeM.impure (.ok (.regRead r)) (fun v => k (π v))) :=
  relRun2_regRead r hd _ _ fun v w hvw => by
    rw [hπ v w hvw]; exact hk (π w)

/-- **A read-only computation the closed reference map `dref` answers** walks to its value, the
state unchanged (the native-walker version of `runRW_of_runRead`). -/
theorem uxnRun_of_runRead (dref : (r : Register) → Option (RegisterType r)) {X : Type}
    (orc : UOrc) (s : NSt) (hd : ∀ r v, dref r = some v → D.Dr r = true ∧ s.u.file r = v) :
    ∀ (m : SailM X) (x : X) (b : Bool), runRead dref m = some (x, b) →
      uxnRun D B orc s m = some (.done x s orc) := by
  intro m
  induction m with
  | pure y => intro x b h; simp only [runRead, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | impure call k ih =>
    intro x b h
    cases call with
    | error e => simp [runRead] at h
    | ok o =>
      have step : ∀ (c : Eff RegisterType exception) (kk : ArchSem.Effect.ret c → SailM X) (v : _),
          nOwn c = false → runRW D orc s.u (FreeM.impure c FreeM.pure) = some (v, s.u, orc) →
          uxnRun D B orc s (FreeM.impure c kk) = uxnRun D B orc s (kk v) := by
        intro c kk v hc hr
        rw [uxnw_node D B orc s c kk hc, hr]
        rfl
      cases o with
      | regRead r =>
        simp only [runRead] at h
        cases hr : dref r with
        | none => rw [hr] at h; cases h
        | some v =>
          rw [hr] at h
          dsimp only at h
          obtain ⟨hdr, hf⟩ := hd r v hr
          rw [step _ k v rfl (by rw [runRW_regRead_dr D orc s.u r FreeM.pure hdr, hf]; rfl)]
          cases hk : runRead dref (k v) with
          | none => rw [hk] at h; cases h
          | some p =>
            rw [hk] at h
            simp only [Option.map_some, Option.some.injEq] at h
            obtain ⟨x', b'⟩ := p
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact ih v x' b' hk
      | barrier _ | cacheOp _ | tlbi _ | translationStart _ | translationEnd _ | takeException _
      | returnException _ | cycleCount | message _ =>
        simp only [runRead] at h
        cases hk : runRead dref (k ()) with
        | none => rw [hk] at h; cases h
        | some p =>
          rw [hk] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨x', b'⟩ := p
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rw [step _ k () rfl rfl]
          exact ih () x' b' hk
      | getCycleCount =>
        simp only [runRead] at h
        cases hk : runRead dref (k (0 : Nat)) with
        | none => rw [hk] at h; cases h
        | some p =>
          rw [hk] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨x', b'⟩ := p
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rw [step _ k (0 : Nat) rfl rfl]
          exact ih (0 : Nat) x' b' hk
      | _ => simp [runRead] at h

/-- **A read-only stretch with a closed answer on both sides** (registers fixed by the relation to
`dref`'s values): both walks pass it with the same value, the states unchanged. -/
theorem relRun2_runRead_bind (dref : (r : Register) → Option (RegisterType r))
    (hdref : ∀ r v, dref r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    {X Y : Type} (m : SailM X) (x : X) (b : Bool) (hm : runRead dref m = some (x, b))
    (k1 k2 : X → SailM Y) (hk : RelRun2 D B Rv G (k1 x) (k2 x)) :
    RelRun2 D B Rv G (m >>= k1) (m >>= k2) := by
  intro orc s1 s2 res1 hrel h
  have hd1 : ∀ r v, dref r = some v → D.Dr r = true ∧ s1.u.file r = v := fun r v hr =>
    ⟨(hdref r v hr).1, ((hdref r v hr).2 _ _ (hrel.file r)).1⟩
  have hd2 : ∀ r v, dref r = some v → D.Dr r = true ∧ s2.u.file r = v := fun r v hr =>
    ⟨(hdref r v hr).1, ((hdref r v hr).2 _ _ (hrel.file r)).2⟩
  rw [uxnRun_bind, uxnRun_of_runRead dref orc s1 hd1 m x b hm] at h
  rw [uxnRun_bind, uxnRun_of_runRead dref orc s2 hd2 m x b hm]
  exact hk orc s1 s2 res1 hrel h

/-- The reference map that answers every register from the file `f`. -/
def fileRef (f : RegFile) : (r : Register) → Option (RegisterType r) := fun r => some (f r)

/-- **A read-only stretch whose value the global relation fixes** (e.g. a PMP check, whose result
two related PMP configurations agree on): both walks pass it with the same value, the states
unchanged. `val f` is the stretch's value on the file `f`. -/
theorem relRun2_readOnly_bind (hDall : ∀ r, D.Dr r = true) {X Y : Type} (m : SailM X)
    (val : RegFile → X) (hro : ∀ f, ∃ b, runRead (fileRef f) m = some (val f, b))
    (hval : ∀ f g, G f g → val f = val g)
    (k1 k2 : X → SailM Y) (hk : ∀ x, RelRun2 D B Rv G (k1 x) (k2 x)) :
    RelRun2 D B Rv G (m >>= k1) (m >>= k2) := by
  intro orc s1 s2 res1 hrel h
  have hd : ∀ (s : NSt) r v, fileRef s.u.file r = some v → D.Dr r = true ∧ s.u.file r = v :=
    fun s r v hr => ⟨hDall r, (Option.some.inj hr)⟩
  obtain ⟨b1, h1⟩ := hro s1.u.file
  obtain ⟨b2, h2⟩ := hro s2.u.file
  rw [uxnRun_bind, uxnRun_of_runRead (fileRef s1.u.file) orc s1 (hd s1) m _ b1 h1] at h
  rw [uxnRun_bind, uxnRun_of_runRead (fileRef s2.u.file) orc s2 (hd s2) m _ b2 h2]
  rw [← hval _ _ hrel.glob]
  exact hk _ orc s1 s2 res1 hrel h

/-! ## §2 `architecture` -/

theorem relRun_architecture_bits_backwards (x : BitVec 2) :
    RelRun D B Rv G (architecture_bits_backwards x) := by
  unfold architecture_bits_backwards
  split
  · exact relRun_pure _
  · exact relRun_pure _
  · exact relRun_pure _
  · exact relRun_internal_error _ _ _

/-- **`architecture` at S or U**: reads `mstatus.SXL`/`UXL`, which the relation preserves. -/
theorem relRun_architecture_SU (hdms : D.Dr .mstatus = true)
    (hsxl : ∀ v w, Rv .mstatus v w → _get_Mstatus_SXL v = _get_Mstatus_SXL w)
    (huxl : ∀ v w, Rv .mstatus v w → _get_Mstatus_UXL v = _get_Mstatus_UXL w)
    (p : Privilege) (hp : p = .Supervisor ∨ p = .User) :
    RelRun D B Rv G (architecture p) := by
  rcases hp with rfl | rfl
  · exact relRun2_regRead_proj .mstatus hdms _get_Mstatus_SXL hsxl architecture_bits_backwards
      (fun y => relRun_architecture_bits_backwards y)
  · exact relRun2_regRead_proj .mstatus hdms _get_Mstatus_UXL huxl
      architecture_bits_backwards (fun y => relRun_architecture_bits_backwards y)

/-! ## §3 `effectivePrivilege` (used by every translation) -/

/-- With `MPRV = 0`, the effective privilege is the current one: `MPP` is not consulted. In
Miralis's payload phase `MPRV = 0` on both sides (an `xRET` to S/U clears it), which is why the
physical/virtual difference in `MPP` never reaches address translation. -/
theorem effectivePrivilege_noMPRV (acc : MemoryAccessType mem_payload) (m : BitVec 64) (p : Privilege)
    (h : _get_Mstatus_MPRV m = 0#1) : effectivePrivilege acc m p = pure p := by
  unfold effectivePrivilege
  have : ((bne acc (MemoryAccessType.InstructionFetch ())) && (_get_Mstatus_MPRV m == 1#1)) = false := by
    rw [h]; simp
  rw [this]
  rfl

/-- So `effectivePrivilege` gives the same program on two `mstatus` values with `MPRV = 0`. -/
theorem effectivePrivilege_rel (acc : MemoryAccessType mem_payload) (m1 m2 : BitVec 64) (p : Privilege)
    (h1 : _get_Mstatus_MPRV m1 = 0#1) (h2 : _get_Mstatus_MPRV m2 = 0#1) :
    effectivePrivilege acc m1 p = effectivePrivilege acc m2 p := by
  rw [effectivePrivilege_noMPRV acc m1 p h1, effectivePrivilege_noMPRV acc m2 p h2]

/-! ## §4 Trap bookkeeping at S -/

/-- **`track_trap` at S**: its `mstatus` read only feeds a logging callback. -/
theorem relRun_track_trap_S (hdms : D.Dr .mstatus = true)
    (hE : EqRegs D Rv [.scause, .stval, .sepc]) (b : Bool) (c : BitVec 6) :
    RelRun D B Rv G (track_trap .Supervisor b c) := by
  unfold track_trap
  apply relRun2_regRead .mstatus hdms
  intro v w _
  simp only [long_csr_write_callback, csr_name_write_callback, csr_full_write_callback, FreeM.bind]
  rel_walk hE

/-- **Trap delivery to S** (`trap_handler .Supervisor`): relational when `mstatus` is related by
`msRelSU` (the two values may differ in `MPP`/`MIE`): the S-mode trap only reads and rewrites
`SIE`/`SPIE`/`SPP` and keeps the other bits. -/
theorem relRun_trap_handler_S (hrefl : ∀ r v, Rv r v v) (hG : GStable D Rv G) (hpriv : ∀ v w, Rv .cur_privilege v w → v = w)
    (hE : EqRegs D Rv [.scause, .stval, .sepc, .stvec, .cur_privilege, .menvcfg])
    (hW : ∀ r ∈ [Register.scause, .stval, .sepc, .mstatus], D.Dw r = true)
    (hdms : D.Dr .mstatus = true)
    (hmisa : ∀ r v, ucDrefMisa r = some v → D.Dr r = true ∧ ∀ a b, Rv r a b → a = v ∧ b = v)
    (hms : ∀ v w, Rv .mstatus v w ↔ msRelSU v w)
    (c : TrapCause) (pc : BitVec 64) (info : Option (BitVec 64)) (ext : Option Unit) :
    RelRun D B Rv G (trap_handler .Supervisor c pc info ext) := by
  have hE3 : EqRegs D Rv [.scause, .stval, .sepc] := fun r hr => hE r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  unfold trap_handler
  have hz : hartSupports extension.Ext_Zicfilp = false := by decide
  simp only [get_config_print_exception, get_config_print_interrupt, Bool.or_false, Bool.false_eq_true, if_false, hz]
  apply relRun2_runRead_bind ucDrefMisa hmisa _ true true uc_runRead_S
  simp only [assert, if_true]
  repeat rel_stepW hE hW hrefl hG
  apply relRun2_regRead .mstatus hdms; intro a1 b1 h1
  apply relRun2_regRead .mstatus hdms; intro a2 b2 h2
  apply relRun2_regWrite hG _ (hW _ (by decide)) _ _ ?hr1
  case hr1 =>
    rw [hms] at h1 h2 ⊢
    simp only [msRelSU, BitVec.updateSubrange, BitVec.updateSubrange', _get_Mstatus_SIE, Sail.BitVec.extractLsb] at *
    bv_decide
  repeat rel_stepW hE hW hrefl hG
  apply relRun2_regRead .mstatus hdms; intro a3 b3 h3
  apply relRun2_regWrite hG _ (hW _ (by decide)) _ _ ?hr2
  case hr2 =>
    rw [hms] at h3 ⊢
    simp only [msRelSU, BitVec.updateSubrange, BitVec.updateSubrange'] at *
    bv_decide
  repeat rel_stepW hE hW hrefl hG
  apply relRun2_regRead .mstatus hdms; intro a4 b4 h4
  repeat rel_stepW hE hW hrefl hG
  rename_i p
  cases p
  all_goals first
    | (apply relRun2_fail; done)
    | skip
  all_goals (repeat rel_stepW hE hW hrefl hG)
  all_goals
    apply relRun2_regWrite hG _ (hW _ (by decide)) _ _ ?hr3
    case hr3 =>
      rw [hms] at h4 ⊢
      simp only [msRelSU, BitVec.updateSubrange, BitVec.updateSubrange'] at *
      bv_decide
    repeat rel_stepW hE hW hrefl hG
  all_goals
    apply relRun2_priv hrefl hG hpriv _ _ _ ?_ rfl
    apply relRun2_bind (relRun_track_trap_S hdms hE3 _ _)
    intro _
    repeat rel_stepW hE hW hrefl hG
    split
    all_goals
      try (rename_i hh; simp only [hh])
      first | exact relRun2_pure _ | (apply relRun2_fail)

end fun_rel

end MachCSL
