/-
MachCSL: **per-function relational lemmas** for the native walker (`RelRun`): the Sail functions
an S/U step runs that read registers whose two values may differ (Miralis's payload phase:
`mstatus` outside `MPP`/`MIE`, `mie`, `mip`, `mideleg`; design note 09 §11). Each lemma is stated
for an arbitrary register relation `Rv`, under hypotheses on what `Rv` preserves (e.g. the `SXL`
and `UXL` fields of `mstatus`), so it is independent of the client's coupling and of the trust
boundary's encoding.
-/
import MachCSL.UNativeRel

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

section fun_rel
variable {D : UFoot} {B : Privilege → Bool} {Rv : RegRel}

/-! ## §1 Generic tools -/

/-- A computation that fails at its first node runs nowhere: relational to anything. -/
theorem relRun2_fail {X : Type} (e : Error exception) (k : _ → SailM X) (m2 : SailM X) :
    RelRun2 D B Rv (FreeM.impure (.error e) k) m2 := by
  intro orc s1 s2 res1 _ h
  rw [uxnw_node D B orc s1 _ k rfl] at h
  simp [runRW] at h

/-- `internal_error` runs nowhere. -/
theorem relRun_internal_error {X : Type} (f : String) (l : Int) (m : String) :
    RelRun D B Rv (internal_error f l m : SailM X) :=
  relRun2_fail _ _ _

/-- Two equal pure returns, through a `match` on a closed value: relational. -/
theorem relRun2_pure_eq {X : Type} {x y : X} (h : x = y) :
    RelRun2 D B Rv (FreeM.pure x) (FreeM.pure y) := by
  subst h; exact relRun2_pure x

/-- A heterogeneous pair of *equal* computations whose bodies are relational. -/
theorem relRun2_of_eq {X : Type} {m1 m2 : SailM X} (he : m1 = m2) (h : RelRun D B Rv m1) :
    RelRun2 D B Rv m1 m2 := by
  subst he; exact h

/-- **A read whose continuation depends only on a projection the relation preserves.** -/
theorem relRun2_regRead_proj {X Y : Type} (r : Register) (hd : D.Dr r = true)
    (hr : r ≠ .cur_privilege) (π : RegisterType r → Y)
    (hπ : ∀ v w, Rv r v w → π v = π w) (k : Y → SailM X) (hk : ∀ y, RelRun D B Rv (k y)) :
    RelRun2 D B Rv (FreeM.impure (.ok (.regRead r)) (fun v => k (π v)))
      (FreeM.impure (.ok (.regRead r)) (fun v => k (π v))) :=
  relRun2_regRead r hd hr _ _ fun v w hvw => by
    rw [hπ v w hvw]; exact hk (π w)

/-! ## §2 `architecture` -/

theorem relRun_architecture_bits_backwards (x : BitVec 2) :
    RelRun D B Rv (architecture_bits_backwards x) := by
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
    RelRun D B Rv (architecture p) := by
  rcases hp with rfl | rfl
  · exact relRun2_regRead_proj .mstatus hdms (by decide) _get_Mstatus_SXL hsxl architecture_bits_backwards
      (fun y => relRun_architecture_bits_backwards y)
  · exact relRun2_regRead_proj .mstatus hdms (by decide) _get_Mstatus_UXL huxl
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

end fun_rel

end MachCSL
