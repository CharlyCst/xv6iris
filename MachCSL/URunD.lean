/-
MachCSL: **the walker over a memory with DIRTY bytes** (`uxdRun`).

`uxRun D T` (MachCSL/URunX) answers non-exclusive reads of the stamped text
map `T` from `T`.  That is exact only for bytes no store has touched since the
last `fence.i`: the instruction cache is non-coherent, so a fetch of a byte
written since then may return an older value.

`uxdRun D T dirty` is `uxRun D T` with a set of DIRTY bytes (`dirty a = true`):

* a PLAIN read of a window in `T` returns `T` (the data view reads the latest
  store, for clean and dirty bytes alike);
* an instruction FETCH of a window in `T` with no dirty byte returns `T`;
* an instruction fetch of a window with a dirty byte draws a value from the
  oracle (`(orc 0).ch (.bitvector (8 * n))`) and returns it on the dirty
  bytes, `T` on the clean ones (`bmMerge`), one draw per fetch event;
* every other node is `runRW`'s.

Its Iris rule is `MachCSL/URunDSwp`, its stepper `MachCSL/UkdWalk`.
-/
import MachCSL.URunXWalk

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## Dirty windows and merged values -/

/-- Byte `j` of the window at `pa` (a `PAddr` sum, for requests whose address
has type `Arch.pa`). -/
abbrev bAddr (pa : PAddr) (j : Nat) : PAddr := pa + BitVec.ofNat 64 j

/-- The window `[pa, pa + n)` holds a dirty byte. -/
def winDirty (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) : Bool :=
  (List.range n).any fun j => dirty (pa + BitVec.ofNat 64 j)

/-- `0xff` at the dirty bytes of the window, `0` elsewhere. -/
def dirtyMask (dirty : PAddr → Bool) (pa : PAddr) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 =>
    ((if dirty (pa + BitVec.ofNat 64 n) then BitVec.allOnes 8 else 0#8) ++ dirtyMask dirty pa n).cast
      (by omega)

/-- The bytes of `x` at the dirty bytes of the window, those of `w` elsewhere. -/
def bmMerge (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (w x : BitVec (8 * n)) : BitVec (8 * n) :=
  (w &&& ~~~(dirtyMask dirty pa n)) ||| (x &&& dirtyMask dirty pa n)

theorem winDirty_false {dirty : PAddr → Bool} {pa : PAddr} {n : Nat} (h : winDirty dirty pa n = false)
    (j : Nat) (hj : j < n) : dirty (pa + BitVec.ofNat 64 j) = false := by
  unfold winDirty at h
  rw [List.any_eq_false] at h
  simpa using h j (List.mem_range.2 hj)

theorem nthByte_dirtyMask (dirty : PAddr → Bool) (pa : PAddr) :
    ∀ (n j : Nat), j < n →
      nthByte (dirtyMask dirty pa n) j = if dirty (pa + BitVec.ofNat 64 j) then BitVec.allOnes 8 else 0#8
  | 0, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj => by
    unfold dirtyMask
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [bm_nthByte_cast_append_lt _ _ _ _ hj]
      exact nthByte_dirtyMask dirty pa n j hj
    · rw [bm_nthByte_cast_append_eq]

theorem nthByte_and {n : Nat} (a b : BitVec (8 * n)) (j : Nat) :
    nthByte (a &&& b) j = nthByte a j &&& nthByte b j := by
  unfold nthByte
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem nthByte_or {n : Nat} (a b : BitVec (8 * n)) (j : Nat) :
    nthByte (a ||| b) j = nthByte a j ||| nthByte b j := by
  unfold nthByte
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem nthByte_not {n : Nat} (a : BitVec (8 * n)) (j : Nat) (hj : j < n) :
    nthByte (~~~a) j = ~~~(nthByte a j) := by
  unfold nthByte
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : 8 * j + i < 8 * n := by omega
  simp [hi, this]

/-- A merged byte: `x`'s if dirty, else `w`'s. -/
theorem nthByte_bmMerge (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (w x : BitVec (8 * n)) (j : Nat)
    (hj : j < n) :
    nthByte (bmMerge dirty pa n w x) j =
      if dirty (pa + BitVec.ofNat 64 j) then nthByte x j else nthByte w j := by
  unfold bmMerge
  rw [nthByte_or, nthByte_and, nthByte_and, nthByte_not _ _ hj, nthByte_dirtyMask dirty pa n j hj]
  split <;> bv_decide

/-- A value agreeing with `w` on the clean bytes is its own merge. -/
theorem bmMerge_eq (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (w x : BitVec (8 * n))
    (h : ∀ j, j < n → dirty (pa + BitVec.ofNat 64 j) = false → nthByte x j = nthByte w j) :
    bmMerge dirty pa n w x = x := by
  apply bv_eq_of_bytes
  intro j hj
  rw [nthByte_bmMerge dirty pa n w x j hj]
  cases hd : dirty (pa + BitVec.ofNat 64 j)
  · exact (h j hj hd).symm
  · rfl

/-- A merge agrees with `w` on the clean bytes. -/
theorem bmMerge_clean (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (w x : BitVec (8 * n)) (j : Nat)
    (hj : j < n) (hc : dirty (pa + BitVec.ofNat 64 j) = false) :
    nthByte (bmMerge dirty pa n w x) j = nthByte w j := by
  rw [nthByte_bmMerge dirty pa n w x j hj, hc]
  rfl

/-! ## The walker -/

/-- **The walker over a memory with dirty bytes.** -/
def uxdRun {X : Type} (D : UFoot) (T : BMap) (dirty : PAddr → Bool) :
    UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)
  | orc, s, .pure x => some (x, s, orc)
  | orc, s, .impure (.ok (.memRead n vasize req)) k =>
    if uxTextRead T req then
      match bmRead T req.pa n with
      | some w =>
        if akIfetch req.access_kind && winDirty dirty req.pa n then
          uxdRun D T dirty orc.tail s
            (k (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
        else uxdRun D T dirty orc s (k (.Ok (w, none)))
      | none => none
    else
      (runRW D orc s (FreeM.impure (.ok (.memRead n vasize req)) FreeM.pure)).bind
        fun r => uxdRun D T dirty r.2.2 r.2.1 (k r.1)
  | orc, s, .impure c k =>
    (runRW D orc s (FreeM.impure c FreeM.pure)).bind fun r => uxdRun D T dirty r.2.2 r.2.1 (k r.1)

section walker
variable (D : UFoot) (T : BMap) (dirty : PAddr → Bool)

/-- A node the map does not answer: a one-node `runRW` walk, then the
continuation. -/
theorem uxdw_node {X : Type} (orc : UOrc) (s : UWSt) (c : Eff RegisterType exception)
    (k : ArchSem.Effect.ret c → SailM X) (hc : uxwIsText T c = false) :
    uxdRun D T dirty orc s (FreeM.impure c k) =
      (runRW D orc s (FreeM.impure c FreeM.pure)).bind fun r => uxdRun D T dirty r.2.2 r.2.1 (k r.1) := by
  rcases c with e | op
  · simp only [uxdRun]
  · cases op with
    | memRead n vasize req =>
      simp only [uxwIsText] at hc
      simp only [uxdRun, hc, Bool.false_eq_true, if_false]
    | _ => simp only [uxdRun]

/-- A read the map answers. -/
theorem uxdw_text {X : Type} (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (hk : uxTextRead T req = true) :
    uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) k) =
      match bmRead T req.pa n with
      | some w =>
        if akIfetch req.access_kind && winDirty dirty req.pa n then
          uxdRun D T dirty orc.tail s
            (k (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none)))
        else uxdRun D T dirty orc s (k (.Ok (w, none)))
      | none => none := by
  simp only [uxdRun, hk, if_true]

/-- **A read answered from the map**: a plain read, or a fetch of a clean
window. -/
theorem uxdw_text_some {X : Type} (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (hk : uxTextRead T req = true) (w : BitVec (8 * n)) (hw : bmRead T req.pa n = some w)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = false) :
    uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) k) =
      uxdRun D T dirty orc s (k (.Ok (w, none))) := by
  rw [uxdw_text D T dirty orc s req k hk, hw]
  simp only [hc, Bool.false_eq_true, if_false]

/-- **A fetch of a dirty window**: the oracle's value on the dirty bytes. -/
theorem uxdw_text_dirty {X : Type} (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (hk : uxTextRead T req = true) (w : BitVec (8 * n)) (hw : bmRead T req.pa n = some w)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = true) :
    uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) k) =
      uxdRun D T dirty orc.tail s
        (k (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none))) := by
  rw [uxdw_text D T dirty orc s req k hk, hw]
  simp only [hc, if_true]

theorem uxdw_text_none {X : Type} (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → SailM X)
    (hk : uxTextRead T req = true) (hw : bmRead T req.pa n = none) :
    uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) k) = none := by
  rw [uxdw_text D T dirty orc s req k hk, hw]

/-- The leaf: a read answered from the map. -/
theorem uxdw_sail_mem_read_text (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (hk : uxTextRead T req = true) (w : BitVec (8 * n)) (hw : bmRead T req.pa n = some w)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = false) :
    uxdRun D T dirty orc s (ConcurrencyInterfaceV1.sail_mem_read req) = some (.Ok (w, none), s, orc) := by
  show uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) FreeM.pure) = _
  rw [uxdw_text_some D T dirty orc s req _ hk w hw hc]
  rfl

/-- The leaf: a fetch of a dirty window. -/
theorem uxdw_sail_mem_read_dirty (orc : UOrc) (s : UWSt) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (hk : uxTextRead T req = true) (w : BitVec (8 * n)) (hw : bmRead T req.pa n = some w)
    (hc : (akIfetch req.access_kind && winDirty dirty req.pa n) = true) :
    uxdRun D T dirty orc s (ConcurrencyInterfaceV1.sail_mem_read req) =
      some (.Ok (bmMerge dirty req.pa n w ((orc 0).ch (.bitvector (8 * n))), none), s, orc.tail) := by
  show uxdRun D T dirty orc s (FreeM.impure (.ok (.memRead n vasize req)) FreeM.pure) = _
  rw [uxdw_text_dirty D T dirty orc s req _ hk w hw hc]
  rfl

/-- **A `runRW` walk is a `uxdRun` walk** (the walker's map missing `T`). -/
theorem uxdw_of_runRW' {X : Type} (m : SailM X) :
    ∀ (orc : UOrc) (s : UWSt) (r : X × UWSt × UOrc), UxwDisj T s →
      runRW D orc s m = some r → uxdRun D T dirty orc s m = some r := by
  induction m with
  | pure x => intro orc s r _ h; exact h
  | impure c k ih =>
    intro orc s r hd h
    cases hc : uxwIsText T c with
    | true =>
      obtain ⟨n, vasize, req, rfl, hk⟩ := uxwIsText_true T hc
      rw [uxw_runRW_text_none D T orc s hd req k hk] at h
      cases h
    | false =>
      rw [uxdw_node D T dirty orc s c k hc]
      rw [MachCSL.uft_runRW_node D orc s c k] at h
      revert h
      cases hr : runRW D orc s (FreeM.impure c FreeM.pure) with
      | none => intro h; simp at h
      | some p =>
        obtain ⟨v, s', o'⟩ := p
        exact ih v o' s' r (uxwDisj_runRW D T _ orc s v s' o' hr hd)

/-- **A `runRW` walk is a `uxdRun` walk.** -/
theorem uxdw_of_runRW {X : Type} (m : SailM X) (orc : UOrc) (s : UWSt) (r : X × UWSt × UOrc)
    (hdisj : ∀ a, (T a).isSome = true → (s.mm a).isSome = false) :
    runRW D orc s m = some r → uxdRun D T dirty orc s m = some r :=
  uxdw_of_runRW' D T dirty m orc s r hdisj

/-- **The bind law.** -/
theorem uxdw_bind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ (orc : UOrc) (s : UWSt), uxdRun D T dirty orc s (m >>= f) =
      (uxdRun D T dirty orc s m).bind (fun r => uxdRun D T dirty r.2.2 r.2.1 (f r.1)) := by
  induction m with
  | pure x => intro orc s; rfl
  | impure c k ih =>
    intro orc s
    have e : (FreeM.impure c k : SailM X) >>= f = FreeM.impure c (fun v => k v >>= f) := rfl
    rw [e]
    cases hc : uxwIsText T c with
    | true =>
      obtain ⟨n, vasize, req, rfl, hk⟩ := uxwIsText_true T hc
      rw [uxdw_text D T dirty orc s req _ hk, uxdw_text D T dirty orc s req _ hk]
      cases bmRead T req.pa n with
      | some w =>
        dsimp only
        split
        · exact ih _ _ _
        · exact ih _ _ _
      | none => rfl
    | false =>
      rw [uxdw_node D T dirty orc s c _ hc, uxdw_node D T dirty orc s c _ hc]
      cases runRW D orc s (FreeM.impure c FreeM.pure) with
      | none => rfl
      | some p => obtain ⟨v, s', o'⟩ := p; exact ih v o' s'

theorem uxdw_bind_some {X Y : Type} (m : SailM X) (f : X → SailM Y) (orc orc' : UOrc) (s s' : UWSt)
    (x : X) (h : uxdRun D T dirty orc s m = some (x, s', orc')) :
    uxdRun D T dirty orc s (m >>= f) = uxdRun D T dirty orc' s' (f x) := by
  rw [uxdw_bind, h]; rfl

theorem uxdw_bind_none {X Y : Type} (m : SailM X) (f : X → SailM Y) (orc : UOrc) (s : UWSt)
    (h : uxdRun D T dirty orc s m = none) : uxdRun D T dirty orc s (m >>= f) = none := by
  rw [uxdw_bind, h]; rfl

/-- A known `runRW` sub-walk (from a state missing `T`), then the
continuation. -/
theorem uxdw_bind_runRW {X Y : Type} (m : SailM X) (f : X → SailM Y) (orc orc' : UOrc) (s s' : UWSt)
    (x : X) (hd : UxwDisj T s) (h : runRW D orc s m = some (x, s', orc')) :
    uxdRun D T dirty orc s (m >>= f) = uxdRun D T dirty orc' s' (f x) :=
  uxdw_bind_some D T dirty m f orc orc' s s' x (uxdw_of_runRW' D T dirty m orc s _ hd h)

end walker

end MachCSL
