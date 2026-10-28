/-
MachCSL: **the misaligned physical access, with its VALUE** (additive to
`UMemMisPhysR`/`UMemMisPhysW`, whose values are existential).

`checked_mem_read`/`checked_mem_write` split a data access into `N` chunks of
`b` bytes (`umm_split_misaligned_plan`) and run them in a loop.  Here the loop
invariant tracks the bytes: after `k` chunks the read accumulator holds the
low `k * b` bytes of the window's value (`bmRead`), and the written map holds
the low `k * b` bytes of the stored value over the old map (`umxWin`).  So a
misaligned (or aligned) access in owned RAM reads exactly `bmRead` and writes
exactly `bmWrite`, as an aligned one does (`uma_read_ram_plain`/
`uma_write_ram_plain`).  The privilege is a parameter: the per-chunk PMP/MMIO
facts are hypotheses, as in `UMemMisPhysR`/`UMemMisPhysW`.
-/
import MachCSL.UMemMisPhysR
import MachCSL.UMemMisPhysW

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## §1 Byte windows -/

/-- Each byte of a read window is the matching byte of the value read. -/
theorem umx_bmRead_bytes (mm : BMap) (pa : PAddr) :
    ∀ (n : Nat) (v : BitVec (8 * n)), bmRead mm pa n = some v →
      ∀ j, j < n → mm (pa + BitVec.ofNat 64 j) = some (v.extractLsb' (8 * j) 8)
  | 0, _, _, j, hj => absurd hj (by omega)
  | n + 1, v, h, j, hj => by
    unfold bmRead at h
    split at h
    · rename_i w b hw hb
      simp only [Option.some.injEq] at h
      subst h
      by_cases e : j = n
      · subst e
        rw [hb]; congr 1
        ext i hi
        simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append]
        rw [if_neg (by omega)]
        simp only [BitVec.getLsbD_eq_getElem (show 8 * j + i - 8 * j < 8 by omega)]
        congr 1; omega
      · rw [umx_bmRead_bytes mm pa n w hw j (by omega)]; congr 1
        ext i hi
        simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append]
        rw [if_pos (by omega)]
    · simp at h

/-- A window whose every byte is the matching byte of `v` reads `v`. -/
theorem umx_bmRead_of_bytes (mm : BMap) (pa : PAddr) :
    ∀ (n : Nat) (v : BitVec (8 * n)),
      (∀ j, j < n → mm (pa + BitVec.ofNat 64 j) = some (v.extractLsb' (8 * j) 8)) → bmRead mm pa n = some v
  | 0, v, _ => by
    unfold bmRead; congr 1; exact BitVec.eq_of_toNat_eq (by have := v.isLt; simp at this ⊢; omega)
  | n + 1, v, h => by
    unfold bmRead
    rw [umx_bmRead_of_bytes mm pa n (v.extractLsb' 0 (8 * n)) (fun j hj => by
      rw [h j (by omega)]; congr 1; ext i hi
      simp only [BitVec.getElem_extractLsb']
      have : 8 * j + i < 8 * n := by omega
      simp [this]), h n (by omega)]
    simp only [Option.some.injEq]
    ext i hi
    simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · simp only [Nat.zero_add]
      rename_i h1
      simp [BitVec.getLsbD_eq_getElem hi]
    · rename_i h1
      rw [show 8 * n + (i - 8 * n) = i by omega, BitVec.getLsbD_eq_getElem hi]

/-- A sub-window of a read window reads the matching slice. -/
theorem umx_bmRead_sub (mm : BMap) (pa : PAddr) (W : Nat) (v : BitVec (8 * W)) (h : bmRead mm pa W = some v)
    (i c : Nat) (hic : i + c ≤ W) :
    bmRead mm (pa + BitVec.ofNat 64 i) c = some (v.extractLsb' (8 * i) (8 * c)) := by
  apply umx_bmRead_of_bytes
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, umx_bmRead_bytes mm pa W v h (i + j) (by omega)]
  congr 1; ext t ht
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  have : 8 * j + t < 8 * c := by omega
  simp only [this, decide_true, Bool.true_and]; congr 1; omega

/-! ## §2 A walker with `runRW`'s monad laws

The read side is stated for any walker with `runRW`'s `pure`/`bind` laws
(`UmxRun`): `runRW` itself, and `uxdRun` (a memory with dirty bytes, whose
plain reads are answered from its map). -/

/-- A walker with the monad laws of `runRW`. -/
structure UmxRun (run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)) : Prop where
  pure : ∀ {X : Type} (x : X) (orc : UOrc) (s : UWSt), run orc s (pure x) = some (x, s, orc)
  bind : ∀ {X Y : Type} (m : SailM X) (f : X → SailM Y) (orc : UOrc) (s : UWSt),
    run orc s (m >>= f) = (run orc s m).bind (fun r => run r.2.2 r.2.1 (f r.1))

theorem umxRun_runRW (D : UFoot) : UmxRun (runRW D) :=
  ⟨fun _ _ _ => rfl, fun m f orc s => runRW_bind D m f orc s⟩

theorem umx_go {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)} (hR : UmxRun run)
    {α ε : Type} (orc : UOrc) (N : Nat) (fin : α → Bool)
    (f : α → ExceptT ε SailM α) (I : Nat → α → UWSt → Prop)
    (hf : ∀ k x s, I k x s → k < N → ∃ x' s', run orc s (ExceptT.run (f x)) = some (.ok x', s', orc) ∧
      I (k + 1) x' s' ∧ fin x' = (k + 1 == N)) :
    ∀ n k x s, I k x s → k + n = N → 0 < n →
      ∃ x' s', run orc s (ExceptT.run (untilFuelM.go (fun x => (pure (fin x) : ExceptT ε SailM Bool)) f x n)) =
        some (.ok x', s', orc) ∧ I N x' s' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
    intro k x s hI hk _
    obtain ⟨x', s', hrun, hI', hfin⟩ := hf k x s hI (by omega)
    unfold untilFuelM.go
    simp only [ExceptT.run_bind, hR.bind, hrun, Option.bind_some]
    simp only [ExceptT.run_pure, hR.pure, Option.bind_some, hfin]
    by_cases hk1 : k + 1 = N
    · subst hk1
      simp only [beq_self_eq_true, if_true, ExceptT.run_pure, hR.pure]
      exact ⟨x', s', rfl, hI'⟩
    · have hb : (k + 1 == N) = false := by simpa using hk1
      simp only [hb, Bool.false_eq_true, if_false]
      exact ih (k + 1) x' s' hI' (by omega) (by omega)

/-- The chunk loop followed by its continuation (`umm_loop_bind` for any `UmxRun` walker). -/
theorem umx_loop_bind {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)} (hR : UmxRun run)
    {α ε Y : Type} (orc : UOrc) (N : Nat) (hN : 0 < N) (fin : α → Bool)
    (f : α → ExceptT ε SailM α) (I : Nat → α → UWSt → Prop) (x0 : α) (s0 : UWSt) (h0 : I 0 x0 s0)
    (hf : ∀ k x s, I k x s → k < N → ∃ x' s', run orc s (ExceptT.run (f x)) = some (.ok x', s', orc) ∧
      I (k + 1) x' s' ∧ fin x' = (k + 1 == N))
    (G : Except ε α × UWSt × UOrc → Option Y) (P : Option Y → Prop)
    (hG : ∀ x' s', I N x' s' → P (G (.ok x', s', orc))) :
    P ((run orc s0 (ExceptT.run (untilFuelM N (fun x => (pure (fin x) : ExceptT ε SailM Bool)) x0 f))).bind G) := by
  obtain ⟨x', s', h, hI⟩ := umx_go hR orc N fin f I hf N 0 x0 s0 h0 (by omega) hN
  rw [show untilFuelM N (fun x => (pure (fin x) : ExceptT ε SailM Bool)) x0 f =
    untilFuelM.go (fun x => (pure (fin x) : ExceptT ε SailM Bool)) f x0 N from rfl, h]
  exact hG x' s' hI

/-! ## §3 The chunked read -/

/-- The model's chunk bounds `8 * (i + 1) * b - 1` and `8 * i * b`, as natural numbers. -/
theorem umx_ib (i b : Nat) :
    ((8 : Int) * ((i : Int) + 1) * (b : Int) - 1).toNat = 8 * (i * b) + 8 * b - 1 ∧
      ((8 : Int) * (i : Int) * (b : Int)).toNat = 8 * (i * b) := by
  have e1 : (8 : Int) * ((i : Int) + 1) * (b : Int) = ((8 * (i * b) + 8 * b : Nat) : Int) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.mul_assoc, Int.natCast_add, Int.natCast_mul]; rfl
  have e2 : (8 : Int) * (i : Int) * (b : Int) = ((8 * (i * b) : Nat) : Int) := by
    simp only [Int.mul_assoc, Int.natCast_mul]; rfl
  rw [e1, e2]; omega

/-- **The chunked read, at a given plan, with its value**, for any `UmxRun` walker whose plain RAM
reads answer from the map `M` (`hrd`): the window's bytes (`bmRead M`), whatever the chunk plan. -/
theorem umx_checked_mem_read_plan {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)}
    (hR : UmxRun run) (M : BMap) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (pbmt : page_based_mem_type) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (N b : Nat) (hN : 0 < N) (hb : 0 < b) (hNb : N * b = W) (_hW : W ≤ 8)
    (hpma : run orc s (check_pma_with_pmp_priority (.Load .Data) pbmt priv (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hsp : split_misaligned (.Physaddr pa) W info.granule_size_exp info.splittable =
      (pure ((N : Int), (b : Int)) : SailM (Int × Int)))
    (hpmp : ∀ j c, 0 < c → j + c ≤ W →
      run orc s (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Load .Data) priv) = some (none, s, orc))
    (hmmio : ∀ j c, 0 < c → j + c ≤ W →
      run orc s (within_mmio_readable (.Physaddr (pa + BitVec.ofNat 64 j)) c) = some (false, s, orc))
    (hrd : ∀ j c (u : BitVec (8 * c)), 0 < c → j + c ≤ W → bmRead M (pa + BitVec.ofNat 64 j) c = some u →
      run orc s (read_ram .Read_plain (.Physaddr (pa + BitVec.ofNat 64 j)) c false) = some ((u, ()), s, orc))
    (v : BitVec (8 * W)) (hv : bmRead M pa W = some v) :
    run orc s (checked_mem_read (.Load .Data) pbmt priv (.Physaddr pa) W false false false false) =
      some (.Ok (v, ()), s, orc) := by
  unfold checked_mem_read
  sail_norm
  simp only [hR.bind, hpma, Option.bind_some, read_kind_of_flags]
  sail_norm
  simp only [hR.bind, hR.pure, Option.bind_some, hsp]
  sail_norm
  simp only [Option.bind_assoc]
  refine umx_loop_bind hR (α := BitVec ((8 * (N : Int) * (b : Int)).toNat) × Bool × Nat) orc N hN (fun x => x.2.1) _
    (fun k x s' => s' = s ∧ (k < N → x.2.1 = false ∧ x.2.2 = k) ∧
      ∀ t, x.1.getLsbD t = (decide (t < 8 * (k * b)) && v.getLsbD t)) _ s ?h0 ?hf _
    (fun o => o = some (Result.Ok (v, ()), s, orc)) ?hG
  case h0 =>
    refine ⟨rfl, fun _ => ⟨rfl, rfl⟩, fun t => ?_⟩
    simp
  case hG =>
    intro x' s' ⟨hs, _, hx⟩
    subst hs
    have hx' : BitVec.setWidth (8 * W) (BitVec.setWidth (8 * N * b) x'.1) = v := by
      ext t ht
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, hx]
      have : t < 8 * N * b := by rw [Nat.mul_assoc, hNb]; exact ht
      have : t < 8 * (N * b) := by rw [hNb]; exact ht
      simp [*]
    simp only [hR.pure, hx', Option.bind_some]
  case hf =>
    intro k ⟨d, fin, i⟩ s' ⟨hs, hI, hd⟩ hk
    obtain ⟨hf0, hik⟩ := hI hk
    simp only at hf0 hik hk hd
    subst hf0 hik hs
    have hk' : i < N := hk
    clear hk
    have hw := umm_chunk_le N b i W hNb hk'
    have hv' := hrd (i * b) b _ hb hw (umx_bmRead_sub M pa W v hv (i * b) b hw)
    simp only [utr_assert_true, umm_ofInt_mul, ExceptT.run_bind, run_liftM, hR.bind, hpmp (i * b) b hb hw,
      hmmio (i * b) b hb hw, hR.pure, Option.bind_some]
    sail_norm
    simp only [hR.bind, hv', hR.pure, Option.bind_some]
    obtain ⟨e1, e2⟩ := umm_idx N i
    refine ⟨_, s', rfl, ⟨rfl, ?_, ?_⟩, ?_⟩
    · intro hlt
      have h1 : (i == N - 1) = false := by simp; omega
      simp only [e1, e2, h1, Bool.false_eq_true, if_false]
      simp
    · intro t
      obtain ⟨f1, f2⟩ := umx_ib i b
      have f3 : ((8 : Int) * (N : Int) * (b : Int)).toNat = 8 * W := by
        rw [(umx_ib N b).2, hNb]
      simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.getLsbD_setWidth,
        BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_allOnes, BitVec.getLsbD_extractLsb', hd]
      have h8 : 8 * N * b = 8 * W := by rw [Nat.mul_assoc, hNb]
      simp only [Nat.succ_mul i b, f1, f2, f3, h8]
      generalize i * b = q at *
      by_cases h1 : t < 8 * q <;> by_cases h2 : t < 8 * q + 8 * b <;> by_cases h3 : t < 8 * W <;>
        simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.add_sub_cancel', Bool.true_and,
          Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_true, Bool.not_false, Bool.or_false,
          Bool.false_or] <;> omega
    · simp only [e1, e2]
      by_cases hi : i + 1 = N
      · have h1 : (i == N - 1) = true := by simp; omega
        simp only [h1, if_true, hi, beq_self_eq_true]
      · have h1 : (i == N - 1) = false := by simp; omega
        have h2 : (i + 1 == N) = false := by simpa using hi
        simp only [h1, h2, Bool.false_eq_true, if_false]

/-- Two distinct offsets below `2^64` are distinct addresses. -/
theorem umx_ofNat_ne (pa : PAddr) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    pa + BitVec.ofNat 64 i ≠ pa + BitVec.ofNat 64 j := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := pa.isLt
  omega

/-- A written byte reads back. -/
theorem umx_bmWrite_in (mm : BMap) (pa : PAddr) (n : Nat) (hn : n < 2 ^ 64) (w : BitVec (8 * n)) (j : Nat) (hj : j < n) :
    bmWrite mm pa n w (pa + BitVec.ofNat 64 j) = some (nthByte w j) := by
  unfold bmWrite
  suffices ∀ (l : List Nat) (m : BMap), (∀ k ∈ l, k < n) →
      (l.foldl (fun m k => bmSet m (pa + BitVec.ofNat 64 k) (nthByte w k)) m) (pa + BitVec.ofNat 64 j) =
        if j ∈ l then some (nthByte w j) else m (pa + BitVec.ofNat 64 j) by
    rw [this _ mm (fun k hk => List.mem_range.1 hk), if_pos (List.mem_range.2 hj)]
  intro l
  induction l with
  | nil => intro m _; simp
  | cons x l ih =>
    intro m hl
    rw [List.foldl_cons, ih _ (fun k hk => hl k (List.mem_cons_of_mem _ hk))]
    unfold bmSet
    by_cases e : j = x
    · subst e; simp
    · rw [if_neg (umx_ofNat_ne pa j x (by omega) (by have := hl x List.mem_cons_self; omega) e)]
      simp [e]

/-- A byte outside the written window is untouched. -/
theorem umx_bmWrite_out (mm : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (a : PAddr)
    (ha : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j) :
    bmWrite mm pa n w a = mm a := by
  unfold bmWrite
  suffices ∀ (l : List Nat) (m : BMap), (∀ k ∈ l, k < n) →
      (l.foldl (fun m k => bmSet m (pa + BitVec.ofNat 64 k) (nthByte w k)) m) a = m a from
    this _ mm (fun k hk => List.mem_range.1 hk)
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons x l ih =>
    intro m hl
    rw [List.foldl_cons, ih _ (fun k hk => hl k (List.mem_cons_of_mem _ hk))]
    unfold bmSet
    rw [if_neg (ha x (hl x List.mem_cons_self))]

/-! ## §4 The chunked write -/

/-- The bytes of `data` written at `[pa, pa + n)` over `mm`. -/
def umxWin (mm : BMap) (pa : PAddr) (n : Nat) (data : Nat → BitVec 8) (m : BMap) : Prop :=
  (∀ j, j < n → m (pa + BitVec.ofNat 64 j) = some (data j)) ∧
    (∀ a, (∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j) → m a = mm a)

theorem umxWin_zero (mm : BMap) (pa : PAddr) (f : Nat → BitVec 8) : umxWin mm pa 0 f mm :=
  ⟨fun _ h => absurd h (by omega), fun _ _ => rfl⟩

/-- Writing the next chunk extends the written window. -/
theorem umxWin_step (mm m : BMap) (pa : PAddr) (q b : Nat) (hqb : q + b < 2 ^ 64) (f : Nat → BitVec 8)
    (h : umxWin mm pa q f m) (c : BitVec (8 * b)) (hc : ∀ j, j < b → nthByte c j = f (q + j)) :
    umxWin mm pa (q + b) f (bmWrite m (pa + BitVec.ofNat 64 q) b c) := by
  have hadd : ∀ j, pa + BitVec.ofNat 64 q + BitVec.ofNat 64 j = pa + BitVec.ofNat 64 (q + j) := by
    intro j; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨fun j hj => ?_, fun a ha => ?_⟩
  · by_cases hjq : j < q
    · rw [umx_bmWrite_out m _ b c _ (fun j' hj' => by
        rw [hadd]; exact umx_ofNat_ne pa j (q + j') (by omega) (by omega) (by omega)), h.1 j hjq]
    · have e : pa + BitVec.ofNat 64 j = pa + BitVec.ofNat 64 q + BitVec.ofNat 64 (j - q) := by
        rw [hadd]; congr 2; omega
      rw [e, umx_bmWrite_in m _ b (by omega) c (j - q) (by omega), hc (j - q) (by omega)]
      congr 2; omega
  · rw [umx_bmWrite_out m _ b c _ (fun j' hj' => by rw [hadd]; exact ha (q + j') (by omega)),
      h.2 a (fun j hj => ha j (by omega))]

/-- The whole window written is `bmWrite`. -/
theorem umxWin_full (mm m : BMap) (pa : PAddr) (W : Nat) (hW : W < 2 ^ 64) (data : BitVec (8 * W))
    (h : umxWin mm pa W (nthByte data) m) : m = bmWrite mm pa W data := by
  funext a
  by_cases ha : ∃ j, j < W ∧ a = pa + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := ha
    rw [h.1 j hj, umx_bmWrite_in mm pa W hW data j hj]
  · have ha' : ∀ j, j < W → a ≠ pa + BitVec.ofNat 64 j := fun j hj e => ha ⟨j, hj, e⟩
    rw [h.2 a ha', umx_bmWrite_out mm pa W data a ha']

/-- **The chunked write, at a given plan, with its bytes**: the map is `bmWrite` of the whole
window, the reservation bit cleared, whatever the chunk plan. -/
theorem umm_checked_mem_write_exact_plan (D : UFoot) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (data : BitVec (8 * W)) (pbmt : page_based_mem_type) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (N b : Nat) (hN : 0 < N) (hb : 0 < b) (hNb : N * b = W) (hW : W ≤ 8)
    (hpma : runRW D orc s (check_pma_with_pmp_priority (.Store .Data) pbmt priv (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hsp : split_misaligned (.Physaddr pa) W info.granule_size_exp info.splittable =
      (pure ((N : Int), (b : Int)) : SailM (Int × Int)))
    (hpmp : ∀ j c st, 0 < c → j + c ≤ W → ummSameRegs s st →
      runRW D orc st (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Store .Data) priv) = some (none, st, orc))
    (hmmio : ∀ j c st, 0 < c → j + c ≤ W → ummSameRegs s st →
      runRW D orc st (within_mmio_writable (.Physaddr (pa + BitVec.ofNat 64 j)) c) = some (false, st, orc))
    (hown : bmOwned s.mm pa W = true) :
    runRW D orc s (checked_mem_write (.Physaddr pa) W data (.Store .Data) pbmt priv () false false false) =
      some (.Ok true, { s with mm := bmWrite s.mm pa W data, rv := false }, orc) := by
  have hown' : ummOwned s.mm pa W := fun j hj => (List.all_eq_true.1 hown) j (List.mem_range.2 hj)
  unfold checked_mem_write
  sail_norm
  simp only [runRW_bind, hpma, Option.bind_some, write_kind_of_flags]
  sail_norm
  simp only [runRW_bind, runRW_pure, Option.bind_some, hsp]
  sail_norm
  simp only [Option.bind_assoc]
  refine umm_loop_bind (α := Bool × Nat × Bool) D orc N hN (fun x => x.1) _
    (fun k x st => ummSameRegs s st ∧ umxWin s.mm pa (k * b) (nthByte data) st.mm ∧ (0 < k → st.rv = false) ∧
      x.2.2 = true ∧ (k < N → x.1 = false ∧ x.2.1 = k)) _ s ?h0 ?hf _
    (fun o => o = some (Result.Ok true, { s with mm := bmWrite s.mm pa W data, rv := false }, orc)) ?hG
  case h0 => exact ⟨⟨rfl, rfl⟩, by simpa using umxWin_zero s.mm pa (nthByte data), fun h => absurd h (by omega),
    rfl, fun _ => ⟨rfl, rfl⟩⟩
  case hG =>
    intro ⟨fin, i, ws⟩ ⟨pin, rs, m, rv⟩ ⟨⟨hp, hr⟩, hd, hrv, hws, _⟩
    simp only at hp hr hd hrv hws
    subst hp hr hws
    obtain rfl := hrv hN
    rw [hNb] at hd
    rw [umxWin_full s.mm m pa W (by omega) data hd]
    rfl
  case hf =>
    intro k ⟨d, i, ws⟩ st ⟨hsr, hd, _, hws, hI⟩ hk
    obtain ⟨hf0, hik⟩ := hI hk
    simp only at hf0 hik hk hws
    subst hf0 hik hws
    have hk' : i < N := hk
    clear hk
    have hw := umm_chunk_le N b i W hNb hk'
    have ho : bmOwned st.mm (pa + BitVec.ofNat 64 (i * b)) b = true := by
      apply bmOwned_of_ummOwned
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hd.2 _ (fun j' hj' =>
        umx_ofNat_ne pa (i * b + j) j' (by omega) (by omega) (by omega))]
      exact hown' (i * b + j) (by omega)
    have hv' := fun v => uma_write_ram_plain D orc st (pa + BitVec.ofNat 64 (i * b)) b (by omega) v ho
    simp only [utr_assert_true, umm_ofInt_mul, ExceptT.run_bind, run_liftM, runRW_bind, hpmp (i * b) b st hb hw hsr,
      hmmio (i * b) b st hb hw hsr, runRW_pure, Option.bind_some]
    sail_norm
    simp only [runRW_bind, hv', runRW_pure, Option.bind_some]
    obtain ⟨e1, e2⟩ := umm_idx N i
    refine ⟨_, _, rfl, ⟨hsr, ?_, fun _ => rfl, rfl, ?_⟩, ?_⟩
    · obtain ⟨f1, f2⟩ := umx_ib i b
      simp only [f2, Nat.succ_mul i b]
      refine umxWin_step s.mm st.mm pa (i * b) b (by omega) _ hd _ (fun j hj => ?_)
      unfold nthByte
      ext t ht
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
      have : 8 * j + t < 8 * b := by omega
      have : 8 * j + t < 8 * (i * b) + 8 * b - 1 - 8 * (i * b) + 1 := by omega
      simp only [*, decide_true, Bool.true_and]
      congr 1; omega
    · intro hlt
      have h1 : (i == N - 1) = false := by simp; omega
      simp only [e1, e2, h1, Bool.false_eq_true, if_false]
      simp
    · simp only [e1, e2]
      by_cases hi : i + 1 = N
      · have h1 : (i == N - 1) = true := by simp; omega
        simp only [h1, if_true, hi, beq_self_eq_true]
      · have h1 : (i == N - 1) = false := by simp; omega
        have h2 : (i + 1 == N) = false := by simpa using hi
        simp only [h1, h2, Bool.false_eq_true, if_false]

/-- **The misaligned physical read, with its value**, for any `UmxRun` walker: whatever the granule
check answered. -/
theorem umx_checked_mem_read {run : {X : Type} → UOrc → UWSt → SailM X → Option (X × UWSt × UOrc)}
    (hR : UmxRun run) (M : BMap) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (pbmt : page_based_mem_type) (priv : Privilege) (info : Phys_Mem_Access_Info) (h0 : 0 < W) (hW : W ≤ 8)
    (hpma : run orc s (check_pma_with_pmp_priority (.Load .Data) pbmt priv (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hpmp : ∀ j c, 0 < c → j + c ≤ W →
      run orc s (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Load .Data) priv) = some (none, s, orc))
    (hmmio : ∀ j c, 0 < c → j + c ≤ W →
      run orc s (within_mmio_readable (.Physaddr (pa + BitVec.ofNat 64 j)) c) = some (false, s, orc))
    (hrd : ∀ j c (u : BitVec (8 * c)), 0 < c → j + c ≤ W → bmRead M (pa + BitVec.ofNat 64 j) c = some u →
      run orc s (read_ram .Read_plain (.Physaddr (pa + BitVec.ofNat 64 j)) c false) = some ((u, ()), s, orc))
    (v : BitVec (8 * W)) (hv : bmRead M pa W = some v) :
    run orc s (checked_mem_read (.Load .Data) pbmt priv (.Physaddr pa) W false false false false) =
      some (.Ok (v, ()), s, orc) := by
  obtain ⟨N, b, hN, hb, hNb, hsp⟩ := umm_split_misaligned_plan pa W info.granule_size_exp info.splittable h0 hW
  exact umx_checked_mem_read_plan hR M orc s pa W pbmt priv info N b hN hb hNb hW hpma hsp hpmp hmmio hrd v hv

/-- **The misaligned physical read, with its value** (`runRW`): whatever the granule check answered. -/
theorem umm_checked_mem_read_exact (D : UFoot) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (pbmt : page_based_mem_type) (priv : Privilege) (info : Phys_Mem_Access_Info) (h0 : 0 < W) (hW : W ≤ 8)
    (hpma : runRW D orc s (check_pma_with_pmp_priority (.Load .Data) pbmt priv (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hpmp : ∀ j c, 0 < c → j + c ≤ W →
      runRW D orc s (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Load .Data) priv) = some (none, s, orc))
    (hmmio : ∀ j c, 0 < c → j + c ≤ W →
      runRW D orc s (within_mmio_readable (.Physaddr (pa + BitVec.ofNat 64 j)) c) = some (false, s, orc))
    (v : BitVec (8 * W)) (hv : bmRead s.mm pa W = some v) :
    runRW D orc s (checked_mem_read (.Load .Data) pbmt priv (.Physaddr pa) W false false false false) =
      some (.Ok (v, ()), s, orc) := by
  obtain ⟨N, b, hN, hb, hNb, hsp⟩ := umm_split_misaligned_plan pa W info.granule_size_exp info.splittable h0 hW
  exact umx_checked_mem_read_plan (umxRun_runRW D) s.mm orc s pa W pbmt priv info N b hN hb hNb hW hpma hsp hpmp
    hmmio (fun j c u _ hjc hu => uma_read_ram_plain D orc s _ c (by omega) u hu) v hv

/-- **The misaligned physical write, with its bytes**: whatever the granule check answered. -/
theorem umm_checked_mem_write_exact (D : UFoot) (orc : UOrc) (s : UWSt) (pa : BitVec 64) (W : Nat)
    (data : BitVec (8 * W)) (pbmt : page_based_mem_type) (priv : Privilege) (info : Phys_Mem_Access_Info)
    (h0 : 0 < W) (hW : W ≤ 8)
    (hpma : runRW D orc s (check_pma_with_pmp_priority (.Store .Data) pbmt priv (.Physaddr pa) W false) =
      some (.Ok info, s, orc))
    (hpmp : ∀ j c st, 0 < c → j + c ≤ W → ummSameRegs s st →
      runRW D orc st (pmpCheck (.Physaddr (pa + BitVec.ofNat 64 j)) c (.Store .Data) priv) = some (none, st, orc))
    (hmmio : ∀ j c st, 0 < c → j + c ≤ W → ummSameRegs s st →
      runRW D orc st (within_mmio_writable (.Physaddr (pa + BitVec.ofNat 64 j)) c) = some (false, st, orc))
    (hown : bmOwned s.mm pa W = true) :
    runRW D orc s (checked_mem_write (.Physaddr pa) W data (.Store .Data) pbmt priv () false false false) =
      some (.Ok true, { s with mm := bmWrite s.mm pa W data, rv := false }, orc) := by
  obtain ⟨N, b, hN, hb, hNb, hsp⟩ := umm_split_misaligned_plan pa W info.granule_size_exp info.splittable h0 hW
  exact umm_checked_mem_write_exact_plan D orc s pa W data pbmt priv info N b hN hb hNb hW hpma hsp hpmp hmmio hown

end MachCSL
