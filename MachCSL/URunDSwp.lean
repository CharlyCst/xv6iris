/-
MachCSL: **the soundness of the walker over a memory with dirty bytes**
(`swp_uxdRun`, the analogue of `URunXSwp.swp_uxRun`).

The bytes of the map `T` are owned as `uxdOwn ξ K DT dirty T`: a clean byte
stamped at `K` (`ctxByteX`), a dirty one as a plain context byte (`ctxByte`).
Beside the receipt `iviewLb cpu K`:

* `swp_sail_mem_read_ifetch_d` -- **the mixed fetch gate**: an instruction
  fetch returns the clean bytes exactly and SOME value on the dirty ones (the
  machine reads at a view `≥ itv ≥ K`; progress at the view `top`, where every
  byte reads its latest store);
* `swp_sail_mem_read_plain_d` -- **the mixed data gate**: a plain load returns
  the latest stores, the stamps kept;
* `swp_uxdRun` -- the walk rule: a fetch of a dirty window lands on the
  oracle that drew the machine's answer (as `urw_choose`), every other node
  is `uxRun`'s.
-/
import MachCSL.URunD
import MachCSL.UIcacheFence

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors}

section own
variable [MachGS hlc GF]

/-! ## Ownership -/

/-- A byte of a memory with dirty bytes: stamped at `K` if clean, a context
byte if dirty. -/
def uxdByte (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8) : IProp GF :=
  if dirty a then ctxByte ξ a (DFrac.own 1) v else ctxByteX ξ K a (DFrac.own 1) v

/-- The `n` bytes of `w` at `pa` (little-endian). -/
def uxdBytes (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    IProp GF :=
  iprop([∗list] j ∈ List.range n, uxdByte ξ K dirty (pa + BitVec.ofNat 64 j) (nthByte w j))

/-- The bytes of the addresses `D`, at the map's values. -/
def uxdOwnL (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (D : List PAddr) (mm : BMap) : IProp GF :=
  iprop([∗list] a ∈ D, ∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ uxdByte ξ K dirty a b)

/-- **The map, owned**: its domain is exactly `DT` (duplicate-free), clean
bytes stamped at `K`, dirty ones context bytes. -/
def uxdOwn (ξ : CtxId) (K : Nat) (DT : List PAddr) (dirty : PAddr → Bool) (T : BMap) : IProp GF :=
  iprop(⌜DT.Nodup ∧ ∀ a, (T a).isSome = true ↔ a ∈ DT⌝ ∗ uxdOwnL ξ K dirty DT T)

instance uxdByte_timeless (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8) :
    Timeless (uxdByte (GF := GF) ξ K dirty a v) := by
  unfold uxdByte; split <;> infer_instance

instance uxdOwn_timeless (ξ : CtxId) (K : Nat) (DT : List PAddr) (dirty : PAddr → Bool) (T : BMap) :
    Timeless (uxdOwn (GF := GF) ξ K DT dirty T) := by
  unfold uxdOwn uxdOwnL; infer_instance

theorem uxdByte_clean (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8)
    (h : dirty a = false) : uxdByte (GF := GF) ξ K dirty a v = ctxByteX ξ K a (DFrac.own 1) v := by
  unfold uxdByte; simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem uxdByte_dirty (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8)
    (h : dirty a = true) : uxdByte (GF := GF) ξ K dirty a v = ctxByte ξ a (DFrac.own 1) v := by
  unfold uxdByte; simp only [h, ↓reduceIte]

/-- A byte of the map is a context byte. -/
theorem uxdByte_forget (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8) :
    uxdByte ξ K dirty a v ⊢@{IProp GF} ctxByte ξ a (DFrac.own 1) v := by
  cases h : dirty a
  · rw [uxdByte_clean ξ K dirty a v h]; exact ctxByteX_forget ξ K a _ v
  · rw [uxdByte_dirty ξ K dirty a v h]

theorem uxdBytes_forget (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) : uxdBytes ξ K dirty pa n w ⊢@{IProp GF} ctxBytes ξ pa n (DFrac.own 1) w := by
  unfold uxdBytes ctxBytes
  apply BigSepL.bigSepL_mono
  intro _ j _
  exact uxdByte_forget ξ K dirty _ _

/-! ## The accessor -/

theorem uxdOwnL_app (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (D₁ D₂ : List PAddr) (mm : BMap) :
    uxdOwnL (GF := GF) ξ K dirty (D₁ ++ D₂) mm ⊣⊢
      iprop(uxdOwnL ξ K dirty D₁ mm ∗ uxdOwnL ξ K dirty D₂ mm) := by
  unfold uxdOwnL; exact BigSepL.bigSepL_append

theorem uxdOwnL_perm (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (D₁ D₂ : List PAddr) (mm : BMap)
    (h : D₁.Perm D₂) : uxdOwnL (GF := GF) ξ K dirty D₁ mm ⊣⊢ uxdOwnL ξ K dirty D₂ mm := by
  unfold uxdOwnL; exact BigSepL.bigSepL_perm h

/-- A readable window's bytes are a `uxdBytes` word. -/
theorem uxdOwnL_win (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr) (n : Nat) (mm : BMap)
    (w : BitVec (8 * n)) (hr : bmRead mm pa n = some w) :
    uxdOwnL (GF := GF) ξ K dirty (ubWin pa n) mm ⊣⊢ uxdBytes ξ K dirty pa n w := by
  unfold uxdOwnL ubWin uxdBytes
  rw [BigSepL.bigSepL_map]
  constructor
  · apply BigSepL.bigSepL_mono
    intro k j hk
    have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
    have hs := bmRead_spec mm pa n w hr j hj
    iintro ⟨%b, %hb, H⟩
    rw [hs] at hb
    obtain rfl := Option.some.inj hb
    iexact H
  · apply BigSepL.bigSepL_mono
    intro k j hk
    have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
    have hs := bmRead_spec mm pa n w hr j hj
    iintro H
    iexists nthByte w j
    iframe H
    ipureintro
    exact hs

/-- **The accessor**: a readable window of the owned map is a `uxdBytes`
word, handed back unchanged. -/
theorem uxdOwn_acc (ξ : CtxId) (K : Nat) (DT : List PAddr) (dirty : PAddr → Bool) (T : BMap) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (hn : n < 2 ^ 64) (hr : bmRead T pa n = some w) :
    uxdOwn ξ K DT dirty T ⊢@{IProp GF}
      uxdBytes ξ K dirty pa n w ∗ (uxdBytes ξ K dirty pa n w -∗ uxdOwn ξ K DT dirty T) := by
  unfold uxdOwn
  iintro ⟨%⟨hnd, hdom⟩, H⟩
  have hsub : ∀ a ∈ ubWin pa n, a ∈ DT := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (ubWin_mem pa n a).1 ha
    exact (hdom _).1 (by rw [bmRead_spec T pa n w hr j hj]; rfl)
  have hp := ub_perm_win DT pa n (by omega) hnd hsub
  icases (uxdOwnL_perm ξ K dirty _ _ T hp).1 $$ H with H
  icases (uxdOwnL_app ξ K dirty _ _ T).1 $$ H with ⟨Hw, Hr⟩
  icases (uxdOwnL_win ξ K dirty pa n T w hr).1 $$ Hw with Hb
  iframe Hb
  iintro Hb
  isplit
  · ipureintro
    exact ⟨hnd, hdom⟩
  iapply (uxdOwnL_perm ξ K dirty _ _ T hp).2
  iapply (uxdOwnL_app ξ K dirty _ _ T).2
  iframe Hr
  iapply (uxdOwnL_win ξ K dirty pa n T w hr).2 $$ Hb

/-! ## The store accessor -/

theorem uxdOwnL_congr (ξ : CtxId) (K : Nat) (dirty dirty' : PAddr → Bool) (D : List PAddr) (mm mm' : BMap)
    (h : ∀ a ∈ D, mm' a = mm a ∧ dirty' a = dirty a) :
    uxdOwnL (GF := GF) ξ K dirty D mm ⊢ uxdOwnL ξ K dirty' D mm' := by
  unfold uxdOwnL
  apply BigSepL.bigSepL_mono
  intro k a hk
  obtain ⟨hm, hd⟩ := h a (List.mem_of_getElem? hk)
  have e : uxdByte (GF := GF) ξ K dirty' a = uxdByte ξ K dirty a := by
    funext v; unfold uxdByte; rw [hd]
  rw [hm, e]

/-- Context bytes of a window whose bytes are all dirty are its `uxdBytes`. -/
theorem uxdBytes_of_ctxBytes (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (h : ∀ j, j < n → dirty (pa + BitVec.ofNat 64 j) = true) :
    ctxBytes (GF := GF) ξ pa n (DFrac.own 1) w ⊢ uxdBytes ξ K dirty pa n w := by
  unfold uxdBytes ctxBytes
  apply BigSepL.bigSepL_mono
  intro k j hk
  rw [uxdByte_dirty ξ K dirty _ _ (h j (List.mem_range.1 (List.mem_of_getElem? hk)))]

/-- **The store accessor**: a window of the owned map is a context word, and
any word written back leaves the window's bytes dirty. -/
theorem uxdOwn_store (ξ : CtxId) (K : Nat) (DT : List PAddr) (dirty : PAddr → Bool) (T : BMap) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (hn : n < 2 ^ 64) (hr : bmRead T pa n = some w) :
    uxdOwn ξ K DT dirty T ⊢@{IProp GF}
      ctxBytes ξ pa n (DFrac.own 1) w ∗
      ∀ w' : BitVec (8 * n), ctxBytes ξ pa n (DFrac.own 1) w' -∗
        uxdOwn ξ K DT (fun a => dirty a || decide (a ∈ ubWin pa n)) (bmWrite T pa n w') := by
  have ho : bmOwned T pa n = true := bmOwned_of_read T pa n w hr
  unfold uxdOwn
  iintro ⟨%⟨hnd, hdom⟩, H⟩
  have hsub : ∀ a ∈ ubWin pa n, a ∈ DT := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (ubWin_mem pa n a).1 ha
    exact (hdom _).1 (by rw [bmRead_spec T pa n w hr j hj]; rfl)
  have hp := ub_perm_win DT pa n (by omega) hnd hsub
  icases (uxdOwnL_perm ξ K dirty _ _ T hp).1 $$ H with H
  icases (uxdOwnL_app ξ K dirty _ _ T).1 $$ H with ⟨Hw, Hr⟩
  icases (uxdOwnL_win ξ K dirty pa n T w hr).1 $$ Hw with Hb
  isplitl [Hb]
  · iapply uxdBytes_forget $$ Hb
  iintro %w' Hb
  have hr' : bmRead (bmWrite T pa n w') pa n = some w' :=
    bmRead_of_bytes _ pa n w' (fun j hj => bmWrite_at T pa n w' (by omega) j hj)
  isplit
  · ipureintro
    refine ⟨hnd, fun a => ?_⟩
    rw [bmWrite_isSome T pa n w' (by omega) ho a]
    exact hdom a
  iapply (uxdOwnL_perm ξ K _ _ _ _ hp).2
  iapply (uxdOwnL_app ξ K _ _ _ _).2
  isplitl [Hb]
  · iapply (uxdOwnL_win ξ K _ pa n _ w' hr').2
    iapply uxdBytes_of_ctxBytes ξ K _ pa n w' ?_ $$ Hb
    intro j hj
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ((ubWin_mem pa n _).2 ⟨j, hj, rfl⟩)
  · iapply uxdOwnL_congr ξ K dirty _ _ T _ ?_ $$ Hr
    intro a ha
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    refine ⟨bmWrite_other T pa n w' a ha.2, ?_⟩
    simp [ha.2]

/-! ## The histories behind the bytes -/

/-- An owned byte's history: its head is the byte, and at or below `K` if
the byte is clean. -/
theorem uxd_byte_hist (m : FlatMem) (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8) :
    genHeapInterp m ∗ uxdByte ξ K dirty a v ⊢@{IProp GF}
      ⌜∃ (e : HEnt) (H : Hist), m[a]? = some (e :: H) ∧ e.v = v ∧ (dirty a = false → e.t ≤ K)⌝ := by
  cases hd : dirty a
  · rw [uxdByte_clean ξ K dirty a v hd]
    unfold ctxByteX
    iintro ⟨Hmem, ⟨%e, %H, Hpt, %hev, _, %htK⟩⟩
    ihave %hget : ⌜m[a]? = some (e :: H)⌝ $$ [Hmem Hpt]
    · icases genHeap_valid $$ [$Hmem $Hpt] with >%_
      itrivial
    ipureintro
    exact ⟨e, H, hget, hev, fun _ => htK⟩
  · rw [uxdByte_dirty ξ K dirty a v hd]
    unfold ctxByte
    iintro ⟨Hmem, ⟨%e, %H, Hpt, %hev, _⟩⟩
    ihave %hget : ⌜m[a]? = some (e :: H)⌝ $$ [Hmem Hpt]
    · icases genHeap_valid $$ [$Hmem $Hpt] with >%_
      itrivial
    ipureintro
    exact ⟨e, H, hget, hev, fun h => absurd h (by decide)⟩

theorem uxd_bytes_hist (m : FlatMem) (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr)
    (bs : Nat → BitVec 8) : ∀ n : Nat,
    genHeapInterp m ∗ ([∗list] j ∈ List.range n, uxdByte ξ K dirty (pa + BitVec.ofNat 64 j) (bs j))
      ⊢@{IProp GF} ⌜∀ j, j < n → ∃ (e : HEnt) (H : Hist), m[pa + BitVec.ofNat 64 j]? = some (e :: H) ∧
        e.v = bs j ∧ (dirty (pa + BitVec.ofNat 64 j) = false → e.t ≤ K)⌝
  | 0 => by
    iintro ⟨_, _⟩
    ipureintro
    intro j hj
    omega
  | n + 1 => by
    rw [List.range_succ]
    iintro ⟨Hmem, Hb⟩
    icases BigSepL.bigSepL_snoc.1 $$ Hb with ⟨Hb1, Hb2⟩
    ihave %H1 : ⌜∀ j, j < n → ∃ (e : HEnt) (H : Hist), m[pa + BitVec.ofNat 64 j]? = some (e :: H) ∧
        e.v = bs j ∧ (dirty (pa + BitVec.ofNat 64 j) = false → e.t ≤ K)⌝ $$ [Hmem Hb1]
    · iapply uxd_bytes_hist m ξ K dirty pa bs n $$ [Hmem Hb1]
      iframe
    ihave %H2 : ⌜∃ (e : HEnt) (H : Hist), m[pa + BitVec.ofNat 64 n]? = some (e :: H) ∧
        e.v = bs n ∧ (dirty (pa + BitVec.ofNat 64 n) = false → e.t ≤ K)⌝ $$ [Hmem Hb2]
    · iapply uxd_byte_hist m ξ K dirty _ (bs n) $$ [Hmem Hb2]
      iframe
    ipureintro
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact H1 j h
    · exact H2

/-- A history's head, at or below the view, is what every agent reads. -/
theorem uxd_read_head {m : FlatMem} {a : PAddr} {e : HEnt} {H : Hist} (hg : m[a]? = some (e :: H))
    (ag : Agent) (tv : Nat) (ht : e.t ≤ tv) : m.read ag tv a = some e.v := by
  unfold FlatMem.read
  rw [hg, Option.bind_some, Hist.read_cons_visible _ _ _ _ (HEnt.visible_of_le _ _ _ ht)]

/-! ## The gates -/

/-- **THE MIXED FETCH GATE**: an instruction fetch of owned bytes, beside the
receipt `iviewLb cpu K`, returns their clean bytes exactly, and some value on
the dirty ones. -/
theorem swp_sail_mem_read_ifetch_d (cpu : CPU) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (w : BitVec (8 * n)) (hk : akIfetch req.access_kind = true)
    (Φ : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → IProp GF) :
    uxdBytes ξ K dirty req.pa n w ∗ iviewLb cpu K ∗
      ▷ (∀ w' : BitVec (8 * n),
          ⌜∀ j, j < n → dirty (bAddr req.pa j) = false → nthByte w' j = nthByte w j⌝ -∗
          uxdBytes ξ K dirty req.pa n w -∗ Φ (.Ok (w', none)))
    ⊢ swp cpu (ConcurrencyInterfaceV1.sail_mem_read req) Φ := by
  unfold ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read PreSail.emit
  iintro ⟨Hb, #Hiv, HΦ⟩
  have hex := akExcl_of_ifetch _ hk
  iapply swp_event cpu (.memRead n vasize req) (fun v => FreeM.pure v) Φ
    (fun _ _ hb => by
      have h1 : akExcl req.access_kind = true := hb.1
      rw [hex] at h1
      exact absurd h1 (by decide))
  iintro %σ Hσ
  icases machInterp_acc_mem σ cpu $$ Hσ with ⟨Hregs, Hmem, Hmm, Hclose⟩
  ihave %hh : ⌜∀ j, j < n → ∃ (e : HEnt) (H : Hist), σ.mem[bAddr req.pa j]? = some (e :: H) ∧
      e.v = nthByte w j ∧ (dirty (bAddr req.pa j) = false → e.t ≤ K)⌝ $$ [Hmem Hb]
  · unfold uxdBytes
    iapply uxd_bytes_hist σ.mem ξ K dirty req.pa (nthByte w) n $$ [Hmem Hb]
    iframe
  ihave %hK : ⌜K ≤ σ.itv cpu⌝ $$ [Hmm Hiv]
  · iapply uic_memModel_iviewLb _ σ cpu K $$ [Hmm Hiv]
    iframe Hmm
    iexact Hiv
  ihave %hmm : ⌜mmOk σ⌝ $$ [Hmm]
  · iapply memModel_mmOk $$ Hmm
  have htop : σ.mem.readBytes (ifetchAgent cpu) σ.top req.pa n w := fun j hj => by
    obtain ⟨e, H, hg, hv, -⟩ := hh j hj
    have ht : e.t ≤ σ.top := ((hmm.1 _ _ hg).2 e List.mem_cons_self).1
    rw [uxd_read_head hg _ _ ht, hv]
  have hram : ramBytes req.pa n := ramBytes_of_readBytes hmm.2.2.2.1 htop
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    exact ⟨.Ok (w, none), σ, Or.inr (Or.inl
      ⟨hram, hk, σ.top, w, (hmm.2.1 cpu).2.1, le_refl _, htop, rfl, rfl⟩)⟩
  inext
  iintro %v' %σ' %Hev
  rcases Hev with ⟨hdev, w₀, ds₀, hdr, _, _⟩ | ⟨_, _, tvn, w', htvn, _, hrd', rfl, hσ⟩ |
    ⟨_, hpl, _⟩ | ⟨_, hex', _⟩
  · exact absurd hdev (not_devBytes_of_ramBytes hram (devRead_pos hdr))
  · subst σ'
    have hag : ∀ j, j < n → dirty (bAddr req.pa j) = false → nthByte w' j = nthByte w j := by
      intro j hj hc
      obtain ⟨e, H, hg, hv, hkt⟩ := hh j hj
      have h1 := hrd' j hj
      rw [uxd_read_head hg _ _ (by have := hkt hc; omega)] at h1
      rw [← hv]
      exact (Option.some.inj h1).symm
    imod Hmask
    imodintro
    isplitl [Hregs Hmem Hmm Hclose]
    · iapply Hclose $$ %σ %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm
    · iapply swp_ret
      iapply HΦ $$ %w' %hag Hb
  · simp [akPlain, hk] at hpl
  · rw [hex] at hex'
    exact absurd hex' (by decide)

/-- **THE MIXED DATA GATE**: a plain load of owned bytes of the running context
returns them, the stamps kept. -/
theorem swp_sail_mem_read_plain_d (cpu : CPU) {n vasize : Nat}
    (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
    (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (w : BitVec (8 * n)) (hk : akPlain req.access_kind = true)
    (Φ : Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort → IProp GF) :
    ownCtx cpu ξ ∗ uxdBytes ξ K dirty req.pa n w ∗
    ▷ (ownCtx cpu ξ -∗ uxdBytes ξ K dirty req.pa n w -∗ Φ (.Ok (w, none)))
    ⊢ swp cpu (ConcurrencyInterfaceV1.sail_mem_read req) Φ := by
  unfold ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read PreSail.emit
  iintro ⟨Hctx, Hb, HΦ⟩
  have hk' : akIfetch req.access_kind = false ∧ akExcl req.access_kind = false := by
    unfold akPlain at hk
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
    exact hk
  iapply swp_event cpu (.memRead n vasize req) (fun v => FreeM.pure v) Φ
    (fun _ _ hb => by
      have h1 : akExcl req.access_kind = true := hb.1
      rw [hk'.2] at h1
      exact absurd h1 (by decide))
  iintro %σ Hσ
  icases machInterp_acc_mem σ cpu $$ Hσ with ⟨Hregs, Hmem, Hmm, Hclose⟩
  ihave %hrd : ⌜∀ tvn, σ.tv cpu ≤ tvn → σ.mem.readBytes (hartAgent cpu) tvn req.pa n w⌝
      $$ [Hmm Hctx Hmem Hb]
  · iapply ctxBytes_readable σ cpu ξ req.pa n (DFrac.own 1) w $$ [Hmm Hctx Hmem Hb]
    iframe Hmm Hctx Hmem
    iapply uxdBytes_forget $$ Hb
  ihave %hmm : ⌜mmOk σ⌝ $$ [Hmm]
  · iapply memModel_mmOk $$ Hmm
  have hram : ramBytes req.pa n := ramBytes_of_readBytes hmm.2.2.2.1 (hrd _ (Nat.le_refl _))
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    refine ⟨.Ok (w, none), σ.afterLoad cpu req.pa n σ.top, Or.inr (Or.inr (Or.inl
      ⟨hram, hk, σ.top, w, (hmm.2.1 cpu).1, le_refl _, ?_, hrd _ (hmm.2.1 cpu).1, rfl, rfl⟩))⟩
    intro j _
    exact (hmm.2.1 cpu).2.2.2 _
  inext
  iintro %v' %σ' %Hev
  rcases Hev with ⟨hdev, w₀, ds₀, hdr, _, _⟩ | ⟨_, hif, _⟩ |
    ⟨_, _, tvn, w', htv, htop, _, hrd', rfl, rfl⟩ | ⟨_, hex', _⟩
  · exact absurd hdev (not_devBytes_of_ramBytes hram (devRead_pos hdr))
  · rw [hk'.1] at hif
    exact absurd hif (by decide)
  · obtain rfl := readBytes_unique _ _ _ _ _ _ _ (hrd tvn htv) hrd'
    imod memModel_load _ σ cpu req.pa n tvn htop $$ Hmm with Hmm
    imod Hmask
    imodintro
    isplitl [Hregs Hmem Hmm Hclose]
    · iapply Hclose $$ %(σ.afterLoad cpu req.pa n tvn) %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm
    · iapply swp_ret
      iapply HΦ $$ Hctx Hb
  · rw [hk'.2] at hex'
    exact absurd hex' (by decide)

/-! ## `fence.i`: every byte stamped -/

theorem uxdOwnL_cons (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (D : List PAddr) (mm : BMap) :
    uxdOwnL (GF := GF) ξ K dirty (a :: D) mm ⊣⊢
      iprop((∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ uxdByte ξ K dirty a b) ∗ uxdOwnL ξ K dirty D mm) := by
  unfold uxdOwnL; exact BigSepL.bigSepL_cons

theorem uxd_stampL (σ : MState) (cpu : CPU) (ξ : CtxId) (K K' : Nat) (h1 : σ.tv cpu ≤ K')
    (h2 : ownPub (hartAgent cpu) σ.log ≤ K') (dirty : PAddr → Bool) (mm : BMap) : ∀ D : List PAddr,
    memModel σ ∗ ownCtx cpu ξ ∗ uxdOwnL ξ K dirty D mm ⊢@{IProp GF}
      memModel σ ∗ ownCtx cpu ξ ∗ uxdOwnL ξ K' (fun _ => false) D mm
  | [] => by
    iintro ⟨Hmm, Hctx, _⟩
    iframe Hmm Hctx
    unfold uxdOwnL
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: D => by
    iintro ⟨Hmm, Hctx, HL⟩
    icases (uxdOwnL_cons ξ K dirty a D mm).1 $$ HL with ⟨⟨%b, %hb, Hb⟩, HL⟩
    ihave Hb := uxdByte_forget ξ K dirty a b $$ Hb
    icases uic_ctxByte_stamp σ cpu ξ K' a (DFrac.own 1) b h1 h2 $$ [$Hmm $Hctx $Hb] with ⟨Hmm, Hctx, Hb⟩
    icases uxd_stampL σ cpu ξ K K' h1 h2 dirty mm D $$ [$Hmm $Hctx $HL] with ⟨Hmm, Hctx, HL⟩
    iframe Hmm Hctx
    iapply (uxdOwnL_cons ξ K' (fun _ => false) a D mm).2
    iframe HL
    iexists b
    isplitr
    · ipureintro; exact hb
    rw [uxdByte_clean ξ K' (fun _ => false) a b rfl]
    iexact Hb

/-- **The mint, for a memory with dirty bytes**: at a `fence.i`, every owned
byte becomes stamped at the raised instruction view, and none is dirty. -/
theorem ifenceStep_stamp_uxd (cpu : CPU) (ξ : CtxId) (K : Nat) (DT : List PAddr) (dirty : PAddr → Bool)
    (T : BMap) :
    ⊢ ifenceStep (GF := GF) cpu iprop(ownCtx cpu ξ ∗ uxdOwn ξ K DT dirty T)
        (fun K' => iprop(ownCtx cpu ξ ∗ uxdOwn ξ K' DT (fun _ => false) T)) := by
  unfold ifenceStep uxdOwn
  dsimp only
  iintro %σ %K' %h1 %h2 _ Hmem Hmm ⟨Hctx, %hd, HL⟩
  icases uxd_stampL σ cpu ξ K K' h1 h2 dirty T DT $$ [$Hmm $Hctx $HL] with ⟨Hmm, Hctx, HL⟩
  imodintro
  iframe Hmem Hmm Hctx HL
  ipureintro; exact hd

end own

/-! ## The Iris rule -/

section iris
variable [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} {D : UFoot} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)

/-- The obligation after a walk from `s`: whatever the oracle, the landing
frames give the postcondition. -/
def uxdPost {X : Type} (T : BMap) (dirty : PAddr → Bool) (s : UWSt) (m : SailM X) (Φ : X → IProp GF) :
    IProp GF :=
  iprop(∀ (orc : UOrc) (x : X) (s' : UWSt) (orc' : UOrc), ⌜uxdRun D T dirty orc s m = some (x, s', orc')⌝ -∗
    uFr RF BF s' -∗ Φ x)

theorem uxdPost_step {X : Type} (T : BMap) (dirty : PAddr → Bool) (s s'' : UWSt) (m m' : SailM X)
    (Φ : X → IProp GF) (hstep : ∀ orc', ∃ orc, uxdRun D T dirty orc s m = uxdRun D T dirty orc' s'' m') :
    uxdPost RF BF T dirty s m Φ ⊢ uxdPost RF BF T dirty s'' m' Φ := by
  unfold uxdPost
  iintro HP %orc' %x %s' %orc'' %h Hfr
  obtain ⟨orc, e⟩ := hstep orc'
  iapply HP $$ %orc %x %s' %orc'' %(e.trans h) Hfr

/-- The oracle whose head answers the choice `.bitvector m` with `x`. -/
noncomputable def uxdOrc (o : UOrc) (m : Nat) (x : BitVec m) : UOrc :=
  UOrc.cons ⟨(o 0).reg, fun p => @dite _ (p = .bitvector m) (Classical.propDecidable _) (fun h => h ▸ x)
    (fun _ => (o 0).ch p)⟩ o

@[simp] theorem uxdOrc_tail (o : UOrc) (m : Nat) (x : BitVec m) : (uxdOrc o m x).tail = o := rfl

@[simp] theorem uxdOrc_ch (o : UOrc) (m : Nat) (x : BitVec m) : (uxdOrc o m x 0).ch (.bitvector m) = x := by
  simp only [uxdOrc, UOrc.cons_zero]
  exact dif_pos trivial

/-- **The walk rule.** -/
theorem swp_uxdRun {X : Type} (K : Nat) (DT : List PAddr) (T : BMap) (dirty : PAddr → Bool) (m : SailM X) :
    ∀ (s : UWSt), (∀ orc, (uxdRun D T dirty orc s m).isSome = true) → ∀ Φ : X → IProp GF,
      uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
        uxdPost RF BF T dirty s m (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x)) ⊢ swp cpu m Φ := by
  induction m with
  | pure x =>
    intro s _ Φ
    iintro ⟨Hfr, Htx, _, HP⟩
    iapply swp_ret
    unfold uxdPost
    ihave HΦ := HP $$ %(UOrc.dflt s.rs) %x %s %(UOrc.dflt s.rs) %rfl Hfr
    iapply HΦ $$ Htx
  | impure c k ih =>
    intro s hok Φ
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
          rw [uxdw_text_none D T dirty _ s req k htx hr] at h
          cases h
      -- the walk continues at the machine's answer `w'`, from the oracle that drew it
      have hcont : ∀ w' : BitVec (8 * n),
          (∀ j, j < n → dirty (bAddr req.pa j) = false → nthByte w' j = nthByte w j) →
          (akIfetch req.access_kind = false → w' = w) →
          ∀ o : UOrc, ∃ o₀, uxdRun D T dirty o₀ s (FreeM.impure (.ok (.memRead n vasize req)) k) =
            uxdRun D T dirty o s (k (.Ok (w', none))) := by
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
          exact ⟨o, uxdw_text_some D T dirty o s req k htx w' hw hd⟩
        | true =>
          refine ⟨uxdOrc o (8 * n) w', ?_⟩
          rw [uxdw_text_dirty D T dirty _ s req k htx w hw hd, uxdOrc_tail, uxdOrc_ch,
            bmMerge_eq dirty req.pa n w w' hag]
      show uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
          uxdPost RF BF T dirty s (FreeM.impure (.ok (.memRead n vasize req)) k)
            (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x)) ⊢
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
        have hok' : ∀ o, (uxdRun D T dirty o s (k (.Ok (w', none)))).isSome = true := fun o => by
          obtain ⟨o₀, h0⟩ := hst o
          rw [← h0]; exact hok o₀
        ihave HP := uxdPost_step RF BF T dirty s s _ _ _ hst $$ HP
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w', none)) s hok' Φ
        iframe Hfr Htx Hiv HP
      | false =>
        have hpl : akPlain req.access_kind = true := by simp [akPlain, hif, hex]
        have hst := hcont w (fun _ _ _ => rfl) (fun _ => rfl)
        have hok' : ∀ o, (uxdRun D T dirty o s (k (.Ok (w, none)))).isSome = true := fun o => by
          obtain ⟨o₀, h0⟩ := hst o
          rw [← h0]; exact hok o₀
        ihave HP := uxdPost_step RF BF T dirty s s _ _ _ hst $$ HP
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
        rw [uxdw_node D T dirty orc s c k hc] at h
        revert h
        cases runRW D orc s (FreeM.impure c FreeM.pure) with
        | none => intro h; simp at h
        | some _ => intro _; rfl
      show uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
          uxdPost RF BF T dirty s (FreeM.impure c k) (fun x => iprop(uxdOwn ξ K DT dirty T -∗ Φ x)) ⊢
        swp cpu ((FreeM.impure c FreeM.pure : SailM (ArchSem.Effect.ret c)) >>= k) Φ
      iintro ⟨Hfr, Htx, #Hiv, HP⟩
      iapply swp_bind
      iapply swp_runRW RF BF (FreeM.impure c FreeM.pure) s hok1 (fun v => swp cpu (k v) Φ)
      iframe Hfr
      unfold uPost
      iintro %orc %v %s' %orc' %h HF HB Hc Hr
      have hre : ∀ o, ∃ orc₀, uxdRun D T dirty orc₀ s (FreeM.impure c k) = uxdRun D T dirty o s' (k v) :=
        fun o => by
          obtain ⟨orc₀, h0⟩ := uft_runRW_node_shift D c s orc v s' orc' h o
          refine ⟨orc₀, ?_⟩
          rw [uxdw_node D T dirty orc₀ s c k hc, h0]; rfl
      have hok' : ∀ o, (uxdRun D T dirty o s' (k v)).isSome = true := fun o => by
        obtain ⟨orc₀, h0⟩ := hre o
        rw [← h0]; exact hok orc₀
      iapply ih v s' hok' Φ
      isplitl [HF HB Hc Hr]
      · unfold uFr; iframe
      iframe Htx Hiv
      iapply uxdPost_step RF BF T dirty s s' _ _ _ hre $$ HP

/-- **The walk rule, with a described landing.** -/
theorem swp_uxdRun_of {X : Type} (K : Nat) (DT : List PAddr) (T : BMap) (dirty : PAddr → Bool) (m : SailM X)
    (s : UWSt) (Pd : X → UWSt → Prop)
    (hw : ∀ orc, ∃ x s' orc', uxdRun D T dirty orc s m = some (x, s', orc') ∧ Pd x s') (Φ : X → IProp GF) :
    uFr RF BF s ∗ uxdOwn ξ K DT dirty T ∗ iviewLb cpu K ∗
      (∀ x s', ⌜Pd x s'⌝ -∗ uFr RF BF s' -∗ uxdOwn ξ K DT dirty T -∗ Φ x) ⊢ swp cpu m Φ := by
  iintro ⟨Hfr, Htx, #Hiv, HΦ⟩
  have hok : ∀ orc, (uxdRun D T dirty orc s m).isSome = true := fun orc => by
    obtain ⟨x, s', orc', h, -⟩ := hw orc
    rw [h]; rfl
  iapply swp_uxdRun RF BF K DT T dirty m s hok Φ
  iframe Hfr Htx Hiv
  unfold uxdPost
  iintro %orc %x %s' %orc' %h Hfr
  obtain ⟨x0, s0, o0, h0, hP⟩ := hw orc
  rw [h0] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, -⟩ := h
  iapply HΦ $$ %x0 %s0 %hP Hfr

end iris

end MachCSL
