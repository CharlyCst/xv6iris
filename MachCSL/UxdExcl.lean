/-
MachCSL: **exclusive reads from `uxdOwn` bytes** without disturbing clean stamps
(`uxn_uxdBytes_exclReadAU`: a copy of Miralis `FwAtomics/Base.lean`'s `uxdBytes_exclReadAU`, renamed
to avoid a clash until Miralis drops its copy; used by the native walker).
-/
import MachCSL.URunDSwp
import MachCSL.WpAtomic

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

theorem uxn_uxdByte_hist_acc (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (a : PAddr) (v : BitVec 8) :
    uxdByte (GF := GF) ξ K dirty a v ⊢
      ∃ (e : HEnt) (H : Hist), a ↦ₕ (e :: H) ∗ ⌜e.v = v⌝ ∗
        (a ↦ₕ (e :: H) -∗ uxdByte ξ K dirty a v) := by
  cases hd : dirty a
  · rw [uxdByte_clean ξ K dirty a v hd]
    unfold ctxByteX
    iintro ⟨%e, %H, Hpt, %hev, #Hkey, %htK⟩
    iexists e, H
    iframe Hpt
    isplitr; · ipureintro; exact hev
    iintro Hpt
    iexists e, H
    iframe Hpt Hkey
    ipureintro; exact ⟨hev, htK⟩
  · rw [uxdByte_dirty ξ K dirty a v hd]
    iintro Hb
    icases ctxByte_cases ξ a (DFrac.own 1) v $$ Hb with ⟨%e, %H, Hpt, %hev, #Hkey⟩
    iexists e, H
    iframe Hpt
    isplitr; · ipureintro; exact hev
    iintro Hpt
    rw [← hev]
    iapply ctxByte_intro ξ a (DFrac.own 1) e H $$ [Hpt]
    iframe Hpt Hkey

theorem uxn_uxdBytes_hist_acc (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr)
    (bs : Nat → BitVec 8) : ∀ n : Nat,
    ([∗list] j ∈ List.range n, uxdByte (GF := GF) ξ K dirty (pa + BitVec.ofNat 64 j) (bs j)) ⊢
      ∃ Hs : Nat → Hist, ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ Hs j) ∗
        ⌜∀ j, j < n → Hs j ≠ [] ∧ (Hs j).head?.map HEnt.v = some (bs j)⌝ ∗
        (([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ Hs j) -∗
          [∗list] j ∈ List.range n, uxdByte ξ K dirty (pa + BitVec.ofNat 64 j) (bs j))
  | 0 => by
    iintro _
    iexists (fun _ => [])
    isplitl []
    · simp only [List.range_zero, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
    isplit
    · ipureintro; intro j hj; omega
    · iintro _
      simp only [List.range_zero, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  | n + 1 => by
    rw [List.range_succ]
    iintro Hb
    icases BigSepL.bigSepL_snoc.1 $$ Hb with ⟨Hb1, Hb2⟩
    icases uxn_uxdBytes_hist_acc ξ K dirty pa bs n $$ Hb1 with ⟨%Hs1, H1, %h1, W1⟩
    icases uxn_uxdByte_hist_acc ξ K dirty _ _ $$ Hb2 with ⟨%e, %H, Hpt, %he, W2⟩
    have hmem : ∀ {k x : Nat}, (List.range n)[k]? = some x → x ≠ n := by
      intro k x hk hx
      have := List.mem_of_getElem? hk
      rw [List.mem_range] at this
      omega
    iexists (fun j => if j = n then e :: H else Hs1 j)
    have heq : ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ
        (fun j => if j = n then e :: H else Hs1 j) j) =
        ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ Hs1 j : IProp GF) := by
      apply BigSepL.bigSepL_eq
      intro k x hk
      simp only [hmem hk, if_false]
    isplitl [H1 Hpt]
    · iapply BigSepL.bigSepL_snoc.2
      simp only [if_true]
      rw [heq]
      iframe H1 Hpt
    isplit
    · ipureintro
      intro j hj
      by_cases hjn : j = n
      · subst hjn; simp [he]
      · simp only [hjn, if_false]; exact h1 j (by omega)
    · iintro Hh
      icases BigSepL.bigSepL_snoc.1 $$ Hh with ⟨Hh1, Hh2⟩
      simp only [if_true]
      rw [heq]
      iapply BigSepL.bigSepL_snoc.2
      isplitl [Hh1 W1]
      · iapply W1 $$ Hh1
      · iapply W2 $$ Hh2

/-- Exclusive read atomic update from `uxdBytes`, preserving clean `ctxByteX` timestamps intact. -/
theorem uxn_uxdBytes_exclReadAU (ξ : CtxId) (K : Nat) (dirty : PAddr → Bool) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) :
    uxdBytes (GF := GF) ξ K dirty pa n w ⊢
      exclReadAU pa n (fun w0 => iprop(⌜w0 = w⌝ ∗ uxdBytes ξ K dirty pa n w)) := by
  unfold uxdBytes exclReadAU histBytes
  iintro H
  icases uxn_uxdBytes_hist_acc ξ K dirty pa (nthByte w) n $$ H with ⟨%Hs, Hh, %h, W⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists (fun _ => DFrac.own 1), Hs
  iframe Hh
  isplit
  · ipureintro; exact fun j hj => (h j hj).1
  inext
  iintro %w0 %hheads Hh
  imod Hmask
  imodintro
  isplit
  · ipureintro
    apply bv_eq_of_bytes
    intro j hj
    have h1 := hheads j hj
    have h2 := (h j hj).2
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  · iapply W $$ Hh

end MachCSL
