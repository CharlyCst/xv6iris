/-
MachCSL: **the native walk rule** (`swp_uxnRun`) and **one machine step of a native hart**
(`wpLoop_uxnStep`): rule R-native. See `MachCSL/UNative.lean` for the walker.
-/
import MachCSL.UNative

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} {D : UFoot} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)
variable (B : Privilege → Bool)

/-- **The native walk rule.** From the walker frames and the owned memory of `s` and the
instruction view, a computation every oracle's native walk runs through (to its end or to an exit
node) satisfies `swp` with postcondition `Φ`, given the obligation at every landing and at every
exit (the `swp` of the exit node and its continuation). -/
theorem swp_uxnRun (hRP : URegFramePriv RF) (hq : QuietPriv (GF := GF) cpu B)
    {X : Type} (K : Nat) (DT : List PAddr) (m : SailM X) :
    ∀ (s : NSt), (∀ orc, (uxnRun D B orc s m).isSome = true) → ∀ Φ : X → IProp GF,
      nFr RF BF K DT s ∗ iviewLb cpu K ∗
        uxnPost RF BF B K DT s m Φ
          (fun p k => swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) Φ) ⊢
        swp cpu m Φ := by
  induction m with
  | pure x =>
    intro s _ Φ
    iintro ⟨Hfr, _, HP⟩
    iapply swp_ret
    unfold uxnPost
    ihave HΦ := HP $$ %(UOrc.dflt s.u.rs) %(NRes.done x s (UOrc.dflt s.u.rs)) %rfl
    iapply HΦ $$ Hfr
  | impure c k ih =>
    intro s hok Φ
    cases hown : nOwn c with
    | false =>
      have hok1 : ∀ orc, (runRW D orc s.u (FreeM.impure c FreeM.pure)).isSome = true := fun orc => by
        have h := hok orc
        rw [uxnw_node D B orc s c k hown] at h
        revert h
        cases runRW D orc s.u (FreeM.impure c FreeM.pure) with
        | none => intro h; simp at h
        | some _ => intro _; rfl
      show nFr RF BF K DT s ∗ iviewLb cpu K ∗
          uxnPost RF BF B K DT s (FreeM.impure c k) Φ
            (fun p k => swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) Φ) ⊢
        swp cpu ((FreeM.impure c FreeM.pure : SailM (ArchSem.Effect.ret c)) >>= k) Φ
      unfold nFr
      iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
      iapply swp_bind
      iapply swp_runRW RF BF (FreeM.impure c FreeM.pure) s.u hok1 (fun v => swp cpu (k v) Φ)
      iframe Hfr
      unfold uPost
      iintro %orc %v %u' %orc' %h HF HB Hc Hr
      have hre : ∀ o, ∃ orc₀, uxnRun D B orc₀ s (FreeM.impure c k) =
          uxnRun D B o { s with u := u' } (k v) :=
        fun o => by
          obtain ⟨orc₀, h0⟩ := uft_runRW_node_shift D c s.u orc v u' orc' h o
          refine ⟨orc₀, ?_⟩
          rw [uxnw_node D B orc₀ s c k hown, h0]; rfl
      iapply ih v { s with u := u' } (uxn_hok_step B s _ _ _ hok hre) Φ
      unfold nFr
      iframe Hiv
      isplitl [HF HB Hc Hr Htx]
      · isplitr [Htx]
        · unfold uFr; iframe
        · iexact Htx
      iapply uxnPost_step RF BF B K DT s _ _ _ _ _ hre $$ HP
    | true =>
    rcases c with e | op
    · simp [nOwn] at hown
    cases op with
    | regWrite r p =>
      by_cases hr : r = .cur_privilege
      rotate_left
      · cases r <;> first | exact absurd rfl hr | simp [nOwn] at hown
      subst hr
      cases h0 : B (s.u.file .cur_privilege) with
      | false =>
        have h := hok (UOrc.dflt s.u.rs)
        rw [uxnw_priv_out D B _ s p k h0] at h
        cases h
      | true =>
      cases h1 : B p with
      | false =>
        iintro ⟨Hfr, _, HP⟩
        unfold uxnPost
        ihave HΨ := HP $$ %(UOrc.dflt s.u.rs) %(NRes.exit p k s (UOrc.dflt s.u.rs))
          %(uxnw_priv_exit D B _ s p k h0 h1)
        iapply HΨ $$ Hfr
      | true =>
        have hst : ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s
            (FreeM.impure (.ok (.regWrite .cur_privilege p)) k) =
            uxnRun D B o { s with u := { s.u with pin := s.u.pin.set .cur_privilege p } } (k ()) :=
          fun o => ⟨o, uxnw_priv_quiet D B o s p k h0 h1⟩
        have e : (FreeM.impure (.ok (.regWrite .cur_privilege p)) k : SailM X) =
            (writeReg Register.cur_privilege p >>= k) := rfl
        unfold nFr
        iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
        ihave HP := uxnPost_step RF BF B K DT s _ _ _ _ _ hst $$ HP
        rw [e]
        unfold uFr
        icases Hfr with ⟨HF, HB, Hc, Hr⟩
        icases hRP s.u.file $$ HF with ⟨Hpc, Hupd⟩
        iapply swp_bind
        iapply hq (s.u.file .cur_privilege) p (fun u => swp cpu (k u) Φ) h0 h1
        iframe Hpc
        inext
        iintro Hpc
        ihave HF := Hupd $$ %p Hpc
        iapply ih () _ (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr uFr
        rw [UWSt.file_setPin]
        iframe
        iexact Hiv
    | memRead n vasize req =>
      have h0 := hok (UOrc.dflt s.u.rs)
      rw [uxnw_read] at h0
      by_cases hn : n < 2 ^ 64
      rotate_left
      · simp [hn] at h0
      simp only [hn, if_true] at h0
      obtain ⟨w, hw⟩ : ∃ w, bmRead s.T req.pa n = some w := by
        cases hr : bmRead s.T req.pa n with
        | some w => exact ⟨w, rfl⟩
        | none => rw [hr] at h0; cases h0
      have e : (FreeM.impure (.ok (.memRead n vasize req)) k : SailM X) =
          (ConcurrencyInterfaceV1.sail_mem_read req >>= k) := rfl
      cases hif : akIfetch req.access_kind with
      | true =>
        have hex : akExcl req.access_kind = false := by
          revert hif; cases req.access_kind <;> simp [akIfetch, akExcl]
        have hcont : ∀ w' : BitVec (8 * n),
            (∀ j, j < n → s.dirty (bAddr req.pa j) = false → nthByte w' j = nthByte w j) →
            ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s (FreeM.impure (.ok (.memRead n vasize req)) k) =
              uxnRun D B o s (k (.Ok (w', none))) := by
          intro w' hag o
          cases hd : winDirty s.dirty req.pa n with
          | false =>
            have hww : w' = w :=
              bv_eq_of_bytes _ _ (fun j hj => hag j hj (winDirty_false hd j hj))
            subst hww
            refine ⟨o, ?_⟩
            rw [uxnw_read, if_pos hn, hw]
            simp only [hif, hd, hex, Bool.and_false, Bool.false_eq_true, if_false]
          | true =>
            refine ⟨uxdOrc o (8 * n) w', ?_⟩
            rw [uxnw_read, if_pos hn, hw]
            simp only [hif, hd, Bool.and_self, if_true]
            rw [uxdOrc_tail, uxdOrc_ch, bmMerge_eq s.dirty req.pa n w w' hag]
        unfold nFr
        iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
        icases uxdOwn_acc ξ K DT s.dirty s.T req.pa n w hn hw $$ Htx with ⟨Hb, Hcl⟩
        rw [e]
        iapply swp_bind
        iapply swp_sail_mem_read_ifetch_d cpu req ξ K s.dirty w hif (fun v => swp cpu (k v) Φ)
        iframe Hb Hiv
        inext
        iintro %w' %hag Hb
        have hst := hcont w' hag
        have hst' : ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s (ConcurrencyInterfaceV1.sail_mem_read req >>= k) =
            uxnRun D B o s (k (.Ok (w', none))) := by rw [← e]; exact hst
        ihave HP := uxnPost_step RF BF B K DT s s _ _ _ _ hst' $$ HP
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w', none)) s (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr
        iframe Hfr Htx Hiv HP
      | false =>
      cases hex : akExcl req.access_kind with
      | false =>
        have hpl : akPlain req.access_kind = true := by simp [akPlain, hif, hex]
        have hst : ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s (FreeM.impure (.ok (.memRead n vasize req)) k) =
            uxnRun D B o s (k (.Ok (w, none))) := fun o => ⟨o, by
          rw [uxnw_read, if_pos hn, hw]
          simp only [hif, hex, Bool.false_and, Bool.false_eq_true, if_false]⟩
        unfold nFr
        iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
        icases uxdOwn_acc ξ K DT s.dirty s.T req.pa n w hn hw $$ Htx with ⟨Hb, Hcl⟩
        ihave HP := uxnPost_step RF BF B K DT s s _ _ _ _ hst $$ HP
        rw [e]
        unfold uFr
        icases Hfr with ⟨HF, HB, Hc, Hr⟩
        iapply swp_bind
        iapply swp_sail_mem_read_plain_d cpu req ξ K s.dirty w hpl (fun v => swp cpu (k v) Φ)
        iframe Hc Hb
        inext
        iintro Hc Hb
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w, none)) s (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr uFr
        iframe
        iexact Hiv
      | true =>
        let s' : NSt := { s with u := { s.u with rv := true } }
        have hst : ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s (FreeM.impure (.ok (.memRead n vasize req)) k) =
            uxnRun D B o s' (k (.Ok (w, none))) := fun o => ⟨o, by
          rw [uxnw_read, if_pos hn, hw]
          simp only [hif, hex, Bool.false_and, Bool.false_eq_true, if_false, if_true, s']⟩
        unfold nFr
        iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
        icases uxdOwn_acc ξ K DT s.dirty s.T req.pa n w hn hw $$ Htx with ⟨Hb, Hcl⟩
        ihave HP := uxnPost_step RF BF B K DT s s' _ _ _ _ hst $$ HP
        rw [e]
        unfold uFr uResvTok
        icases Hfr with ⟨HF, HB, Hc, %r, Hfrag⟩
        iapply swp_bind
        iapply swp_sail_mem_read_excl_au cpu req (akAcq req.access_kind) hex rfl hn r
          (fun v => swp cpu (k v) Φ)
        iframe Hfrag
        ihave Hau := uxn_uxdBytes_exclReadAU ξ K s.dirty req.pa n w $$ Hb
        iapply exclReadAU_wand req.pa n _ _ $$ Hau
        inext
        iintro %w1 ⟨%hw1, Hb⟩ Hfrag
        subst hw1
        ihave Htx := Hcl $$ Hb
        iapply ih (.Ok (w1, none)) s' (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr uFr
        dsimp only [s']
        rw [show ({ s.u with rv := true } : UWSt).file = s.u.file from rfl]
        iframe HF HB Hc Htx Hiv HP
        iapply uResvTok_of cpu true _ _ $$ Hfrag
    | memWrite n vasize req =>
      have h0 := hok (UOrc.dflt s.u.rs)
      rw [uxnw_write] at h0
      by_cases hn : n < 2 ^ 64
      rotate_left
      · simp [hn] at h0
      simp only [hn, if_true] at h0
      cases hv : req.value with
      | none => rw [hv] at h0; cases h0
      | some w' =>
      rw [hv] at h0
      cases ho : bmOwned s.T req.pa n with
      | false => simp [ho] at h0
      | true =>
      obtain ⟨w0, hw0⟩ := bmRead_of_owned s.T req.pa n ho
      let s' : NSt := ⟨{ s.u with rv := false }, bmWrite s.T req.pa n w', dirtyAdd s.dirty req.pa n⟩
      have hst : ∀ o : UOrc, ∃ o₀, uxnRun D B o₀ s (FreeM.impure (.ok (.memWrite n vasize req)) k) =
          uxnRun D B o s' (k (.Ok (some true))) := fun o => ⟨o, by
        rw [uxnw_write, if_pos hn, hv]
        simp only [ho, if_true, s']⟩
      have e : (FreeM.impure (.ok (.memWrite n vasize req)) k : SailM X) =
          (ConcurrencyInterfaceV1.sail_mem_write req >>= k) := rfl
      unfold nFr
      iintro ⟨⟨Hfr, Htx⟩, #Hiv, HP⟩
      icases uxdOwn_store ξ K DT s.dirty s.T req.pa n w0 hn hw0 $$ Htx with ⟨Hb, Hback⟩
      ihave HP := uxnPost_step RF BF B K DT s s' _ _ _ _ hst $$ HP
      rw [e]
      cases hex : akExcl req.access_kind with
      | false =>
        unfold uFr
        icases Hfr with ⟨HF, HB, Hc, Hr⟩
        ihave Htok := uResvTok_ctxTok cpu ξ s.u.rv $$ [$Hc $Hr]
        iapply swp_bind
        iapply swp_sail_mem_write_plain cpu req ξ w0 w' hv hex (fun v => swp cpu (k v) Φ)
        iframe Htok Hb
        inext
        iintro Htok Hb
        ihave Htx := Hback $$ %w' Hb
        icases ctxTok_uResvTok cpu ξ $$ Htok with ⟨Hc, Hr⟩
        iapply ih (.Ok (some true)) s' (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr uFr
        dsimp only [s', dirtyAdd]
        rw [show ({ s.u with rv := false } : UWSt).file = s.u.file from rfl]
        iframe HF HB Hc Hr Hiv HP
        iexact Htx
      | true =>
        unfold uFr uResvTok
        icases Hfr with ⟨HF, HB, Hc, %r, Hfrag⟩
        iapply swp_bind
        iapply swp_sail_mem_write_excl_ctx cpu req ξ r w0 w' hv hex (fun v => swp cpu (k v) Φ)
        iframe Hc Hfrag Hb
        inext
        iintro Hc Hfrag Hb
        ihave Htx := Hback $$ %w' Hb
        iapply ih (.Ok (some true)) s' (uxn_hok_step B s _ _ _ hok hst) Φ
        unfold nFr uFr
        dsimp only [s', dirtyAdd]
        rw [show ({ s.u with rv := false } : UWSt).file = s.u.file from rfl]
        iframe HF HB Hc Hiv HP
        isplitr [Htx]
        · iapply uResvTok_of cpu false none false $$ Hfrag
        · iexact Htx
    | _ => simp [nOwn] at hown

/-- **One machine step of a native hart** (rule R-native): the whole cycle `try_step 0 false` is one
native walk, then the optional clock tick. At a landing, the client continues the loop; at an
exit (a trap into M-mode), the client runs the exit node and the rest of the cycle with the
boundary and M-mode rules. -/
theorem wpLoop_uxnStep [BndTriv (hlc := hlc) (GF := GF)] (hRP : URegFramePriv RF)
    (hq : QuietPriv (GF := GF) cpu B) (K : Nat) (DT : List PAddr) (s : NSt)
    (hok : ∀ orc, (uxnRun D B orc s (try_step 0 false)).isSome = true) :
    nFr RF BF K DT s ∗ iviewLb cpu K ∗
      ▷ (∀ tick : Bool,
        uxnPost RF BF B K DT s (try_step 0 false)
          (fun _ => swp cpu (if tick then tick_clock () else pure ()) (fun _ => wpLoop cpu))
          (fun p k => swp cpu (FreeM.impure (.ok (.regWrite .cur_privilege p)) k)
              (fun _ => swp cpu (if tick then tick_clock () else pure ()) (fun _ => wpLoop cpu))))
    ⊢ wpLoop cpu := by
  iintro ⟨Hfr, #Hiv, HK⟩
  iapply wpLoop_ucStep
  iintro %tick
  inext
  ispecialize HK $$ %tick
  iapply swp_uxnRun RF BF B hRP hq K DT (try_step 0 false) s hok
  iframe Hfr Hiv HK

end iris

end MachCSL
