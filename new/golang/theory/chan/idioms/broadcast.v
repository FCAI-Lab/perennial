From iris.algebra.lib Require Import dfrac_agree.
Require Import New.golang.theory.
Require Import New.proof.proof_prelude.

(** A pattern for channel usage: a channel that never has anything sent, and is
    only closed at some point. Closing broadcasts a persistent proposition to
    all readers. *)

Record broadcast_internal_names :=
  { done_gn : gname }.

Module broadcast.
Inductive t := Pending | Done | Unknown.
End broadcast.
Import broadcast.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!go.Semantics}.

(* Note: could make the namespace be user-chosen *)
#[local] Definition is_broadcast_chan_internal (ch : chan.t) γ γch (Q : iProp Σ) : iProp Σ :=
  "#His_ch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ (st : chanstate.t unit),
        "Hch" ∷ own_chan γ unit st ∗
        "Hs" ∷ (match st with
                | chanstate.Idle
                | chanstate.RcvPending =>
                    own γch.(done_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
                | chanstate.Closed [] =>
                    □ Q ∗ own γch.(done_gn) (to_dfrac_agree DfracDiscarded true)
                | _ => False
                end)
    ).

Definition own_broadcast_chan (ch : chan.t) γ (Q : iProp Σ) (st : broadcast.t) : iProp Σ :=
  ∃ γch,
  "#Hinv" ∷ is_broadcast_chan_internal ch γ γch Q ∗
  "Hown" ∷ (match st with
            | Pending => own γch.(done_gn) (to_dfrac_agree (DfracOwn (1/2)) false)
            | Done => own γch.(done_gn) (to_dfrac_agree DfracDiscarded true)
            | Unknown => True
            end).

#[global] Opaque own_broadcast_chan.
#[local] Transparent own_broadcast_chan.
#[global] Instance own_broadcast_chan_Unknown_pers ch γch P :
  Persistent (own_broadcast_chan ch γch P Unknown) := _.
#[global] Instance own_broadcast_chan_Done_pers ch γch P :
  Persistent (own_broadcast_chan ch γch P Done) := _.

Lemma broadcast_chan_done ch γ Q :
  £ 1 -∗ own_broadcast_chan ch γ Q Done ={⊤}=∗
  Q.
Proof.
  iIntros "Hlc". iNamed 1. iNamed "Hinv". iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  destruct st; try by iExFalso; simpl.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
  - destruct drain; try done.
    iClear "Hown". iDestruct "Hs" as "[#? ?]". iMod ("Hclose" with "[-]"). { iFrame. iFrame "∗#". }
    iModIntro. iFrame "#".
Qed.

Lemma broadcast_chan_receive ch γ Q Φ cl :
  own_broadcast_chan ch γ Q cl -∗
  (□Q ∗ own_broadcast_chan ch γ Q Done -∗ Φ () false) -∗
  recv_au γ unit Φ.
Proof.
  iNamed 1. iIntros "HΦ".  iNamed "Hinv".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame.
  destruct st; try done.
  - iIntros "Hch". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#%". }
    iModIntro.
    iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
    iNext. iNamed "Hi". iFrame. destruct st; try done.
    destruct drain; try done. iIntros "Hch". iDestruct "Hs" as "[#? #?]".
    iMod "Hmask" as "_". iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#". }
    iApply "HΦ". iModIntro. iFrame "∗#".
  - destruct drain; try done. iIntros "Hch".
    iDestruct "Hs" as "[#? #?]". iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ]"). { iFrame "∗#%". }
    iApply "HΦ". iModIntro. iFrame "∗#".
Qed.

Lemma own_broadcast_chan_nonblocking_receive ch γ Q Φ Φnotready cl :
  own_broadcast_chan ch γ Q cl -∗
  (match cl with
   | Unknown | Done => (own_broadcast_chan ch γ Q Done -∗ Φ () false)
   | _ => True
   end ∧
   match cl with
   | Unknown | Pending => (own_broadcast_chan ch γ Q cl -∗ Φnotready)
   | _ => True
   end)
  -∗
  nonblocking_recv_au_alt γ unit Φ Φnotready.
Proof.
  iNamed 1. iNamed "Hinv". subst.
  iIntros "HΦ".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct st; try done.
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iSpecialize ("HΦ" with "[$]"). iFrame. iMod ("Hclose" with "[-]"); last done. iFrame "∗#%".
  - iIntros "Hch". iMod "Hmask". destruct cl.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iRight in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iMod ("Hclose" with "[-]"); last done.
      iFrame "∗#%".
  - destruct drain; try done. iDestruct "Hs" as "[#? #Hs]". destruct cl.
    + iCombine "Hs Hown" gives %Hbad%dfrac_agree_op_valid. naive_solver.
    + iDestruct ("HΦ" with "[$]") as "$". iIntros "Hch".
      iMod "Hmask" as "_". iMod ("Hclose" with "[-]"); last done. iFrame "∗#".
    + iLeft in "HΦ". iDestruct ("HΦ" with "[$]") as "$". iIntros "Hch".
      iMod "Hmask" as "_". iMod ("Hclose" with "[-]"); last done. iFrame "∗#".
Qed.

Lemma broadcast_close_au ch γch Q Φ :
  own_broadcast_chan ch γch Q Pending -∗
  □ Q -∗
  ▷ (own_broadcast_chan ch γch Q Done -∗ Φ) -∗
  close_au γch unit Φ.
Proof.
  iNamed 1. iIntros "#HQ HΦ". iNamed "Hinv".
  iInv "Hinv" as "Hi" "Hclose". iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask"].
  iNext. iNamed "Hi". iFrame. destruct st; try done.
  - iIntros "Hch". iMod "Hmask" as "_".
    iCombine "Hown Hs" as "Hown". rewrite -dfrac_agree_op dfrac_op_own Qp.half_half.
    iMod (own_update  _ _ (to_dfrac_agree DfracDiscarded true) with "Hown") as "#H".
    { apply cmra_update_exclusive. done. }
    iMod ("Hclose" with "[-HΦ]").
    { iFrame "∗#%". }
    iModIntro. iApply "HΦ". iFrame "∗#".
  - destruct drain; try done. iRight in "Hs".
    iCombine "Hown Hs" gives %Hbad%dfrac_agree_op_valid. exfalso. naive_solver.
Qed.

Lemma wp_broadcast_chan_close `[!ty ↓u go.ChannelType dir (go.StructType [])] ch γch Q :
  {{{ own_broadcast_chan ch γch Q Pending ∗ □ Q }}}
  #(functions go.close [ty]) #ch
  {{{ RET #(); own_broadcast_chan ch γch Q Done }}}.
Proof.
  wp_start_folded as "[Hown #HQ]".
  iAssert (is_chan ch γch unit) as "#His".
  { iNamed "Hown". iNamed "Hinv". iFrame "#". }
  wp_apply (chan.wp_close with "His"). iIntros "Hlcs".
  iApply (broadcast_close_au with "Hown HQ [HΦ]").
  iNext. iIntros "Hclosed". by iApply "HΦ".
Qed.

Lemma alloc_broadcast_chan {E} Q γ ch :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={E}=∗
  own_broadcast_chan ch γ Q Pending.
Proof.
  iIntros "#? Hch".
  iMod (own_alloc
          ((to_dfrac_agree (DfracOwn (1/2)) false) ⋅ (to_dfrac_agree (DfracOwn (1/2)) false))
       ) as (tok_gn) "Htok".
  { rewrite -dfrac_agree_op //. }
  iDestruct "Htok" as "[Htok Htok2]".
  iAssert (|={E}=> is_broadcast_chan_internal ch γ ltac:(econstructor) Q)%I with "[-Htok]" as ">#H".
  2:{ iFrame "∗#". simpl. iFrame. done. }
  simpl. iFrame.
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame. iFrame.
Qed.

Lemma own_broadcast_chan_Unknown ch γ Q cl :
  own_broadcast_chan ch γ Q cl -∗
  own_broadcast_chan ch γ Q Unknown.
Proof. iNamed 1. iFrame "#". Qed.

Lemma own_broadcast_chan_is_chan ch γ Q cl :
  own_broadcast_chan ch γ Q cl -∗
  is_chan ch γ unit.
Proof. iNamed 1. iNamed "Hinv". iFrame "#". Qed.

End proof.
