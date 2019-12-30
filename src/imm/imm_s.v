(******************************************************************************)
(** * Weaker IMM model for Promise->IMM    *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_bob.
Require Import imm_s_ppo.
Require Import imm_s_hb_hb.
Require Import imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(imm_s_hb.hb).
Notation "'sw'" := G.(imm_s_hb.sw).

Notation "'bob'" := G.(bob).
Notation "'ppo'" := G.(imm_s_ppo.ppo).
Notation "'ar_int'" := G.(imm_s_ppo.ar_int).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition psc := ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘.

Definition scb := sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪
                     (hb ∩ same_loc) ∪ co ∪ fr.
Definition psc_base := ⦗ Sc ⦘ ⨾ (⦗ F ⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗ F ⦘)^? ⨾ ⦗ Sc ⦘.
Definition psc_f    := ⦗F∩₁Sc⦘ ⨾  hb ⨾ (eco ⨾ hb)^? ⨾ ⦗F∩₁Sc⦘.

Definition ar sc := sc ∪ rfe ∪ ar_int.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Record wf_sc sc :=
  { wf_scE : sc ≡ ⦗E⦘ ⨾ sc ⨾ ⦗E⦘ ;
    wf_scD : sc ≡ ⦗F∩₁Sc⦘ ⨾ sc ⨾ ⦗F∩₁Sc⦘ ;
    sc_trans : transitive sc ;
    wf_sc_total : is_total (E ∩₁ F ∩₁ Sc) sc ;
    sc_irr : irreflexive sc ;
  }.

Definition acyc_ext sc := acyclic (ar sc).

Definition coh_sc sc := irreflexive (sc ⨾ hb ⨾ (eco ⨾ hb)^?).

Definition imm_consistent sc := 
  ⟪ Wf_sc : wf_sc sc ⟫ /\
  ⟪ Csc   : coh_sc sc ⟫ /\
  ⟪ Comp  : complete G ⟫ /\
  ⟪ Cint  : coherence G ⟫ /\
  ⟪ Cext  : acyc_ext sc ⟫ /\
  ⟪ Cat   : rmw_atomicity G ⟫.

Definition imm_psc_consistent sc :=
  ⟪ IC   : imm_consistent sc ⟫ /\
  ⟪ Cpsc : acyclic (psc_f ∪ psc_base) ⟫.

Hypothesis WF : Wf G.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.

Section SC.

Variable sc : relation actid.

Hypothesis WF_SC : wf_sc sc.
Hypothesis IMMCON : imm_consistent sc.
Hypothesis CSC : coh_sc sc.
Hypothesis ACYC_EXT : acyc_ext sc.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_pscE : psc ≡ ⦗E⦘ ⨾ psc ⨾ ⦗E⦘.
Proof using WF.
split; [|basic_solver].
unfold psc; rewrite (wf_hbE WF) at 1 2.
basic_solver 42.
Qed.

Lemma wf_arE : ar sc ≡ ⦗E⦘ ⨾ ar sc ⨾ ⦗E⦘.
Proof using WF WF_SC.
split; [|basic_solver].
unfold ar.
rewrite (wf_scE WF_SC), (wf_ar_intE WF), (wf_rfeE WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_pscD : psc ≡ ⦗F∩₁Sc⦘ ⨾ psc ⨾ ⦗F∩₁Sc⦘.
Proof using.
split; [|basic_solver].
unfold psc; basic_solver 42.
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma no_psc_to_init : psc ≡ psc ⨾  ⦗fun x => ~ is_init x⦘.
Proof using WF.
split; [|basic_solver].
rewrite wf_pscD at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma no_sc_to_init :
 sc ≡ sc ⨾  ⦗fun x => ~ is_init x⦘.
Proof using WF WF_SC.
split; [|basic_solver].
rewrite wf_scD at 1; try done.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma F_sc_ar_F_sc :
  ⦗F ∩₁ Sc⦘ ⨾ (ar sc)⁺ ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof using WF WF_SC ACYC_EXT.
rewrite wf_arE; try done.
rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
unfold ar.
destruct WF_SC.
unfolder; ins; desf.
eapply tot_ex; eauto; try basic_solver.
intro; eapply ACYC_EXT.
eapply t_trans; unfold ar; [basic_solver| apply t_step; basic_solver].
intro; eapply ACYC_EXT; unfold ar; basic_solver.
Qed.

(* TODO: move to imm_s_ppo. *)
Lemma rmw_in_ar_int : rmw ⊆ ar_int.
Proof using WF.
  unfold imm_s_ppo.ar_int.
  rewrite WF.(rmw_in_ppo). eauto with hahn.
Qed.

(* TODO: move to imm_s_ppo. *)
Lemma rfe_rmw_in_rfe_ar_int_ct : rfe ⨾ rmw ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  rewrite rmw_in_ar_int.
  arewrite (ar_int ⊆ rfe ∪ ar_int) at 1.
  arewrite (rfe ⊆ rfe ∪ ar_int) at 1.
  do 2 (rewrite ct_begin; rewrite rtE).
  rewrite <- ct_step. basic_solver 10.
Qed.

(* TODO: move to imm_s_ppo. *)
Lemma ar_int_rfe_rfrmw_in_ar_int_rfe_ct : (rfe ∪ ar_int) ;; rf ;; rmw ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  remember (rfe ∪ ar_int) as ax.
  assert (sb ;; sb ⊆ sb) as AA.
  { apply transitiveI. apply sb_trans. }
  
  assert (rfi ;; rmw ⊆ sb) as BB.
  { arewrite (rfi ⊆ sb). by rewrite rmw_in_sb. }

  rewrite rfi_union_rfe.
  rewrite seq_union_l, seq_union_r.
  unionL.
  2: { rewrite rfe_rmw_in_rfe_ar_int_ct.
       arewrite (ax ⊆ ax^?) at 1. subst ax. relsf. }
  subst ax.
  rewrite !seq_union_l.
  unionL.
  { rewrite (dom_l WF.(wf_rfiD)).
    rewrite (dom_r WF.(wf_rfeD)).
    type_solver. }
  unfold imm_s_ppo.ar_int at 1.
  rewrite !seq_union_l.
  unionL.
  5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
  3: { rewrite WF.(wf_detourD).
       rewrite WF.(wf_rfiD). type_solver. }
  { unfold imm_bob.bob at 1.
    rewrite !seq_union_l, !seqA.
    unionL.
    2: { rewrite BB, AA.
         arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
         rewrite bob_in_ar_int. rewrite <- ct_step. eauto with hahn. }
    rewrite fwbob_rfi_rmw_in_fwbob; auto.
    rewrite fwbob_in_bob. rewrite bob_in_ar_int. eauto with hahn. }
  { rewrite WF.(rmw_in_ppo), ppo_rfi_ppo. rewrite <- ct_step.
    rewrite ppo_in_ar_int. eauto with hahn. }
  arewrite_id ⦗W⦘. rewrite seq_id_l.
  rewrite (dom_r WF.(wf_rmwD)).
  sin_rewrite BB. sin_rewrite AA.
  rewrite <- ct_step.
  rewrite w_ex_acq_sb_w_in_ar_int. eauto with hahn.
Qed.

(* TODO: move to imm_s_ppo. *)
Lemma ar_int_rfe_rfrmw_rt_in_ar_int_rfe_ct :
  (rfe ∪ ar_int) ;; (rf ;; rmw)^* ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  apply rt_ind_left with (P:=fun r => (rfe ∪ ar_int) ⨾ r).
  { eauto with hahn. }
  { by rewrite seq_id_r, <- ct_step. }
  ins. sin_rewrite ar_int_rfe_rfrmw_in_ar_int_rfe_ct.
  rewrite ct_end at 1. rewrite !seqA. rewrite H.
  relsf.
Qed.

(* TODO: move to imm_s_ppo. *)
Lemma ar_int_rfe_ct_rfrmw_rt_in_ar_int_rfe_ct :
  (rfe ∪ ar_int)⁺ ;; (rf ;; rmw)^* ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  rewrite ct_end at 1. rewrite !seqA. rewrite ar_int_rfe_rfrmw_rt_in_ar_int_rfe_ct; auto.
  relsf.
Qed.

Lemma sw_in_ar0 :
  sw ⊆
     ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfe ∪ ar_int)⁺
     ∪ sb.
Proof using WF.
  remember (rfe ∪ ar_int) as ax.
  unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
  rewrite rt_rf_rmw.
  arewrite ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfi ⨾ rmw)＊ ⊆ (sb ∩ same_loc)^? ⨾ ⦗W⦘).
  { rewrite (dom_r WF.(wf_rmwD)). sin_rewrite WF.(rfi_rmw_in_sb_loc).
    rewrite rtE. rewrite inclusion_ct_seq_eqv_r.
    generalize (@sb_same_loc_trans G); intros HH.
    rewrite ct_of_trans; auto. generalize HH; basic_solver 10. }
  arewrite (⦗W⦘ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊ ⊆ ⦗W⦘ ;; (ax⁺ ⨾ ⦗W_ex⦘)^?).
  { rewrite crE.
    rewrite rtE at 1. rewrite seq_union_r. unionL.
    { basic_solver. }
    rewrite ct_begin, !seqA.
    rewrite rmw_W_ex at 1. rewrite !seqA.
    sin_rewrite rfe_rmw_in_rfe_ar_int_ct.
    arewrite ((rfi ⨾ rmw)＊ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊ ⊆ (rf ;; rmw)^*).
    { arewrite (rfi ⊆ rf). arewrite (rfe ⊆ rf).
      rewrite <- seqA, <- ct_begin. rewrite rt_of_ct. apply rt_rt. }
    arewrite (⦗W_ex⦘ ⨾ (rf ⨾ rmw)＊ ⊆ ⦗W_ex⦘ ⨾ (rf ⨾ rmw)＊ ⨾  ⦗W_ex⦘).
    { rewrite <- seqA. apply codom_rel_helper.
      rewrite rtE, seq_union_r, codom_union. unionL; [basic_solver|].
      rewrite rmw_W_ex at 1. rewrite <- seqA. rewrite inclusion_ct_seq_eqv_r.
      basic_solver. }
    arewrite_id ⦗W_ex⦘ at 1. rewrite seq_id_l.
    sin_rewrite ar_int_rfe_ct_rfrmw_rt_in_ar_int_rfe_ct; auto.
    subst ax. basic_solver. }
  arewrite ((ax⁺ ⨾ ⦗W_ex⦘)^? ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ ax⁺ ∪ sb).
  2: { rewrite !seq_union_r. unionL; eauto with hahn.
       generalize (@sb_trans G). basic_solver. }
  rewrite rfi_union_rfe.
  assert ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ ax^? ⨾ ⦗Acq⦘) as AA.
  { rewrite !crE, !seq_union_l. apply union_mori; [done|].
    arewrite (⦗Acq⦘ ⊆ ⦗Acq/Rel⦘ ;; ⦗Acq⦘) at 1 by mode_solver.
    hahn_frame_r. rewrite <- id_inter.
    rewrite sb_to_f_in_bob. rewrite bob_in_ar_int. subst ax. eauto with hahn. }
  rewrite !seq_union_l, !seq_union_r. unionL.
  2: { arewrite (rfe ⊆ ax) by subst ax; eauto with hahn.
       rewrite AA. arewrite_id ⦗W_ex⦘. rewrite seq_id_r.
       rewrite cr_of_ct. seq_rewrite <- ct_end.
       seq_rewrite ct_cr. basic_solver. }
  rewrite crE at 1. rewrite !seq_union_l, seq_id_l. unionL.
  { arewrite (rfi ⊆ sb). generalize (@sb_trans G). basic_solver. }
  rewrite seqA. rewrite crE at 1. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
  arewrite (⦗W_ex⦘ ⨾ rfi ⨾ ⦗Acq⦘ ⊆ ax).
  { subst ax. unfold imm_s_ppo.ar_int. rewrite (dom_r WF.(wf_rfiD)) at 1.
    basic_solver 10. }
  rewrite ct_unit.
  arewrite_id ⦗W_ex⦘. rewrite seq_id_l.
  arewrite (rfi ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⊆ sb ⨾ ⦗F ∩₁ Acq/Rel⦘).
  2: { rewrite sb_to_f_in_bob. rewrite bob_in_ar_int. 
       arewrite (ar_int ⊆ ax) by subst ax; eauto with hahn.
       rewrite ct_unit. eauto with hahn. }
  arewrite (rfi ⊆ sb). generalize (@sb_trans G). mode_solver 10.
Qed.

Lemma sw_in_ar1 :
  sw ⊆ (<|F ∩₁ Rel|> ;; sb ∪ <|W ∩₁ Rel|> ;; (sb ∩ same_loc⨾ ⦗W⦘)^?) ⨾ 
  (rfe ∪ ar_int)⁺ ⨾ sb^? ∪ sb.
Proof using WF.
  rewrite sw_in_ar0.
  apply union_mori; [|done].
  assert (<|fun _ => True|> ⊆ sb^?) as HH by basic_solver.
  rewrite <- HH, seq_id_r.
  hahn_frame_r. generalize (@sb_trans G). basic_solver 10.
Qed.

Lemma f_sc_hb_f_sc_in_rfe_ar_int :
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  unfold imm_s_hb.hb.
  rewrite (dom_l (wf_swD WF)).
  rewrite sw_in_ar1.
  remember (rfe ∪ ar_int) as ax.
  rewrite seq_union_r.
  arewrite (⦗FW ∩₁ Rel⦘ ⨾ sb ⊆ sb).

  rewrite unionC.
  rewrite unionA.
  arewrite (sb ∪ sb ⊆ sb).
  rewrite unionC.
  rewrite path_union.

  rewrite seq_union_l, seq_union_r. unionL.
  { rewrite ct_of_trans; [|by apply sb_trans].
    desf. rewrite <- ct_step; unfold imm_s_ppo.ar_int, imm_bob.bob, imm_bob.fwbob.
    mode_solver 21. }
  rewrite rt_of_trans; [|by apply sb_trans].
  rewrite ct_seq_swap.
  rewrite !seqA.
  arewrite (sb^? ⨾ sb^? ⊆ sb^?).
  { generalize (@sb_trans G). basic_solver. }
  rewrite ct_rotl, !seqA.

  assert (sb^? ⨾ ⦗FW ∩₁ Rel⦘ ⊆ ax^?) as BB.
  { desf.
    rewrite <- bob_in_ar_int, <- fwbob_in_bob.
    unfold imm_bob.fwbob.
    mode_solver 12. }

  sin_rewrite !BB.

  arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ ax^?).
  { desf.
    rewrite <- bob_in_ar_int, <- fwbob_in_bob.
    unfold imm_bob.fwbob.
    mode_solver 12. }
  rels.
  arewrite ((⦗F ∩₁ Rel⦘ ⨾ sb ∪ ⦗W ∩₁ Rel⦘ ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^?) ⊆ ax^?).
  { unionL.
    2: { rewrite crE. rewrite seq_union_r. unionL.
         { basic_solver. }
         rewrite sb_from_w_rel_in_bob. subst. unfold imm_s_ppo.ar_int. basic_solver 10. }
    arewrite (Rel ⊆₁ Acq/Rel) by mode_solver.
    rewrite sb_from_f_in_fwbob. rewrite fwbob_in_bob.
    subst. unfold imm_s_ppo.ar_int. basic_solver 10. }
  rels.
  basic_solver.
Qed.

Lemma f_sc_hb_f_sc_in_ar : 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ (ar sc)⁺.
Proof using WF.
  rewrite f_sc_hb_f_sc_in_rfe_ar_int.
  unfold ar. apply clos_trans_mori. eauto with hahn.
Qed.

Lemma f_sc_hb_f_sc_in_sc : 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof using WF WF_SC ACYC_EXT.
arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗F ∩₁ Sc⦘) by basic_solver.
sin_rewrite f_sc_hb_f_sc_in_ar.
apply F_sc_ar_F_sc; done.
Qed.

Lemma wf_ar : well_founded (ar sc).
Proof using WF WF_SC IMMCON.
  eapply wf_finite.
  { cdes IMMCON. apply Cext. }
  rewrite wf_arE; auto.
  apply doma_eqv.
Qed.

Lemma wf_ar_tc : well_founded ((ar sc)⁺).
Proof using WF WF_SC IMMCON.
  eapply wf_finite; auto.
  { cdes IMMCON. unfold acyclic. rewrite ct_of_ct.
    apply Cext. }
  rewrite wf_arE; auto.
  apply ct_doma. apply doma_eqv.
Qed.

Lemma ar_int_in_ar : ar_int ⊆ ar sc.
Proof using. unfold ar. basic_solver. Qed.

Lemma ppo_in_ar : ppo ⊆ ar sc.
Proof using.
  etransitivity; [|by apply ar_int_in_ar].
  apply ppo_in_ar_int.
Qed.

Lemma bob_in_ar : bob ⊆ ar sc.
Proof using.
  etransitivity; [|by apply ar_int_in_ar].
  apply bob_in_ar_int.
Qed.

Lemma detour_in_ar : detour ⊆ ar sc.
Proof using.
  etransitivity; [|by apply ar_int_in_ar].
  apply detour_in_ar_int.
Qed.

Lemma rfe_in_ar : rfe ⊆ ar sc.
Proof using. unfold ar. basic_solver. Qed.

Lemma sc_in_ar : sc ⊆ ar sc.
Proof using. unfold ar. basic_solver. Qed.

Lemma w_ex_acq_sb_w_in_ar : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar sc.
Proof using.
  etransitivity; [|by apply ar_int_in_ar].
  apply w_ex_acq_sb_w_in_ar_int.
Qed.

Lemma coh_sc_alt : ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ sc.
Proof using WF WF_SC CSC COH.
rewrite (dom_l (wf_hbE WF)) at 1.
rewrite (dom_r (wf_hbE WF)) at 2.
unfolder; ins; desf.
eapply tot_ex.
apply WF_SC.
basic_solver.
basic_solver.
intro; eapply CSC; basic_solver 10.
intro; subst.
eapply COH.
eexists; splits; [ | eby right].
eapply hb_trans; eauto.
Qed.

Proposition coh_helper_alt :
  irreflexive (hb ⨾ sc^? ∪ hb ⨾ (sc ⨾ hb)^? ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ co ∪ hb ⨾ (sc ⨾ hb)^? ⨾ co ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ fr ∪ hb ⨾ (sc ⨾ hb)^? ⨾ fr ⨾ rfe) -> 
  irreflexive (hb ⨾ (sc ⨾ hb)^? ⨾ eco^?).
Proof using.
unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize (@hb_trans G); ins; relsf.
all: try (unfolder in *; basic_solver 12).
all: try (unfolder in *; basic_solver 16).
Qed.

Lemma init_co_w
      e e' (INIT : is_init e) (NINIT : ~ is_init e')
      (EE : E e') (WW : W e') (SL : same_loc e e') :
  co e e'.
Proof using WF IMMCON.
  destruct (is_w_loc lab e' WW) as [l LOC].
  red in SL. rewrite LOC in SL.
  unfold is_init in INIT. unfold Events.loc in SL.
  destruct e; [|done].
  rewrite WF.(wf_init_lab) in SL. inv SL.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists. eauto. }
  edestruct WF.(wf_co_total) as [CO|CO]; eauto; desf.
  { split; [split|]; auto. by apply init_w.
    unfold Events.loc at 1. by rewrite WF.(wf_init_lab). }
  { intros H. subst. desf. }
  exfalso. cdes IMMCON.
  eapply Cint. eexists. split.
  { apply sb_in_hb. by apply init_ninit_sb with (y:=e'); eauto. }
  apply r_step. apply Execution_eco.co_in_eco; eauto.
Qed.

Lemma wf_rfrmw_irr : irreflexive (rf ⨾ rmw).
Proof using WF IMMCON.
  arewrite (rmw ⊆ sb).
  { rewrite WF.(wf_rmwi). basic_solver. }
  rewrite Execution_eco.rf_in_eco.
  rewrite sb_in_hb. cdes IMMCON.
  red in Cint. generalize Cint. basic_solver 10.
Qed.

Lemma rfrmw_in_im_co :
  rf ⨾ rmw ⊆ immediate co.
Proof using WF IMMCON. 
  cdes IMMCON.
  apply rf_rmw_in_coimm; auto using coherence_sc_per_loc.
Qed.

Lemma rfe_rmw_in_ar_ct : rfe ;; rmw ⊆ (ar sc)⁺.
Proof using WF.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, WF.(rmw_in_ppo), ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

Lemma rfe_ppo_in_ar_ct : rfe ;; ppo ⊆ (ar sc)⁺.
Proof using.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

(*
Lemma rfe_Rex_sb_in_ar_ct : rfe ;; <|R_ex|> ;; sb ;; <|W|> ⊆ ar⁺.
Proof using.
  arewrite (⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo).
  2: by apply rfe_ppo_in_ar_ct.
  unfold imm_s_ppo.ppo. rewrite <- ct_step, !seq_union_l, !seq_union_r, !seqA.
  unionR left -> right.
  type_solver.
Qed.
*)

(*
Lemma rfe_rmw_sb_in_ar_ct WF : rfe ;; rmw ;; sb ;; <|W|> ⊆ ar⁺.
Proof using.
  rewrite (dom_l WF.(wf_rmwD)), WF.(rmw_in_sb), !seqA.
  (* TODO: introduce a lemma *)
  arewrite (sb ;; sb ⊆ sb).
  { apply transitiveI. apply sb_trans. }
  apply rfe_Rex_sb_in_ar_ct.
Qed.
*)

Lemma sb_release_rmw_in_fwbob
      (COMPL : complete G)
      (SPL   : Execution_eco.sc_per_loc G) :
  sb^? ∩ release G ⨾ sb ∩ Events.same_loc lab ⨾ rmw ⊆ fwbob G.
Proof using WF.
  rewrite (dom_r WF.(wf_rmwD)).
  rewrite WF.(rmw_in_sb_loc).
  sin_rewrite rewrite_trans.
  2: by apply sb_same_loc_trans.
  rewrite (dom_l WF.(wf_releaseD)).
  arewrite (sb^? ∩ (⦗(F ∪₁ W) ∩₁ Rel⦘ ⨾ release G) ⊆
            ⦗(F ∪₁ W) ∩₁ Rel⦘ ⨾ (sb^? ∩ release G)).
  { basic_solver. }
  rewrite set_inter_union_l.
  rewrite id_union, seq_union_l.
  unionL.
  { unfold fwbob.
    unionR right. 
    arewrite (sb^? ∩ release G ⨾ sb ∩ Events.same_loc lab ⊆ sb).
    { generalize (@sb_trans G). basic_solver. }
    mode_solver. }
  unfold release.
  arewrite (⦗W ∩₁ Rel⦘ ⨾ sb^? ∩ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs G) ⊆
            ⦗W ∩₁ Rel⦘ ⨾ sb^? ∩ (⦗Rel⦘ ⨾ rs G)).
  { type_solver 10. }
  rewrite rs_in_co; auto.
  rewrite WF.(wf_col).
  arewrite (sb^? ∩ (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Events.same_loc lab)^?) ⊆
               (sb ∩ Events.same_loc lab)^?).
  { basic_solver. }
  sin_rewrite rewrite_trans_seq_cr_l.
  2: by apply sb_same_loc_trans.
  unfold fwbob. eauto with hahn.
Qed.

Lemma no_ar_to_init : ar sc ;; <|is_init|> ≡ ∅₂.
Proof using WF IMMCON.
  split; [|basic_solver].
  unfold ar.
  rewrite WF.(ar_int_in_sb). rewrite no_sb_to_init.
  rewrite wf_scD with (sc:=sc); [|by apply IMMCON].
  rewrite WF.(wf_rfeD).
  rewrite seq_union_l. unionL; [|basic_solver].
  rewrite WF.(init_w). type_solver 10.
Qed.

Lemma no_ar_rfrmw_to_init : (ar sc ∪ rf ⨾ rmw) ;; <|is_init|> ≡ ∅₂.
Proof using WF IMMCON.
  split; [|basic_solver].
  rewrite seq_union_l, seqA, no_ar_to_init; auto.
  rewrite WF.(rmw_in_sb). rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma wf_ar_rfrmwE :
  ar sc ∪ rf ;; rmw ≡ <|E|> ;; (ar sc ∪ rf ;; rmw) ;; <|E|>.
Proof using WF WF_SC IMMCON.
  rewrite wf_arE at 1; auto.
  rewrite (dom_l WF.(wf_rfE)) at 1.
  rewrite (dom_r WF.(wf_rmwE)) at 1.
  basic_solver 10.
Qed.

Lemma wf_ar_rfrmw_ctE :
  (ar sc ∪ rf ;; rmw)⁺ ≡ <|E|> ;; (ar sc ∪ rf ;; rmw)⁺ ;; <|E|>.
Proof using WF WF_SC IMMCON.
  split; [|basic_solver].
  rewrite wf_ar_rfrmwE at 1; auto.
  rewrite inclusion_ct_seq_eqv_l.
    by rewrite inclusion_ct_seq_eqv_r.
Qed.

Lemma ar_ar_in_ar_ct : ar sc ;; ar sc ⊆ (ar sc)⁺.
Proof using.
  rewrite ct_step with (r:=ar sc) at 1 2. apply ct_ct.
Qed.

Lemma rfe_n_same_tid : rfe ∩ same_tid ⊆ ∅₂.
Proof using WF IMMCON.
  arewrite (rfe ∩ same_tid ⊆ rfe ∩ (<|E|> ;; same_tid ;; <|E|>)).
  { rewrite WF.(wf_rfeE) at 1. basic_solver. }
  arewrite (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘ ⊆ same_tid ∩ (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘)) by basic_solver.
  rewrite tid_sb.
  rewrite !inter_union_r.
  unionL.
  3: { rewrite WF.(wf_rfeD). rewrite init_w; eauto. type_solver. }
  2: { unfolder. ins. desf.
       cdes IMMCON.
       eapply Cint. eexists. split.
       { eby apply sb_in_hb. }
       right. apply rf_in_eco.
       match goal with
       | H : rfe _ _ |- _ => apply H
       end. }
  unfolder. ins. desf.
  { eapply eco_irr; eauto. apply rf_in_eco.
    match goal with
    | H : rfe _ _ |- _ => apply H
    end. }
  cdes IMMCON.
  eapply (thread_rfe_sb WF (coherence_sc_per_loc Cint)).
  basic_solver 10.
Qed.

Lemma ar_W_in_ar_int : ar sc ;; <|W|> ⊆ ar_int.
Proof using WF IMMCON.
  unfold ar. erewrite wf_scD with (sc:=sc); [|by apply IMMCON].
  rewrite WF.(wf_rfeD). type_solver.
Qed.

Lemma C_EXT_helper2 : (psc ∪ rfe)⁺ ⊆ psc⁺ ∪ rfe.
Proof using WF.
apply ct_ind_left with (P:= fun r => r).
by eauto with hahn.
by unionL; vauto.
ins; rewrite H; relsf; unionL.
arewrite (psc ⊆ psc＊); relsf.
rewrite ct_begin.
rewrite (dom_l wf_pscD) at 1; rewrite (dom_r (wf_rfeD WF)); type_solver 12.
rewrite (dom_r wf_pscD) at 1; rewrite (dom_l (wf_rfeD WF)); type_solver 12.
rewrite (dom_r (wf_rfeD WF)) at 1; rewrite (dom_l (wf_rfeD WF)); type_solver 12.
Qed.

Lemma s_acyc_ext_psc_helper
      (AC : acyclic (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)) :
  acyclic (psc ∪ rfe ∪ ar_int).
Proof using WF.
  generalize (@sb_trans G); intro SBT.
  red. apply acyclic_mon with (r:= ar_int ∪ (psc ∪ rfe)).
  2: by basic_solver 12.
  apply acyclic_union1.
  { rewrite (ar_int_in_sb WF). apply sb_acyclic. }
  { eapply acyclic_mon; [edone|basic_solver 12]. }
  rewrite C_EXT_helper2; unionL.
  arewrite (psc ⊆ sb^? ⨾ psc ⨾ sb^?) by basic_solver 12.
  relsf.
  rewrite (imm_s_ppo.ar_int_in_sb WF) at 1; relsf.
  rewrite ct_begin, !seqA; relsf.
  arewrite (sb ⊆ sb^?) at 1.
  rewrite <- !seqA, <- ct_begin, !seqA.
  apply acyclic_union1.
  { red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  { rewrite (dom_l (wf_rfeD WF)), <- seqA, acyclic_rotl.
    rewrite (dom_r (wf_rfeD WF)), !seqA.
    apply acyclic_seq_from_union.
    red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  relsf.
  rewrite (ct_begin (ar_int⁺ ⨾ rfe)).
  rewrite (imm_s_ppo.ar_int_in_sb WF) at 1.
  rewrite !seqA; relsf.
  arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⨾ sb ⊆ (sb^? ⨾ psc ⨾ sb^?)⁺).
  { rewrite ct_end at 1; rewrite !seqA.
    arewrite (sb^? ⨾ sb ⊆ sb^?).
    { generalize (@sb_trans G); basic_solver. }
      by rewrite <- ct_end. }
  rewrite (dom_l (wf_rfeD WF)) at 2.
  arewrite (rfe ⨾ (ar_int⁺ ⨾ ⦗W⦘ ⨾ rfe)＊ ⊆ (rfe ⨾ ar_int⁺ ⨾ ⦗W⦘)＊ ⨾ rfe).
  { by rewrite <- seqA; apply rt_seq_swap. }
  rewrite (dom_r (wf_rfeD WF)) at 1.
  rewrite !seqA.
  arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)⁺).
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  arewrite (⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 3.
  relsf.
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  relsf; red; rels.
Qed.

End SC.

Lemma s_acyc_ext_helper
      (AC : acyclic (psc ∪ rfe ∪ ar_int)) :
  exists sc, wf_sc sc /\ acyc_ext sc /\ coh_sc sc.
Proof using WF.
  set (ar' := psc ∪ rfe ∪ ar_int).
  unfold acyc_ext.
  exists (⦗ E ∩₁ F ∩₁ Sc ⦘ ⨾ tot_ext G.(acts) ar' ⨾ ⦗ E ∩₁ F ∩₁ Sc ⦘).
  splits.
  { constructor.
    1,2: apply dom_helper_3; basic_solver.
    { rewrite <- restr_relE; apply transitive_restr, tot_ext_trans. }
    { unfolder; ins; desf.
      cut (tot_ext (acts G) ar' a b \/ tot_ext (acts G) ar' b a).
      { basic_solver 12. }
      eapply tot_ext_total; desf; eauto. }
    rewrite <- restr_relE.
    apply irreflexive_restr. by apply tot_ext_irr. }
  { unfold ar.
    apply acyclic_mon with (r:= tot_ext (acts G) ar').
    { apply trans_irr_acyclic.
      { apply tot_ext_irr, AC. }
      apply tot_ext_trans. }
    apply inclusion_union_l; [apply inclusion_union_l|].
    { basic_solver. }
    all: subst ar'; rewrite <- tot_ext_extends; unfold ar; basic_solver. }
  unfold coh_sc.
  rotate 4.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⨾ hb ⨾ (eco ⨾ hb)^? ⨾ ⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ar'⁺).
  2: { arewrite (ar' ⊆ tot_ext (acts G) ar') at 2.
       { apply tot_ext_extends. }
       rewrite ct_step with (r:= tot_ext (acts G) ar') at 1.
       rewrite ct_ct.
       apply trans_irr_acyclic.
       { apply tot_ext_irr, AC. }
       apply tot_ext_trans. }
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘) by basic_solver.
  case_refl _. 
  { erewrite f_sc_hb_f_sc_in_rfe_ar_int; eauto.
    apply clos_trans_mori. subst ar'. eauto with hahn. }
  rewrite !seqA. rewrite <- ct_step. subst ar'. 
  unfold psc. eauto with hahn.
Qed.

End IMM.
