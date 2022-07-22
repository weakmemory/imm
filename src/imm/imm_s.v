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
Require Import AuxDef.
Require Import AuxRel2.

Set Implicit Arguments.

Section IMM.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).
Notation "'hb'" := (imm_s_hb.hb G).
Notation "'sw'" := (imm_s_hb.sw G).

Notation "'bob'" := (bob G).
Notation "'ppo'" := (imm_s_ppo.ppo G).
Notation "'ar_int'" := (imm_s_ppo.ar_int G).

Notation "'lab'" := (lab G).
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

(* Hypothesis FSUPP : fsupp (ar sc)⁺. *)
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

Lemma sc_not_init:
  sc ≡ ⦗set_compl is_init⦘ ⨾ sc ⨾ ⦗set_compl is_init⦘. 
Proof using WF WF_SC. 
  apply dom_helper_3.
  rewrite wf_scD, init_pln; eauto. mode_solver. 
Qed.

Lemma no_sc_to_init :
 sc ≡ sc ⨾  ⦗fun x => ~ is_init x⦘.
Proof using WF WF_SC.
  rewrite sc_not_init. basic_solver. 
Qed.

(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma n_Wex_co_rf_rmw_rt_transp_in_co_cr :
  ⦗set_compl W_ex⦘ ⨾ co ⨾ ((rf ⨾ rmw)＊)⁻¹ ⊆ co^?.
Proof using WF IMMCON.
  clear AT.
  rewrite transp_rt.
  eapply rt_ind_right with (P:= fun r => ⦗set_compl W_ex⦘ ⨾ co ⨾ r).
  { by eauto with hahn. }
  { basic_solver. }
  ins.
  arewrite (⦗set_compl W_ex⦘ ⊆ ⦗set_compl W_ex⦘ ⨾ ⦗set_compl W_ex⦘) by basic_solver.
  sin_rewrite H.
  rewrite crE at 1. relsf. unionL.
  { rewrite rmw_W_ex. basic_solver. }
  rewrite rf_rmw_in_coimm; auto; try apply IMMCON.
  { rewrite co_immediate_co_in_co_cr; auto. basic_solver. }
  apply coherence_sc_per_loc. apply IMMCON.
Qed.

Lemma sc_rfe_ct_in_sc_rfe : (sc ∪ rfe)⁺ ⊆ sc ∪ rfe.
Proof using WF WF_SC.
  rewrite path_union.
  generalize (sc_trans WF_SC); ins; relsf; unionL; [basic_solver|].
  rewrite crE at 2; relsf; unionL.
  { arewrite (sc^? ⨾ rfe ⊆ rfe).
    { rewrite crE; relsf; unionL; [basic_solver|].
      rewrite (dom_l (wf_rfeD WF)) at 1.
      rewrite (dom_r (wf_scD WF_SC)) at 1.
      type_solver. }
    rewrite ct_begin, rtE; relsf; unionL; [basic_solver|].
    rewrite ct_begin.
    rewrite (wf_rfeD WF).
    type_solver. }
  rewrite (dom_r (wf_rfeD WF)).
  rewrite <- !seqA.
  rewrite inclusion_ct_seq_eqv_r, !seqA.
  rewrite (dom_l (wf_scD WF_SC)) at 2.
  type_solver.
Qed.

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

Lemma sw_in_ar0 :
  sw ⊆
     ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfe ∪ ar_int)⁺
     ∪ sb.
Proof using WF.
  remember (rfe ∪ ar_int) as ax.
  unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
  rewrite rt_rf_rmw.
  arewrite ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfi ⨾ rmw)＊ ⊆ (sb ∩ same_loc)^? ⨾ ⦗W⦘).
  { rewrite (dom_r (wf_rmwD WF)). sin_rewrite (rfi_rmw_in_sb_loc WF).
    rewrite rtE. rewrite inclusion_ct_seq_eqv_r.
    generalize (@sb_same_loc_trans G); intros HH.
    rewrite ct_of_trans; auto. generalize HH; basic_solver 10. }
  arewrite (⦗W⦘ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊ ⊆ ⦗W⦘ ⨾ (ax⁺ ⨾ ⦗W_ex⦘)^?).
  { rewrite crE.
    rewrite rtE at 1. rewrite seq_union_r. unionL.
    { basic_solver. }
    rewrite ct_begin, !seqA.
    rewrite rmw_W_ex at 1. rewrite !seqA.
    sin_rewrite rfe_rmw_in_rfe_ar_int_ct; auto.
    arewrite ((rfi ⨾ rmw)＊ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊ ⊆ (rf ⨾ rmw)＊).
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
    arewrite (⦗Acq⦘ ⊆ ⦗Acq/Rel⦘ ⨾ ⦗Acq⦘) at 1 by mode_solver.
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
  { subst ax. unfold imm_s_ppo.ar_int. rewrite (dom_r (wf_rfiD WF)) at 1.
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
  sw ⊆ (⦗F ∩₁ Rel⦘ ⨾ sb ∪ ⦗W ∩₁ Rel⦘ ⨾ (sb ∩ same_loc⨾ ⦗W⦘)^?) ⨾ 
  (rfe ∪ ar_int)⁺ ⨾ sb^? ∪ sb.
Proof using WF.
  rewrite sw_in_ar0.
  apply union_mori; [|done].
  assert (⦗fun _ => True⦘ ⊆ sb^?) as HH by basic_solver.
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

Lemma f_sc_sb_f_sc_in_sc : ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof using WF WF_SC ACYC_EXT.
  rewrite sb_in_hb.
  apply f_sc_hb_f_sc_in_sc; auto.
Qed.

Lemma sc_sb_sc_in_sc : sc ⨾ sb ⨾ sc ⊆ sc.
Proof using WF WF_SC ACYC_EXT.
  assert (transitive sc) as TSC.
  { now apply WF_SC. }
  rewrite (wf_scD WF_SC) at 1 2.
  rewrite !seqA.
  sin_rewrite f_sc_sb_f_sc_in_sc; auto.
  sin_rewrite !rewrite_trans; auto.
  clear; basic_solver 1.
Qed.

Lemma sb_sc_acyclic : acyclic (sb ∪ sc).
Proof using WF WF_SC ACYC_EXT.
  assert (transitive sc) as TSC.
  { now apply WF_SC. }
  assert (transitive sb) as TSB.
  { apply sb_trans. }
  apply acyclic_utt; auto.
  splits.
  { apply sb_irr. }
  { apply WF_SC. }
  rewrite (wf_scD WF_SC).
  rewrite <- !seqA, acyclic_rotl, !seqA.
  sin_rewrite f_sc_sb_f_sc_in_sc; auto.
  rewrite rewrite_trans; auto.
  red. rewrite ct_of_trans; auto.
  apply WF_SC.
Qed.

Lemma sb_sc_rt : (sb ∪ sc)^* ≡ sb^? ;; sc^? ;; sb^?.
Proof using WF WF_SC ACYC_EXT.
  assert (transitive sc) as TSC.
  { now apply WF_SC. }
  assert (transitive sb) as TSB.
  { apply sb_trans. }
  assert (transitive (sb ⨾ sc)) as TSBSC.
  { apply transitiveI. rewrite seqA.
    now rewrite sc_sb_sc_in_sc; auto. }
  split.
  2: { arewrite (sb^? ⊆ (sb ∪ sc)＊).
       arewrite (sc^? ⊆ (sb ∪ sc)＊).
       now rewrite !rt_rt. }
  rewrite unionC.
  rewrite path_ut; auto.
  rewrite ct_of_trans; auto.
  rewrite rt_of_trans; auto.
  rewrite rt_of_trans; auto.
  rewrite !crE. rewrite !seq_union_l, !seq_id_l, !seq_union_r, !seqA.
  rewrite !seq_id_r.
  rewrite sc_sb_sc_in_sc; auto.
  unionL; eauto with hahn.
  sin_rewrite sc_sb_sc_in_sc; auto.
  eauto with hahn.
Qed.


(* Lemma wf_ar : well_founded (ar sc). *)
(* Proof using WF FINDOM WF_SC IMMCON. *)
(*   cdes FINDOM. *)
(*   eapply wf_finite. *)
(*   { cdes IMMCON. apply Cext. } *)
(*   rewrite wf_arE; auto. *)
(*   eapply doma_mori; [reflexivity|red; apply FINDOM0 |]. *)
(*   apply doma_eqv. *)
(* Qed. *)

(* Lemma wf_ar_tc : well_founded ((ar sc)⁺). *)
(* Proof using WF FSUPP WF_SC IMMCON. *)
(*   apply fsupp_well_founded; auto. *)
(*   apply transitive_ct. *)
(*   (* cdes FINDOM. *) *)
(*   (* eapply wf_finite; auto. *) *)
(*   (* { cdes IMMCON. unfold acyclic. rewrite ct_of_ct. *) *)
(*   (*   apply Cext. } *) *)
(*   (* rewrite wf_arE; auto. *) *)
(*   (* apply ct_doma. *) *)
(*   (* eapply doma_mori; [reflexivity|red; apply FINDOM0 |]. *) *)
(*   (* apply doma_eqv. *) *)
(* Qed. *)

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

Lemma rmwrf_ct_Acq_in_ar_rfrmw_ct : (rmw ⨾ rf)⁺ ⨾ ⦗Acq⦘ ⊆ (ar sc ∪ rf ⨾ rmw)⁺.
Proof using WF.
  rewrite rmw_W_ex at 1. rewrite !seqA.
  rewrite clos_trans_rotl, !seqA.
  arewrite (⦗W_ex⦘ ⨾ rf ⨾ ⦗Acq⦘ ⊆ ar sc).
  { rewrite rfi_union_rfe, !seq_union_l, !seq_union_r.
    unionL.
    2: { rewrite rfe_in_ar. basic_solver. }
    rewrite (dom_r (wf_rfiD WF)), !seqA. rewrite <- id_inter.
    unfold ar, imm_s_ppo.ar_int. eauto with hahn. }
  rewrite (rmw_in_ar_int WF) at 1. rewrite ar_int_in_ar.
  arewrite (⦗W_ex⦘ ⨾ rf ⨾ rmw ⊆ ar sc ∪ rf ⨾ rmw).
  arewrite (ar sc ⊆ ar sc ∪ rf ⨾ rmw) at 1.
  arewrite (ar sc ⊆ ar sc ∪ rf ⨾ rmw) at 3.
  rewrite <- ct_end.
  rewrite ct_step with (r:=ar sc ∪ rf ⨾ rmw) at 1.
  apply ct_ct.
Qed.

Lemma rmwrf_rt_Acq_in_ar_rfrmw_rt : (rmw ⨾ rf)＊ ⨾ ⦗Acq⦘ ⊆ (ar sc ∪ rf ⨾ rmw)＊.
Proof using WF.
  rewrite !rtE, seq_union_l. rewrite rmwrf_ct_Acq_in_ar_rfrmw_ct. basic_solver.
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
  rewrite (wf_init_lab WF) in SL. inv SL.
  assert (E (InitEvent l)) as EL.
  { apply (wf_init WF). eexists. eauto. }
  edestruct (wf_co_total WF) as [CO|CO]; eauto; desf.
  { split; [split|]; auto. by apply init_w.
    unfold Events.loc at 1. by rewrite (wf_init_lab WF). }
  { intros H. subst. desf. }
  exfalso. cdes IMMCON.
  eapply Cint. eexists. split.
  { apply sb_in_hb. by apply init_ninit_sb with (y:=e'); eauto. }
  apply r_step. apply Execution_eco.co_in_eco; eauto.
Qed.

Lemma wf_rfrmw_irr : irreflexive (rf ⨾ rmw).
Proof using WF IMMCON.
  arewrite (rmw ⊆ sb).
  { rewrite (wf_rmwi WF). basic_solver. }
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

Lemma wf_rfrmwsf : functional (rf ⨾ rmw).
Proof using WF IMMCON.
  rewrite rfrmw_in_im_co; eauto.
  apply wf_immcof; auto.
Qed.

Lemma wf_rfirmwsf : functional (rfi ⨾ rmw).
Proof using WF IMMCON. arewrite (rfi ⊆ rf). eapply wf_rfrmwsf; eauto. Qed.

Lemma W_ex_in_codom_rfrmw : W_ex ⊆₁ codom_rel (rf ⨾ rmw).
Proof using WF IMMCON.
  intros x [y RMW].
  enough (exists z, rf z y) as [z RF].
  { exists z. eexists. eauto. }
  apply IMMCON.
  apply (dom_l (wf_rmwE WF)) in RMW. destruct_seq_l RMW as AA. split; auto.
  apply (dom_l (wf_rmwD WF)) in RMW. destruct_seq_l RMW as BB. type_solver.
Qed.

Lemma rfrmwP_in_immPco P P'
    (DRES : dom_rel (rf ⨾ rmw ⨾ ⦗P'⦘) ⊆₁ P) :
  rf ⨾ rmw ⨾ ⦗P'⦘ ⊆ immediate (⦗P⦘ ⨾ co).
Proof using WF IMMCON.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IMMCON. }

  rewrite <- immediate_inter_mori with (x:=co).
  2: basic_solver.
  apply inclusion_inter_r.
  2: { rewrite <- seqA. rewrite rfrmw_in_im_co; eauto. basic_solver. }
  rewrite <- rf_rmw_in_co; auto.
  generalize DRES. basic_solver 10.
Qed.

Lemma rfrmw_in_eco (SPL : sc_per_loc G) (COMP : complete G) :
  rf ⨾ rmw ⊆ eco.
Proof using WF.
  rewrite rf_in_eco. rewrite rmw_in_fr; auto.
  rewrite fr_in_eco.
  apply transitiveI. by apply eco_trans.
Qed.

Lemma rfrmw_sb_irr : 
  irreflexive (rf ⨾ rmw ⨾ sb).
Proof using WF IMMCON.
  arewrite (rf ⨾ rmw ⊆ eco).
  { apply rfrmw_in_eco; auto.
    apply coherence_sc_per_loc.
    all: by apply IMMCON. }
  rewrite sb_in_hb.
  rewrite irreflexive_seqC.
  arewrite (eco ⊆ eco^?).
  apply IMMCON. 
Qed.

Lemma rfe_rmw_in_ar_ct : rfe ⨾ rmw ⊆ (ar sc)⁺.
Proof using WF.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, (rmw_in_ppo WF), ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

Lemma rfe_ppo_in_ar_ct : rfe ⨾ ppo ⊆ (ar sc)⁺.
Proof using.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

(*
Lemma rfe_Rex_sb_in_ar_ct : rfe ⨾ ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar⁺.
Proof using.
  arewrite (⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo).
  2: by apply rfe_ppo_in_ar_ct.
  unfold imm_s_ppo.ppo. rewrite <- ct_step, !seq_union_l, !seq_union_r, !seqA.
  unionR left -> right.
  type_solver.
Qed.
*)

(*
Lemma rfe_rmw_sb_in_ar_ct WF : rfe ⨾ rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ar⁺.
Proof using.
  rewrite (dom_l (wf_rmwD WF)), (rmw_in_sb WF), !seqA.
  (* TODO: introduce a lemma *)
  arewrite (sb ⨾ sb ⊆ sb).
  { apply transitiveI. apply sb_trans. }
  apply rfe_Rex_sb_in_ar_ct.
Qed.
*)

Lemma sb_release_rmw_in_fwbob
      (COMPL : complete G)
      (SPL   : Execution_eco.sc_per_loc G) :
  sb^? ∩ release G ⨾ sb ∩ Events.same_loc lab ⨾ rmw ⊆ fwbob G.
Proof using WF.
  rewrite (dom_r (wf_rmwD WF)).
  rewrite (rmw_in_sb_loc WF).
  sin_rewrite rewrite_trans.
  2: by apply sb_same_loc_trans.
  rewrite (dom_l (wf_releaseD WF)).
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
  rewrite (wf_col WF).
  arewrite (sb^? ∩ (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Events.same_loc lab)^?) ⊆
               (sb ∩ Events.same_loc lab)^?).
  { basic_solver. }
  sin_rewrite rewrite_trans_seq_cr_l.
  2: by apply sb_same_loc_trans.
  unfold fwbob. eauto with hahn.
Qed.

Lemma rf_sb_sc_sb_fwbob_in_ar : rf^? ⨾ sb^? ⨾ sc^? ⨾ sb^? ⨾ (fwbob G) ⊆ (ar sc)⁺.
Proof using WF_SC.
  arewrite (rf^? ⊆ rfe^? ;; sb^?).
  { rewrite rfi_union_rfe, cr_union_r.
    rewrite rfi_in_sb. clear. basic_solver 10. }
  rewrite <- cr_ct.
  rewrite rfe_in_ar.
  hahn_frame_l.
  assert (sb^? ⨾ sb^? ⊆ sb^?) as SBSB.
  { apply transitiveI. apply transitive_cr. apply sb_trans. }
  sin_rewrite SBSB.
  arewrite (sb^? ⨾ sc^? ⊆ sb^? ∪ (fwbob G)^? ;; sc^?).
  { rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r.
    unionL; eauto with hahn.
    transitivity (fwbob G ⨾ sc); eauto with hahn.
    rewrite (dom_l (wf_scD WF_SC)) at 1.
    hahn_frame. unfold imm_bob.fwbob.
    clear. mode_solver 10. }
  rewrite !seq_union_l. sin_rewrite SBSB.
  arewrite (sb^? ⨾ (fwbob G) ⊆ (ar sc)⁺).
  { rewrite crE, !seq_union_l, seq_id_l.
    rewrite sb_fwbob_in_fwbob. rewrite fwbob_in_bob, bob_in_ar.
    eauto with hahn. }
  rewrite fwbob_in_bob, bob_in_ar.
  arewrite (sc^? ⊆ (ar sc)^?).
  rewrite !cr_ct.
  eauto with hahn.
Qed.

Lemma rf_sb_sc_rt_sb_fwbob_in_ar : rf^? ⨾ (sb ∪ sc)^* ⨾ fwbob G ⊆ (ar sc)⁺.
Proof using WF WF_SC ACYC_EXT.
  rewrite sb_sc_rt, !seqA; auto.
  now apply rf_sb_sc_sb_fwbob_in_ar.
Qed.

Lemma no_ar_to_init : ar sc ⨾ ⦗is_init⦘ ≡ ∅₂.
Proof using WF IMMCON.
  split; [|basic_solver].
  unfold ar.
  rewrite (ar_int_in_sb WF). rewrite no_sb_to_init.
  rewrite wf_scD with (sc:=sc); [|by apply IMMCON].
  rewrite (wf_rfeD WF).
  rewrite seq_union_l. unionL; [|basic_solver].
  rewrite (init_w WF). type_solver 10.
Qed.

Lemma no_ar_rfrmw_to_init : (ar sc ∪ rf ⨾ rmw) ⨾ ⦗is_init⦘ ≡ ∅₂.
Proof using WF IMMCON.
  split; [|basic_solver].
  rewrite seq_union_l, seqA, no_ar_to_init; auto.
  rewrite (rmw_in_sb WF). rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma wf_ar_rfrmwE :
  ar sc ∪ rf ⨾ rmw ≡ ⦗E⦘ ⨾ (ar sc ∪ rf ⨾ rmw) ⨾ ⦗E⦘.
Proof using WF WF_SC IMMCON.
  rewrite wf_arE at 1; auto.
  rewrite (dom_l (wf_rfE WF)) at 1.
  rewrite (dom_r (wf_rmwE WF)) at 1.
  basic_solver 10.
Qed.

Lemma wf_ar_rfrmw_ctE :
  (ar sc ∪ rf ⨾ rmw)⁺ ≡ ⦗E⦘ ⨾ (ar sc ∪ rf ⨾ rmw)⁺ ⨾ ⦗E⦘.
Proof using WF WF_SC IMMCON.
  split; [|basic_solver].
  rewrite wf_ar_rfrmwE at 1; auto.
  rewrite inclusion_ct_seq_eqv_l.
    by rewrite inclusion_ct_seq_eqv_r.
Qed.

Lemma ar_ar_in_ar_ct : ar sc ⨾ ar sc ⊆ (ar sc)⁺.
Proof using.
  rewrite ct_step with (r:=ar sc) at 1 2. apply ct_ct.
Qed.

Lemma no_ar_rf_ppo_loc_to_init : (ar sc ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗is_init⦘ ≡ ∅₂.
Proof using WF IMMCON.
  split; [|basic_solver].
  rewrite seq_union_l, seqA, no_ar_to_init; auto.
  arewrite (ppo ∩ same_loc ⊆ ppo).
  rewrite (ppo_in_sb WF). rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma wf_ar_rf_ppo_locE :
  ar sc ∪ rf ⨾ ppo ∩ same_loc ≡ ⦗E⦘ ⨾ (ar sc ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗E⦘.
Proof using WF IMMCON WF_SC.
  rewrite wf_arE at 1; auto.
  rewrite (dom_l (wf_rfE WF)) at 1.
  rewrite (dom_r (wf_ppoE WF)) at 1.
  basic_solver 10.
Qed.

Lemma wf_ar_rf_ppo_loc_ctE :
  (ar sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ≡ ⦗E⦘ ⨾ (ar sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗E⦘.
Proof using WF IMMCON WF_SC.
  split; [|basic_solver].
  rewrite wf_ar_rf_ppo_locE at 1; auto.
  rewrite inclusion_ct_seq_eqv_l.
    by rewrite inclusion_ct_seq_eqv_r.
Qed.

Lemma rfe_n_same_tid : rfe ∩ same_tid ⊆ ∅₂.
Proof using WF COH.
  arewrite (rfe ∩ same_tid ⊆ rfe ∩ (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘)).
  { rewrite (wf_rfeE WF) at 1. basic_solver. }
  arewrite (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘ ⊆ same_tid ∩ (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘)) by basic_solver.
  rewrite tid_sb.
  rewrite !inter_union_r.
  unionL.
  3: { rewrite (wf_rfeD WF). rewrite init_w; eauto. type_solver. }
  2: { unfolder. ins. desf.
       eapply COH. eexists. split.
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
  eapply (thread_rfe_sb WF (coherence_sc_per_loc COH)).
  basic_solver 10.
Qed.

Lemma ar_W_in_ar_int : ar sc ⨾ ⦗W⦘ ⊆ ar_int.
Proof using WF IMMCON.
  unfold ar. erewrite wf_scD with (sc:=sc); [|by apply IMMCON].
  rewrite (wf_rfeD WF). type_solver.
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
      (FINDOM : set_finite E)
      (AC : acyclic (psc ∪ rfe ∪ ar_int)) :
  exists sc, wf_sc sc /\ acyc_ext sc /\ coh_sc sc.
Proof using WF.
  cdes FINDOM.
  set (ar' := psc ∪ rfe ∪ ar_int).
  unfold acyc_ext.
  exists (⦗ E ∩₁ F ∩₁ Sc ⦘ ⨾ tot_ext findom ar' ⨾ ⦗ E ∩₁ F ∩₁ Sc ⦘).
  splits.
  { constructor.
    1,2: apply dom_helper_3; basic_solver.
    { rewrite <- restr_relE; apply transitive_restr, tot_ext_trans. }
    { unfolder; ins; desf.
      cut (tot_ext findom ar' a b \/ tot_ext findom ar' b a).
      { basic_solver 12. }
      eapply tot_ext_total; desf; eauto. }
    rewrite <- restr_relE.
    apply irreflexive_restr. by apply tot_ext_irr. }
  { unfold ar.
    apply acyclic_mon with (r:= tot_ext findom ar').
    { apply trans_irr_acyclic.
      { apply tot_ext_irr, AC. }
      apply tot_ext_trans. }
    apply inclusion_union_l; [apply inclusion_union_l|].
    { basic_solver. }
    all: subst ar'; rewrite <- tot_ext_extends; unfold ar; basic_solver. }
  unfold coh_sc.
  rotate 4.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⨾ hb ⨾ (eco ⨾ hb)^? ⨾ ⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ar'⁺).
  2: { arewrite (ar' ⊆ tot_ext findom ar') at 2.
       { apply tot_ext_extends. }
       rewrite ct_step with (r:= tot_ext findom ar') at 1.
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

Global Add Parametric Morphism: (fun G sc => ar G sc) with signature
       eq ==> same_relation ==> same_relation as ar_more.
Proof using.
  intros G r r' EQ.
  now unfold ar; rewrite EQ.
Qed.

