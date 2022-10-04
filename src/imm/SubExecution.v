(******************************************************************************)

(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import FinExecution.
Require Import FairExecution.
Require Import FinThreads.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s.
Require Import CombRelations.
Require Import AuxRel2.

Require Import TraversalOrder.
Require Import TLSCoherency.
Require Import IordCoherency.

Set Implicit Arguments.

Section SubExecution.

Variables G G' : execution.
Variables sc sc' : relation actid.

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'deps''" := (deps G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'fre''" := (fre G').
Notation "'rfe''" := (rfe G').
Notation "'coe''" := (coe G').
Notation "'rfi''" := (rfi G').
Notation "'fri''" := (fri G').
Notation "'coi''" := (coi G').
Notation "'fr''" := (fr G').
Notation "'eco''" := (eco G').
Notation "'detour''" := (detour G').
Notation "'furr''" := ((furr G') sc').
Notation "'urr''" := ((urr G') sc').
Notation "'msg_rel''" := ((msg_rel G') sc').

Notation "'R''" := (fun a => is_true (is_r lab' a)).
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'F''" := (fun a => is_true (is_f lab' a)).
Notation "'RW''" := (R' ∪₁ W').
Notation "'FR''" := (F' ∪₁ R').
Notation "'FW''" := (F' ∪₁ W').
Notation "'W_ex''" := (W_ex G').
Notation "'W_ex_acq''" := (W_ex' ∩₁ (fun a => is_true (is_xacq lab' a))).
Notation "'R_ex''" := (fun a => is_true (R_ex lab' a)).

Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'same_loc''" := (same_loc lab').

Notation "'Loc'_' l" := (fun x => loc' x = Some l) (at level 1).
Notation "'W'_' l" := (W' ∩₁ Loc'_ l) (at level 1).
Notation "'R'_' l" := (R' ∩₁ Loc'_ l) (at level 1).

Notation "'ppo''" := (ppo G').
Notation "'bob''" := (bob G').
Notation "'fwbob''" := (fwbob G').
Notation "'ar''" := (ar G').
Notation "'ar_int''" := (ar_int G').
Notation "'sw''" := (sw G').
Notation "'rs''" := (rs G').
Notation "'release''" := (release G').
Notation "'rs''" := (rs G').
Notation "'hb''" := (hb G').

Notation "'Pln''" := (fun a => is_true (is_only_pln lab' a)).
Notation "'Rlx''" := (fun a => is_true (is_rlx lab' a)).
Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).
Notation "'Acqrel''" := (fun a => is_true (is_acqrel lab' a)).
Notation "'Acq/Rel''" := (fun a => is_true (is_ra lab' a)).
Notation "'Sc''" := (fun a => is_true (is_sc lab' a)).

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'deps'" := (deps G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'coi'" := (coi G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'detour'" := (detour G).
Notation "'furr'" := ((furr G) sc).
Notation "'urr'" := ((urr G) sc).
Notation "'msg_rel'" := ((msg_rel G) sc).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'ppo'" := (ppo G).
Notation "'bob'" := (bob G).
Notation "'fwbob'" := (fwbob G).
Notation "'ar'" := (ar G).
Notation "'ar_int'" := (ar_int G).
Notation "'sw'" := (sw G).
Notation "'rs'" := (rs G).
Notation "'release'" := (release G).
Notation "'hb'" := (hb G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Record sub_execution :=
  { sub_E: E' ⊆₁ E ;
    sub_threads : threads_set' ≡₁ threads_set ;
    sub_lab : lab' = lab ;
    sub_rmw : rmw'  ≡ ⦗E'⦘ ⨾ rmw ⨾ ⦗E'⦘ ;
    sub_data : data'  ≡ ⦗E'⦘ ⨾ data ⨾ ⦗E'⦘ ;
    sub_addr : addr'  ≡ ⦗E'⦘ ⨾ addr ⨾ ⦗E'⦘ ;
    sub_ctrl : ctrl'  ≡ ⦗E'⦘ ⨾ ctrl ⨾ ⦗E'⦘ ;
    sub_frmw : rmw_dep'  ≡ ⦗E'⦘ ⨾ rmw_dep ⨾ ⦗E'⦘ ;
    sub_rf : rf'  ≡ ⦗E'⦘ ⨾ rf ⨾ ⦗E'⦘ ;
    sub_co : co'  ≡ ⦗E'⦘ ⨾ co ⨾ ⦗E'⦘ ;
    sub_sc : sc'  ≡ ⦗E'⦘ ⨾ sc ⨾ ⦗E'⦘ ;
  }.

Hypothesis INIT : is_init ∩₁ E ⊆₁ E'.

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis SUB : sub_execution.
Hypothesis RMWCLOS : codom_rel (⦗E'⦘ ⨾ rmw) ⊆₁ E'.

Lemma sub_Acq : Acq' ≡₁ Acq.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_Rel : Rel' ≡₁ Rel.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_AcqRel : Acq/Rel' ≡₁ Acq/Rel.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_Sc : Sc' ≡₁ Sc.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_W : W' ≡₁ W.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_R : R' ≡₁ R.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_F : F' ≡₁ F.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_W_ l : W'_ l ≡₁ W_ l.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_R_ex : R_ex' ≡₁ R_ex.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_xacq : is_xacq lab' ≡₁ is_xacq lab.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_same_loc : same_loc' ≡ same_loc.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_loc : loc' = loc.
Proof using SUB. by rewrite (sub_lab SUB). Qed.
Lemma sub_val : val' = val.
Proof using SUB. by rewrite (sub_lab SUB). Qed.

Lemma sub_E_in : E' ⊆₁ E.
Proof using SUB. rewrite (sub_E SUB); basic_solver. Qed.
Lemma sub_data_in : data' ⊆ data.
Proof using SUB. rewrite sub_data; basic_solver. Qed.
Lemma sub_addr_in : addr' ⊆ addr.
Proof using SUB. rewrite sub_addr; basic_solver. Qed.
Lemma sub_ctrl_in : ctrl' ⊆ ctrl.
Proof using SUB. rewrite sub_ctrl; basic_solver. Qed.
Lemma sub_frmw_in : rmw_dep' ⊆ rmw_dep.
Proof using SUB. rewrite sub_frmw; basic_solver. Qed.
Lemma sub_rmw_in : rmw' ⊆ rmw.
Proof using SUB. rewrite sub_rmw; basic_solver. Qed.
Lemma sub_rf_in : rf' ⊆ rf.
Proof using SUB. rewrite sub_rf; basic_solver. Qed.
Lemma sub_co_in : co' ⊆ co.
Proof using SUB. rewrite sub_co; basic_solver. Qed.
Lemma sub_sc_in : sc' ⊆ sc.
Proof using SUB. rewrite sub_sc; basic_solver. Qed.

Lemma sub_W_ex_in : W_ex' ⊆₁ W_ex.
Proof using SUB. unfold Execution.W_ex; rewrite sub_rmw_in; basic_solver. Qed.
Lemma sub_W_ex_acq_in : W_ex_acq' ⊆₁ W_ex_acq.
Proof using SUB. by rewrite sub_W_ex_in, sub_xacq. Qed.

Lemma sub_sb : sb' ≡ ⦗E'⦘ ⨾  sb ⨾ ⦗E'⦘.
Proof using SUB. unfold Execution.sb; generalize sub_E_in; basic_solver 12. Qed.

Lemma sub_sb_in : sb' ⊆ sb.
Proof using SUB. rewrite sub_sb; basic_solver. Qed.


(******************************************************************************)
(** Well-Formedness **  *)
(******************************************************************************)

Lemma sub_WF : Wf G'.
Proof using INIT SUB WF.
constructor.
- by ins; desf; apply (wf_index WF); splits; eauto; apply sub_E_in.
- by rewrite (sub_data SUB), data_in_sb, sub_sb.
- apply dom_helper_3; rewrite (sub_data SUB), wf_dataD, sub_R, sub_W; basic_solver.
- by rewrite (sub_addr SUB), addr_in_sb, sub_sb.
- apply dom_helper_3; rewrite (sub_addr SUB), wf_addrD, sub_R, sub_W; basic_solver 12.
- by rewrite (sub_ctrl SUB), ctrl_in_sb, sub_sb.
- rewrite (sub_ctrl SUB), wf_ctrlD, sub_R; basic_solver 12.
- rewrite (sub_ctrl SUB), sub_sb. 
  generalize (ctrl_sb WF); basic_solver 12.
- apply dom_helper_3; rewrite (sub_rmw SUB), wf_rmwD, sub_R, sub_W; basic_solver 12.
- rewrite sub_rmw_in, sub_same_loc; apply WF.
- rewrite (sub_rmw SUB).
  unfolder; ins; desf; splits.
  apply sub_sb; generalize (rmw_in_sb WF); basic_solver 12.
  ins; eapply  (wf_rmwi WF); eauto; apply (sub_sb_in); edone.
- apply dom_helper_3; rewrite (sub_rf SUB); basic_solver.
- apply dom_helper_3; rewrite (sub_rf SUB), wf_rfD, sub_R, sub_W; basic_solver 12.
- rewrite sub_rf_in, sub_same_loc; apply WF.
- rewrite sub_val, sub_rf_in; apply WF.
- rewrite sub_rf_in; apply WF.
- apply dom_helper_3; rewrite (sub_co SUB); basic_solver 12.
- apply dom_helper_3; rewrite (sub_co SUB), wf_coD, sub_W; basic_solver 12.
- rewrite sub_co_in, sub_same_loc; apply WF.
- rewrite (sub_co SUB), <- restr_relE; apply transitive_restr, WF.
- intro ol. 
  rewrite (sub_co SUB), sub_W.
  unfolder; ins; eapply (wf_co_total WF) in NEQ.
  by desf; eauto.
  by unfolder; desf; splits; auto; apply sub_E_in.
  by unfolder; desf; splits; auto; [apply sub_E_in| rewrite <- sub_loc].
- rewrite sub_co_in; apply WF.
- ins; desf.
  apply INIT; unfolder; splits; eauto.
  apply (wf_init WF); splits; exists b; splits; eauto.
  by apply sub_E_in.
  generalize sub_loc; congruence.
- ins; rewrite (sub_lab SUB); apply WF.
- by rewrite (sub_frmw SUB), rmw_dep_in_sb, sub_sb.
- apply dom_helper_3; rewrite (sub_frmw SUB), wf_rmw_depD, sub_R, sub_R_ex; basic_solver 12.
- ins. apply sub_threads; auto. apply WF.
  apply sub_E; auto.
Qed.

(******************************************************************************)
(** Relations **  *)
(******************************************************************************)

Lemma sub_fwbob : fwbob' ≡ ⦗E'⦘ ⨾ fwbob ⨾ ⦗E'⦘.
Proof using SUB. 
unfold imm_bob.fwbob; rewrite sub_Rel, sub_AcqRel, sub_W, sub_F, sub_sb, sub_same_loc.
basic_solver 21.
Qed.

Lemma sub_fwbob_in : fwbob' ⊆ fwbob .
Proof using SUB. rewrite sub_fwbob; basic_solver. Qed.

Lemma sub_bob : bob' ≡ ⦗E'⦘ ⨾ bob ⨾ ⦗E'⦘.
Proof using SUB. 
unfold imm_bob.bob; rewrite sub_Acq, sub_fwbob, sub_R, sub_sb.
basic_solver 21.
Qed.

Lemma sub_bob_in : bob' ⊆ bob .
Proof using SUB. rewrite sub_bob; basic_solver. Qed.

Lemma sub_rfi : rfi' ≡ ⦗E'⦘ ⨾ rfi ⨾ ⦗E'⦘.
Proof using SUB. unfold Execution.rfi; rewrite sub_sb, sub_rf; basic_solver. Qed.

Lemma sub_rfi_in : rfi' ⊆ rfi.
Proof using SUB. rewrite sub_rfi; basic_solver. Qed.

Lemma sub_rfe : rfe' ≡ ⦗E'⦘ ⨾ rfe ⨾ ⦗E'⦘.
Proof using SUB. 
unfold Execution.rfe; rewrite sub_sb, (sub_rf SUB).
split; [basic_solver 15 | unfolder; ins; desf; splits; eauto; intro; desf].
Qed.

Lemma sub_rfe_in : rfe' ⊆ rfe.
Proof using SUB. rewrite sub_rfe; basic_solver. Qed.

Lemma sub_coe : coe' ≡ ⦗E'⦘ ⨾ coe ⨾ ⦗E'⦘.
Proof using SUB.
unfold Execution.coe; rewrite sub_sb, (sub_co SUB).
split; [basic_solver 15 | unfolder; ins; desf; splits; eauto; intro; desf].
Qed.

Lemma sub_coe_in : coe' ⊆ coe.
Proof using SUB. rewrite sub_coe; basic_solver. Qed.

Lemma sub_detour_in : detour' ⊆ detour.
Proof using SUB. 
unfold Execution.detour.
rewrite sub_sb, sub_coe, sub_rfe_in.
basic_solver 21.
Qed.

Lemma sub_same_loc_in : same_loc' ⊆ same_loc.
Proof using SUB.
by rewrite (sub_lab SUB).
Qed.

Lemma sub_ppo_in : ppo' ⊆ ppo.
Proof using SUB.
unfold imm_s_ppo.ppo.
rewrite sub_W, sub_R.
hahn_frame; apply inclusion_t_t.
apply union_mori.
{ rewrite sub_sb_in, sub_rfi_in.
  rewrite sub_data_in, sub_ctrl_in, sub_addr_in, sub_frmw_in.
  rewrite sub_rmw_in at 1.
  basic_solver 12. }
rewrite (dom_l (@wf_sbE G')).
rewrite sub_R_ex, sub_sb_in.
unfolder. ins. desf.
Qed.

Lemma sub_fr_in : fr' ⊆ fr.
Proof using SUB.
unfold Execution.fr.
by rewrite sub_rf_in, sub_co_in.
Qed.

Lemma sub_fre_in : fre' ⊆ fre.
Proof using INIT SUB WF.
rewrite (wf_freE sub_WF).
ie_unfolder.
rewrite sub_fr_in, sub_sb.
basic_solver 21.
Qed.

Lemma sub_eco_in : eco' ⊆ eco.
Proof using SUB.
unfold Execution_eco.eco.
rewrite sub_rf_in, sub_co_in, sub_fr_in.
basic_solver 21.
Qed.

Lemma sub_rs_in : rs' ⊆ rs.
Proof using SUB.
unfold imm_s_hb.rs.
by rewrite sub_rf_in, sub_rmw_in, sub_sb_in, sub_same_loc, sub_W.
Qed.

Lemma sub_release_in : release' ⊆ release.
Proof using SUB.
unfold imm_s_hb.release.
by rewrite sub_sb_in, sub_rs_in, sub_F, sub_Rel.
Qed.

Lemma sub_sw_in : sw' ⊆ sw.
Proof using SUB.
unfold imm_s_hb.sw.
by rewrite sub_sb_in, sub_release_in, sub_rf_in, sub_F, sub_Acq.
Qed.

Lemma sub_hb_in : hb' ⊆ hb.
Proof using SUB.
unfold imm_s_hb.hb.
by rewrite sub_sb_in, sub_sw_in.
Qed.

Lemma sub_ar_int_in : ar_int' ⊆ ar_int.
Proof using SUB.
unfold imm_s_ppo.ar_int.
rewrite sub_bob_in, sub_ppo_in, sub_detour_in, sub_sb_in.
rewrite sub_W_ex_acq_in, sub_W.
rewrite sub_W_ex_in, sub_rfi_in.
rewrite sub_R, sub_Acq.
done.
Qed.

Lemma sub_ar_in : ar' sc' ⊆ ar sc.
Proof using SUB.
unfold imm_s.ar.
by rewrite sub_sc_in, sub_rfe_in, sub_ar_int_in.
Qed.

Lemma sub_urr_in l : urr' l ⊆ urr l.
Proof using SUB.
unfold CombRelations.urr.
by rewrite sub_rf_in, sub_hb_in, (sub_W_ l), sub_F, sub_Sc, sub_sc_in.
Qed.

Lemma sub_furr_in : furr' ⊆ furr.
Proof using SUB.
unfold CombRelations.furr.
unfolder; ins; desf; eexists; apply sub_urr_in; eauto.
Qed.

Lemma sub_is_ta_propagate_to_G :
  is_ta_propagate_to_G G' ≡₁ is_ta_propagate_to_G G.
Proof using SUB. 
  unfold is_ta_propagate_to_G.
  now rewrite sub_threads.
Qed. 

Lemma sub_SB : SB G' sc' ⊆ SB G sc.
Proof using SUB. 
  unfold SB, RF, sb; ins.
  hahn_frame; apply map_rel_mori; auto.
  try apply clos_trans_mori.
  rewrite sub_sc, sub_E; auto using SUB.
  clear; basic_solver.
Qed.

Lemma sub_RF : RF G' ⊆ RF G.
Proof using SUB. 
  unfold SB, RF, sb; ins.
  hahn_frame; apply map_rel_mori; auto.
  try apply clos_trans_mori.
  rewrite sub_rf, sub_W; auto using SUB.
  clear; basic_solver.
Qed.

Lemma sub_FWBOB : FWBOB G' ⊆ FWBOB G.
Proof using SUB.
  unfold FWBOB; ins. 
  rewrite sub_fwbob; eauto using SUB; ins.
  rewrite sub_W; eauto using SUB; ins.
  clear; basic_solver 20.
Qed.

Lemma sub_AR : AR G' sc' ⊆ AR G sc.
Proof using SUB.
  unfold AR; ins.
  rewrite sub_ar_in, sub_ppo_in, sub_rf, sub_W; eauto using SUB.
  rewrite sub_same_loc; eauto using SUB.
  repeat (apply seq_mori; try easy).
  apply map_rel_mori; auto.
  repeat (apply seq_mori; try easy).
  apply clos_trans_mori.
  clear; basic_solver 10.
Qed.

Lemma sub_IPROP : IPROP G' ⊆ IPROP G.
Proof using SUB.
  unfold IPROP.
  rewrite sub_is_ta_propagate_to_G.
  now rewrite sub_W; eauto using SUB.
Qed.
 
Lemma sub_PROP : PROP G' sc' ⊆ PROP G sc.
Proof using SUB.
  unfold PROP.
  rewrite sub_is_ta_propagate_to_G.
  repeat (apply seq_mori; try easy).
  apply inter_rel_mori; try easy.
  apply map_rel_mori; auto.
  by rewrite sub_furr_in, sub_co_in, sub_W.   
Qed.

Lemma sub_iord : iord G' sc' ⊆ iord G sc.
Proof using SUB.
  unfold iord.
  apply restr_rel_mori.
  { rewrite sub_E; eauto using SUB. }
  rewrite sub_SB, sub_RF, sub_FWBOB, sub_AR, sub_IPROP, sub_PROP.
  easy.
Qed.

(******************************************************************************)
(** Consistecy **  *)
(******************************************************************************)

Lemma sub_WF_SC : wf_sc G' sc'.
Proof using SUB WF_SC.
constructor.
- apply dom_helper_3; rewrite (sub_sc SUB); basic_solver.
- apply dom_helper_3; rewrite (sub_sc SUB), (wf_scD WF_SC).
  rewrite sub_F, sub_Sc; basic_solver 12.
- rewrite (sub_sc SUB), <- restr_relE; apply transitive_restr, WF_SC.
- rewrite (sub_sc SUB), sub_F, sub_Sc.
  unfolder; ins; eapply (wf_sc_total WF_SC) in NEQ.
  by desf; eauto.
  by unfolder; desf; splits; auto; apply sub_E_in.
  by unfolder; desf; splits; auto; apply sub_E_in.
- rewrite sub_sc_in; apply WF_SC.
Qed.

Lemma sub_coherence (COH: coherence G) : coherence G'.
Proof using SUB.
red; rewrite sub_hb_in, sub_eco_in; apply COH.
Qed.

Lemma sub_coh_sc (CSC: coh_sc G sc) : coh_sc G' sc'.
Proof using SUB.
red; rewrite sub_hb_in, sub_eco_in, sub_sc_in; apply CSC.
Qed.

Lemma sub_acyc_ext (ACYC: acyc_ext G sc) : acyc_ext G' sc'.
Proof using SUB.
red; rewrite sub_ar_in; apply ACYC.
Qed.

Lemma sub_rmw_atomicity (AT: rmw_atomicity G) : rmw_atomicity G'.
Proof using INIT SUB WF.
red; rewrite sub_rmw_in, sub_coe_in, sub_fre_in; apply AT.
Qed.


(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma sub_detour (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') : detour' ≡ ⦗E'⦘ ⨾ detour ⨾ ⦗E'⦘.
Proof using SUB.
unfold Execution.detour, Execution.rfe.
rewrite sub_sb, sub_coe, (sub_rf SUB).
unfolder in RF_A; unfolder; splits; ins; desf; eauto 20. 
splits; eauto 20.
exists z; splits; eauto 20.
exists z; splits; eauto 20.
intro; desf.
Qed.

Lemma sub_fr (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') : fr' ≡ ⦗E'⦘ ⨾ fr ⨾ ⦗E'⦘.
Proof using SUB.
unfold Execution.fr.
rewrite (sub_rf SUB), (sub_co SUB).
unfolder in RF_A; basic_solver 21.
Qed.

Lemma sub_eco (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E')  : eco' ≡ ⦗E'⦘ ⨾ eco ⨾ ⦗E'⦘.
Proof using SUB.
unfold Execution_eco.eco.
rewrite (sub_rf SUB), (sub_co SUB), (sub_fr RF_A).
unfolder in RF_A; basic_solver 21.
Qed.

Lemma sub_comp (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') (COMP: complete G) : complete G'.
Proof using SUB.
red; rewrite sub_R, (sub_rf SUB).
unfolder; ins.
edestruct (COMP x); eauto.
{ generalize sub_E_in; basic_solver. }
unfolder; ins; desf.
generalize (sub_E SUB).
revert RF_A.
basic_solver 21.
Qed.

Lemma sub_imm_consistent (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E')
  (IMMCON: imm_consistent G sc) : imm_consistent G' sc'.
Proof using INIT SUB WF WF_SC.
cdes IMMCON; red.
splits; eauto using sub_comp, sub_WF_SC, sub_coh_sc, sub_coherence, sub_acyc_ext, sub_rmw_atomicity.
Qed.

End SubExecution.


(******************************************************************************)
(** generator **  *)
(******************************************************************************)

Definition restrict (G : execution) D :=
    {| acts_set := D ∩₁ G.(acts_set);
       threads_set := threads_set G;
       lab := (lab G);
       rmw := ⦗ D ⦘ ⨾ (rmw G) ⨾ ⦗ D ⦘;
       data := ⦗ D ⦘ ⨾(data G) ⨾ ⦗ D ⦘;
       addr := ⦗ D ⦘ ⨾ (addr G) ⨾ ⦗ D ⦘;
       ctrl := ⦗ D ⦘ ⨾ (ctrl G) ⨾ ⦗ D ⦘;
       rmw_dep := ⦗ D ⦘ ⨾ (rmw_dep G) ⨾ ⦗ D ⦘;
       rf := ⦗ D ⦘ ⨾ (rf G) ⨾ ⦗ D ⦘;
       co := ⦗ D ⦘ ⨾ (co G) ⨾ ⦗ D ⦘;
    |}.

Lemma restrict_E G D (IN: D ⊆₁ (acts_set G)) :
 (acts_set (restrict G D)) ≡₁ D.
Proof using.
  unfolder in *; split; ins; desf; splits; eauto.
  { apply H. }
  split; auto.
Qed.

Lemma restrict_sub G sc sc' D (SC: sc' ≡ ⦗D⦘ ⨾ sc ⨾ ⦗D⦘) (IN: D ⊆₁ (acts_set G)) : 
 sub_execution G (restrict G D) sc sc'.
Proof using.
by constructor; ins; rewrite (@restrict_E G D IN).
Qed.

Lemma events_separation G:
  acts_set G ≡₁ ⋃₁ t, acts_set (restrict G (Tid_ t)).
Proof using.
  unfold restrict. simpl.
  rewrite set_bunion_inter_compat_r, set_interC, <- set_bunion_inter_compat_l.
  apply set_bunion_separation. 
Qed.

Lemma fin_exec_bounded_threads G b
      (TB: threads_bound G b)
      (FIN_B: forall t (LTB: BinPos.Pos.lt t b), fin_exec (restrict G (Tid_ t))):
  fin_exec G. 
Proof using.
  red. rewrite events_separation, <- set_bunion_minus_compat_r.
  rewrite set_full_split with (S := fun t => BinPos.Pos.lt t b).
  rewrite set_bunion_union_l. apply set_finite_union. split.
  2: { exists nil. unfold restrict. simpl. unfolder. ins. desc.
       red in TB. apply TB in IN2. congruence. }
  apply set_finite_bunion; [by apply BinPos_lt_fin| done].
Qed.

Lemma restrict_fair G (S: actid -> Prop) (FAIR: mem_fair G):
  mem_fair (restrict G S).
Proof using.
  unfold restrict, mem_fair, fr. simpl. destruct FAIR as [FSco FSfr].
  split.
  { eapply fsupp_mori; [| by apply FSco]. red. basic_solver. }
  eapply fsupp_mori; [| by apply FSfr]. red. unfold fr. basic_solver.
Qed.

Lemma restrict_threads_bound (G: execution) (b: thread_id) (S: actid -> Prop)
      (BOUND: threads_bound G b):
  threads_bound (restrict G S) b.
Proof using.
  unfold restrict, threads_bound. simpl.
  ins. apply BOUND, Ge.
Qed. 
