(******************************************************************************)

(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import CombRelations.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section SubExecution.

Variables G G' : execution.
Variables sc sc' : relation actid.

Notation "'E''" := G'.(acts_set).
Notation "'acts''" := G'.(acts).
Notation "'lab''" := G'.(lab).
Notation "'sb''" := G'.(sb).
Notation "'rf''" := G'.(rf).
Notation "'co''" := G'.(co).
Notation "'rmw''" := G'.(rmw).
Notation "'data''" := G'.(data).
Notation "'addr''" := G'.(addr).
Notation "'ctrl''" := G'.(ctrl).
Notation "'deps''" := G'.(deps).
Notation "'rmw_dep''" := G'.(rmw_dep).

Notation "'fre''" := G'.(fre).
Notation "'rfe''" := G'.(rfe).
Notation "'coe''" := G'.(coe).
Notation "'rfi''" := G'.(rfi).
Notation "'fri''" := G'.(fri).
Notation "'coi''" := G'.(coi).
Notation "'fr''" := G'.(fr).
Notation "'eco''" := G'.(eco).
Notation "'detour''" := G'.(detour).
Notation "'furr''" := (G'.(furr) sc').
Notation "'urr''" := (G'.(urr) sc').
Notation "'msg_rel''" := (G'.(msg_rel) sc').

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

Notation "'ppo''" := G'.(ppo).
Notation "'bob''" := G'.(bob).
Notation "'fwbob''" := G'.(fwbob).
Notation "'ar''" := G'.(ar).
Notation "'ar_int''" := G'.(ar_int).
Notation "'sw''" := G'.(sw).
Notation "'rs''" := G'.(rs).
Notation "'release''" := G'.(release).
Notation "'rs''" := G'.(rs).
Notation "'hb''" := G'.(hb).

Notation "'Pln''" := (fun a => is_true (is_only_pln lab' a)).
Notation "'Rlx''" := (fun a => is_true (is_rlx lab' a)).
Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).
Notation "'Acqrel''" := (fun a => is_true (is_acqrel lab' a)).
Notation "'Acq/Rel''" := (fun a => is_true (is_ra lab' a)).
Notation "'Sc''" := (fun a => is_true (is_sc lab' a)).

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'coi'" := G.(coi).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'detour'" := G.(detour).
Notation "'furr'" := (G.(furr) sc).
Notation "'urr'" := (G.(urr) sc).
Notation "'msg_rel'" := (G.(msg_rel) sc).

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

Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).
Notation "'fwbob'" := G.(fwbob).
Notation "'ar'" := G.(ar).
Notation "'ar_int'" := G.(ar_int).
Notation "'sw'" := G.(sw).
Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'hb'" := G.(hb).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Record sub_execution :=
  { sub_E: E' ⊆₁ E ;
(*   sub_lab : forall a (IN: E a), lab' a = lab a ; *)
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

Lemma sub_Acq : Acq' ≡₁ Acq.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_Rel : Rel' ≡₁ Rel.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_AcqRel : Acq/Rel' ≡₁ Acq/Rel.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_Sc : Sc' ≡₁ Sc.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_W : W' ≡₁ W.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_R : R' ≡₁ R.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_F : F' ≡₁ F.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_W_ l : W'_ l ≡₁ W_ l.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_R_ex : R_ex' ≡₁ R_ex.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_xacq : is_xacq lab' ≡₁ is_xacq lab.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_same_loc : same_loc' ≡ same_loc.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_loc : loc' = loc.
Proof. by rewrite (sub_lab SUB). Qed.
Lemma sub_val : val' = val.
Proof. by rewrite (sub_lab SUB). Qed.

Lemma sub_E_in : E' ⊆₁ E.
Proof. rewrite (sub_E SUB); basic_solver. Qed.
Lemma sub_data_in : data' ⊆ data.
Proof. rewrite sub_data; basic_solver. Qed.
Lemma sub_addr_in : addr' ⊆ addr.
Proof. rewrite sub_addr; basic_solver. Qed.
Lemma sub_ctrl_in : ctrl' ⊆ ctrl.
Proof. rewrite sub_ctrl; basic_solver. Qed.
Lemma sub_frmw_in : rmw_dep' ⊆ rmw_dep.
Proof. rewrite sub_frmw; basic_solver. Qed.
Lemma sub_rmw_in : rmw' ⊆ rmw.
Proof. rewrite sub_rmw; basic_solver. Qed.
Lemma sub_rf_in : rf' ⊆ rf.
Proof. rewrite sub_rf; basic_solver. Qed.
Lemma sub_co_in : co' ⊆ co.
Proof. rewrite sub_co; basic_solver. Qed.
Lemma sub_sc_in : sc' ⊆ sc.
Proof. rewrite sub_sc; basic_solver. Qed.

Lemma sub_W_ex_in : W_ex' ⊆₁ W_ex.
Proof. unfold Execution.W_ex; rewrite sub_rmw_in; basic_solver. Qed.
Lemma sub_W_ex_acq_in : W_ex_acq' ⊆₁ W_ex_acq.
Proof. by rewrite sub_W_ex_in, sub_xacq. Qed.

Lemma sub_sb : sb' ≡ ⦗E'⦘ ⨾  sb ⨾ ⦗E'⦘.
Proof. unfold Execution.sb; generalize sub_E_in; basic_solver 12. Qed.

Lemma sub_sb_in : sb' ⊆ sb.
Proof. rewrite sub_sb; basic_solver. Qed.


(******************************************************************************)
(** Well-Formedness **  *)
(******************************************************************************)

Lemma sub_WF : Wf G'.
Proof.
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
- apply dom_helper_3; rewrite (sub_rmw SUB), wf_rmwD, sub_R_ex, sub_W; basic_solver 12.
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
Qed.

(******************************************************************************)
(** Relations **  *)
(******************************************************************************)

Lemma sub_fwbob : fwbob' ≡ ⦗E'⦘ ⨾ fwbob ⨾ ⦗E'⦘.
Proof. 
unfold imm_common.fwbob; rewrite sub_Rel, sub_AcqRel, sub_W, sub_F, sub_sb, sub_same_loc.
basic_solver 21.
Qed.

Lemma sub_fwbob_in : fwbob' ⊆ fwbob .
Proof. rewrite sub_fwbob; basic_solver. Qed.

Lemma sub_bob : bob' ≡ ⦗E'⦘ ⨾ bob ⨾ ⦗E'⦘.
Proof. 
unfold imm_common.bob; rewrite sub_Acq, sub_fwbob, sub_R, sub_sb.
basic_solver 21.
Qed.

Lemma sub_bob_in : bob' ⊆ bob .
Proof. rewrite sub_bob; basic_solver. Qed.

Lemma sub_rfi : rfi' ≡ ⦗E'⦘ ⨾ rfi ⨾ ⦗E'⦘.
Proof. unfold Execution.rfi; rewrite sub_sb, sub_rf; basic_solver. Qed.

Lemma sub_rfi_in : rfi' ⊆ rfi.
Proof. rewrite sub_rfi; basic_solver. Qed.

Lemma sub_rfe : rfe' ≡ ⦗E'⦘ ⨾ rfe ⨾ ⦗E'⦘.
Proof. 
unfold Execution.rfe; rewrite sub_sb, (sub_rf SUB).
split; [basic_solver 15 | unfolder; ins; desf; splits; eauto; intro; desf].
Qed.

Lemma sub_rfe_in : rfe' ⊆ rfe.
Proof. rewrite sub_rfe; basic_solver. Qed.

Lemma sub_coe : coe' ≡ ⦗E'⦘ ⨾ coe ⨾ ⦗E'⦘.
Proof.
unfold Execution.coe; rewrite sub_sb, (sub_co SUB).
split; [basic_solver 15 | unfolder; ins; desf; splits; eauto; intro; desf].
Qed.

Lemma sub_coe_in : coe' ⊆ coe.
Proof. rewrite sub_coe; basic_solver. Qed.

Lemma sub_detour_in : detour' ⊆ detour.
Proof. 
unfold Execution.detour.
rewrite sub_sb, sub_coe, sub_rfe_in.
basic_solver 21.
Qed.

Lemma sub_ppo_in : ppo' ⊆ ppo.
Proof.
unfold imm_common.ppo.
rewrite sub_R_ex, sub_W, sub_R.
hahn_frame; apply inclusion_t_t.
rewrite sub_sb_in, sub_rfi_in.
rewrite sub_data_in, sub_ctrl_in, sub_addr_in, sub_frmw_in.
basic_solver 12.
Qed.

Lemma sub_fr_in : fr' ⊆ fr.
Proof.
unfold Execution.fr.
by rewrite sub_rf_in, sub_co_in.
Qed.

Lemma sub_fre_in : fre' ⊆ fre.
Proof.
rewrite (wf_freE sub_WF).
ie_unfolder.
rewrite sub_fr_in, sub_sb.
basic_solver 21.
Qed.

Lemma sub_eco_in : eco' ⊆ eco.
Proof.
unfold Execution_eco.eco.
rewrite sub_rf_in, sub_co_in, sub_fr_in.
basic_solver 21.
Qed.

Lemma sub_rs_in : rs' ⊆ rs.
Proof.
unfold imm_s_hb.rs.
by rewrite sub_rf_in, sub_rmw_in, sub_sb_in, sub_same_loc, sub_W.
Qed.

Lemma sub_release_in : release' ⊆ release.
Proof.
unfold imm_s_hb.release.
by rewrite sub_sb_in, sub_rs_in, sub_F, sub_Rel.
Qed.

Lemma sub_sw_in : sw' ⊆ sw.
Proof.
unfold imm_s_hb.sw.
by rewrite sub_sb_in, sub_release_in, sub_rf_in, sub_F, sub_Acq.
Qed.

Lemma sub_hb_in : hb' ⊆ hb.
Proof.
unfold imm_s_hb.hb.
by rewrite sub_sb_in, sub_sw_in.
Qed.

Lemma sub_ar_int_in : ar_int' ⊆ ar_int.
Proof.
unfold imm_common.ar_int.
by rewrite sub_bob_in, sub_ppo_in, sub_detour_in, sub_sb_in, sub_W_ex_acq_in, sub_W .
Qed.

Lemma sub_ar_in : ar' sc' ⊆ ar sc.
Proof.
unfold imm_s.ar.
by rewrite sub_sc_in, sub_rfe_in, sub_ar_int_in.
Qed.

Lemma sub_urr_in l : urr' l ⊆ urr l.
Proof.
unfold CombRelations.urr.
by rewrite sub_rf_in, sub_hb_in, (sub_W_ l), sub_F, sub_Sc, sub_sc_in.
Qed.

Lemma sub_furr_in : furr' ⊆ furr.
Proof.
unfold CombRelations.furr.
unfolder; ins; desf; eexists; apply sub_urr_in; eauto.
Qed.


(******************************************************************************)
(** Consistecy **  *)
(******************************************************************************)

Lemma sub_WF_SC : wf_sc G' sc'.
Proof.
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
Proof.
red; rewrite sub_hb_in, sub_eco_in; apply COH.
Qed.

Lemma sub_coh_sc (CSC: coh_sc G sc) : coh_sc G' sc'.
Proof.
red; rewrite sub_hb_in, sub_eco_in, sub_sc_in; apply CSC.
Qed.

Lemma sub_acyc_ext (ACYC: acyc_ext G sc) : acyc_ext G' sc'.
Proof.
red; rewrite sub_ar_in; apply ACYC.
Qed.

Lemma sub_rmw_atomicity (AT: rmw_atomicity G) : rmw_atomicity G'.
Proof.
red; rewrite sub_rmw_in, sub_coe_in, sub_fre_in; apply AT.
Qed.


(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma sub_detour (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') : detour' ≡ ⦗E'⦘ ⨾ detour ⨾ ⦗E'⦘.
Proof.
unfold Execution.detour, Execution.rfe.
rewrite sub_sb, sub_coe, (sub_rf SUB).
unfolder in RF_A; unfolder; splits; ins; desf; eauto 20. 
splits; eauto 20.
exists z; splits; eauto 20.
exists z; splits; eauto 20.
intro; desf.
Qed.

Lemma sub_fr (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') : fr' ≡ ⦗E'⦘ ⨾ fr ⨾ ⦗E'⦘.
Proof.
unfold Execution.fr.
rewrite (sub_rf SUB), (sub_co SUB).
unfolder in RF_A; basic_solver 21.
Qed.

Lemma sub_eco (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E')  : eco' ≡ ⦗E'⦘ ⨾ eco ⨾ ⦗E'⦘.
Proof.
unfold Execution_eco.eco.
rewrite (sub_rf SUB), (sub_co SUB), (sub_fr RF_A).
unfolder in RF_A; basic_solver 21.
Qed.

Lemma sub_comp (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E') (COMP: complete G) : complete G'.
Proof.
red; rewrite sub_R, (sub_rf SUB).
unfolder; ins.
exploit (COMP x).
generalize sub_E_in; basic_solver.
unfolder; ins; desf.
generalize (sub_E SUB).
revert RF_A.
basic_solver 21.
Qed.

Lemma sub_imm_consistent (RF_A : dom_rel (rf ⨾ ⦗ E' ⦘) ⊆₁ E')
  (IMMCON: imm_consistent G sc) : imm_consistent G' sc'.
Proof.
cdes IMMCON; red.
splits; eauto using sub_comp, sub_WF_SC, sub_coh_sc, sub_coherence, sub_acyc_ext, sub_rmw_atomicity.
Qed.

End SubExecution.


(******************************************************************************)
(** generator **  *)
(******************************************************************************)

Definition restrict (G : execution) D :=
    {| acts := filterP (fun x => D x) G.(acts);
       lab := G.(lab);
       rmw := ⦗ D ⦘ ⨾ G.(rmw) ⨾ ⦗ D ⦘;
       data := ⦗ D ⦘ ⨾G.(data) ⨾ ⦗ D ⦘;
       addr := ⦗ D ⦘ ⨾ G.(addr) ⨾ ⦗ D ⦘;
       ctrl := ⦗ D ⦘ ⨾ G.(ctrl) ⨾ ⦗ D ⦘;
       rmw_dep := ⦗ D ⦘ ⨾ G.(rmw_dep) ⨾ ⦗ D ⦘;
       rf := ⦗ D ⦘ ⨾ G.(rf) ⨾ ⦗ D ⦘;
       co := ⦗ D ⦘ ⨾ G.(co) ⨾ ⦗ D ⦘;
    |}.

Lemma restrict_E G D (IN: D ⊆₁ G.(acts_set)) :
 (restrict G D).(acts_set) ≡₁ D.
Proof.
unfold acts_set in *; unfolder in *; split; ins; desf; splits; eauto.
apply in_filterP_iff in H; desf. 
apply in_filterP_iff; splits; eauto.
Qed.

Lemma restrict_sub G sc sc' D (SC: sc' ≡ ⦗D⦘ ⨾ sc ⨾ ⦗D⦘) (IN: D ⊆₁ G.(acts_set)) : 
 sub_execution G (restrict G D) sc sc'.
Proof.
by constructor; ins; rewrite (@restrict_E G D IN).
Qed.
