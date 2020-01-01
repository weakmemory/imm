From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_bob.
Require Import CertCOhelper.
Require Import imm_common_more.

Require Import CombRelations.
Require Import TraversalConfig.
Require Import TraversalConfigAlt.
Require Import TraversalConfigAltOld.

Set Implicit Arguments.
Remove Hints plus_n_O.


Section CertExec.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Variable G : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'E'" := G.(acts_set).
Notation "'Gacts'" := G.(acts).
Notation "'Glab'" := G.(lab).
Notation "'Gsb'" := G.(sb).
Notation "'Grf'" := G.(rf).
Notation "'Gco'" := G.(co).
Notation "'Grmw'" := G.(rmw).
Notation "'Gdata'" := G.(data).
Notation "'Gaddr'" := G.(addr).
Notation "'Gctrl'" := G.(ctrl).
Notation "'Gdeps'" := G.(deps).
Notation "'Grmw_dep'" := G.(rmw_dep).

Notation "'Gfre'" := G.(fre).
Notation "'Grfe'" := G.(rfe).
Notation "'Gcoe'" := G.(coe).
Notation "'Grfi'" := G.(rfi).
Notation "'Gfri'" := G.(fri).
Notation "'Gcoi'" := G.(coi).
Notation "'Gfr'" := G.(fr).
Notation "'Geco'" := G.(eco).
Notation "'Gdetour'" := G.(detour).
Notation "'Gsw'" := G.(sw).
Notation "'Grelease'" := G.(release).
Notation "'Grs'" := G.(rs).
Notation "'Ghb'" := G.(hb).
Notation "'Gppo'" := G.(ppo).
Notation "'Gbob'" := G.(bob).
Notation "'Gfwbob'" := G.(fwbob).
Notation "'Gar'" := (G.(ar) sc).
Notation "'Gar_int'" := (G.(ar_int)).
Notation "'Gurr'" := (G.(urr) sc).
Notation "'Gfurr'" := (G.(furr) sc).
Notation "'Gmsg_rel'" := (G.(msg_rel) sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := G.(W_ex).
Notation "'GW_ex_acq'" := (GW_ex ∩₁ (fun a => is_true (is_xacq Glab a))).

Notation "'Loc_' l" := (fun x => Gloc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln Glab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx Glab a)).
Notation "'Rel'" := (fun a => is_true (is_rel Glab a)).
Notation "'Acq'" := (fun a => is_true (is_acq Glab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel Glab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra Glab a)).
Notation "'Sc'" := (fun a => is_true (is_sc Glab a)).
Notation "'xacq'" := (fun a => is_true (is_xacq Glab a)).

Variable T : trav_config.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).

Variable thread : BinNums.positive.

Lemma tid_set_dec : Tid_ thread ∪₁ NTid_ thread ≡₁ (fun x => True).
Proof. unfolder; split; ins; desf; tauto. Qed.

Hypothesis WF : Wf G.
Hypothesis WF_SC : wf_sc G sc.
Hypothesis RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.
Hypothesis TCCOH : tc_coherent G sc T.
Hypothesis ACQEX : GW_ex ⊆₁ GW_ex_acq.
Hypothesis ACYC_EXT : acyc_ext G sc.
Hypothesis CSC : coh_sc G sc.
Hypothesis COH : coherence G.
Hypothesis AT : rmw_atomicity G.

Hypothesis IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Hypothesis E_to_I: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘).
Hypothesis Grfe_E : dom_rel Grfe ⊆₁ I.
Hypothesis W_ex_E: GW_ex ∩₁ E ⊆₁ I.
Hypothesis E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Hypothesis COMP_ACQ: forall r (IN: (E ∩₁ R ∩₁ Acq) r), exists w, Grf w r.
Hypothesis urr_helper: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Hypothesis urr_helper_C: dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Hypothesis W_hb_sc_hb_to_I_NTid: dom_rel (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Hypothesis detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Hypothesis hb_sc_hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gsb.
Hypothesis COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis COMP_PPO : dom_rel (Gppo ⨾ ⦗I⦘) ∩₁ R ⊆₁ codom_rel Grf.
Hypothesis TCCOH_rst_new_T : tc_coherent G sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).

(******************************************************************************)
(**  the set D   *)
(******************************************************************************)

Definition D := C ∪₁ I ∪₁ (E ∩₁ NTid_ thread) ∪₁
  dom_rel (Grfi^? ⨾ Gppo ⨾ ⦗ I ⦘) ∪₁ 
  (* TODO: potential fix for new_ppo *)
  (* codom_rel (⦗I⦘ ⨾ Grfi) ∪₁ codom_rel (Grfe ⨾ (rmw ;; rfi)^* ;; ⦗ R ∩₁ Acq ⦘). *)
  codom_rel (⦗I⦘ ⨾ Grfi) ∪₁ codom_rel (Grfe ⨾  ⦗ R ∩₁ Acq ⦘).

(*   (E ∩₁ R ∩₁ Acq ∩₁ codom_rel (⦗I⦘ ⨾ Grfi)). *)

(* Definition determined :=
  dom_rel (rmw ⨾ ⦗ NTid_ thread ∩₁ issued T ⦘) \ codom_rel (⦗ set_compl W_ex⦘⨾ rfi).
 *)

Lemma C_in_D : C ⊆₁ D.
Proof. unfold D; basic_solver 12. Qed.
Lemma I_in_D : I ⊆₁ D.
Proof. unfold D; basic_solver 12. Qed.
Lemma D_in_E : D ⊆₁ E.
Proof. 
unfold D.
rewrite (wf_ppoE WF), (wf_rfiE WF), (wf_rfeE WF), (coveredE TCCOH).
rewrite (issuedE TCCOH) at 1.
basic_solver 21. 
Qed.

Lemma D_init : E ∩₁ is_init ⊆₁ D.
Proof. cdes TCCOH; generalize ICOV; unfold D; basic_solver 12. Qed.

Lemma dom_addr_in_D : dom_rel Gaddr ⊆₁ D.
Proof.
rewrite (dom_r (wf_addrE WF)).
rewrite E_to_I.
rewrite id_union; relsf; unionL; splits.
- rewrite (addr_in_sb WF).
  generalize (dom_sb_covered TCCOH).
  unfold D; basic_solver 21.
- rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  generalize (issuedW TCCOH); basic_solver.
  rewrite (dom_l (wf_addrD WF)), !seqA.
  arewrite (⦗R⦘ ⨾ Gaddr ⨾ Gsb^? ⨾ ⦗W⦘ ⊆ Gppo).
  unfold ppo; rewrite <- ct_step; basic_solver 12.
  unfold D; basic_solver 21.
Qed.

Lemma dom_ctrl_in_D : dom_rel Gctrl ⊆₁ D.
Proof.
rewrite (dom_r (wf_ctrlE WF)).
rewrite E_to_I.
rewrite id_union; relsf; unionL; splits.
- rewrite (ctrl_in_sb WF).
  generalize (dom_sb_covered TCCOH).
  by unfold D; basic_solver 12.
- rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  generalize (issuedW TCCOH); basic_solver.
  rewrite (wf_ctrlD WF), !seqA.
  arewrite (Gctrl ⨾ Gsb^? ⊆ Gctrl).
  generalize (ctrl_sb WF); basic_solver 21.
  arewrite (⦗R⦘ ⨾ Gctrl ⨾ ⦗W⦘ ⊆ Gppo).
  unfold ppo; rewrite <- ct_step; basic_solver 12.
  by unfold D; basic_solver 21.
Qed.

Lemma dom_frmw_in_D : dom_rel Grmw_dep ⊆₁ D.
Proof.
rewrite (dom_r (wf_rmw_depE WF)).
rewrite E_to_I.
rewrite id_union; relsf; unionL; splits.
- rewrite (rmw_dep_in_sb WF).
  generalize (dom_sb_covered TCCOH).
  by unfold D; basic_solver 12.
- rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  generalize (issuedW TCCOH); basic_solver.
  rewrite (dom_l (wf_rmw_depD WF)), !seqA.
  arewrite (⦗R⦘ ⨾ Grmw_dep ⨾ Gsb^? ⨾ ⦗W⦘ ⊆ Gppo).
  2: unfold D; basic_solver 21.
  unfold ppo; hahn_frame.
  rewrite <- ct_step. basic_solver 12.
Qed.

Lemma dom_rmw_in_D : dom_rel Grmw ⊆₁ D.
Proof.
  rewrite (dom_r (wf_rmwE WF)).
  rewrite rmw_W_ex. rewrite !seqA.
  rewrite <- id_inter.
  rewrite W_ex_E.
  rewrite WF.(rmw_in_ppo).
  unfold D. basic_solver 10.
Qed.

Lemma Rex_in_D (REX_IN_DEPS : GR_ex ⊆₁ dom_rel (Gctrl ∪ Grmw)) : GR_ex ∩₁ E ⊆₁ D.
Proof.
  rewrite REX_IN_DEPS.
  rewrite dom_union.
  rewrite dom_ctrl_in_D, dom_rmw_in_D.
  basic_solver.
Qed.

Lemma dom_detour_D : dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I.
Proof.
  unfold D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (dom_l (wf_detourD WF)).
    rewrite detour_in_sb.
    generalize dom_sb_covered, w_covered_issued; basic_solver 21. }
  { rewrite (dom_r (wf_detourD WF)).
    rewrite (issuedW TCCOH) at 1; type_solver. }
  { apply detour_E. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE; relsf; unionL; splits.
    2: by rewrite (dom_r (wf_detourD WF)), (dom_l (wf_rfiD WF)); type_solver.
    etransitivity.
    2: eapply tc_dr_pb_I; eauto; apply tc_coherent_implies_tc_coherent_alt; eauto.
    basic_solver 10. }
  { rewrite dom_rel_eqv_codom_rel, transp_seq; relsf.
    sin_rewrite (detour_transp_rfi WF); rels. }
  rewrite (dom_r (wf_rfeE WF)).
  relsf.
  transitivity (dom_rel (Gdetour ⨾ ⦗R ∩₁ Acq⦘ ⨾ ⦗E⦘)).
  basic_solver 21.
  generalize detour_Acq_E; basic_solver 21.
Qed.

Lemma dom_data_D: dom_rel (Gdata ⨾ ⦗D⦘) ⊆₁ D.
Proof.
unfold D.
rewrite !id_union; relsf; unionL; splits.
- rewrite (data_in_sb WF).
  generalize dom_sb_covered; basic_solver 21.
- rewrite (data_in_ppo WF).
  basic_solver 12.
- rewrite (data_in_sb WF).
  rewrite (dom_l (@wf_sbE G)) at 1.
  rewrite sb_tid_init' at 1; relsf; unionL; split.
  by unionR left -> left -> left -> right; unfold same_tid; unfolder; ins; desf; eauto 20.
  arewrite (⦗E⦘ ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ⦗D⦘).
  generalize D_init; basic_solver.
  arewrite (dom_rel (⦗D⦘ ⨾ Gsb ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ D) by basic_solver.
  unfold D; basic_solver 12.
- rewrite dom_rel_eqv_dom_rel.
  rewrite crE at 1; relsf; unionL; splits.
  rewrite (dom_r (wf_dataD WF)), (dom_l (@wf_ppoD G)); type_solver.
  rewrite (data_in_ppo WF).
  sin_rewrite ppo_rfi_ppo; basic_solver 21.
- rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfiD WF)); type_solver.
- rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)); type_solver.
Qed.

Lemma dom_sb_F_AcqRel_in_CI : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq/Rel⦘) ⊆₁ C ∪₁ I.
Proof.
rewrite E_to_I.
unfold D.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_sb_covered; basic_solver 21.
- arewrite (⦗dom_rel (Gsb^? ⨾ ⦗I⦘) ∩₁ F ∩₁ Acq/Rel⦘ ⊆ ⦗dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ Gsb^? ⨾ ⦗I⦘)⦘).
  basic_solver 12.
  rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ Gsb^? ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ Gsb).
  case_refl _.
  rewrite (issuedW TCCOH); type_solver.
  generalize (dom_F_sb_issued TCCOH). basic_solver 12.
  generalize dom_sb_covered; basic_solver 21.
Qed.

Lemma dom_sb_F_AcqRel_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq/Rel⦘) ⊆₁ D.
Proof.
rewrite dom_sb_F_AcqRel_in_CI, C_in_D, I_in_D; relsf.
Qed.

Lemma dom_sb_F_Acq_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Acq⦘) ⊆₁ D.
Proof. 
arewrite (Acq ⊆₁ Acq/Rel) by mode_solver. 
apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma dom_sb_F_Rel_in_D : dom_rel (Gsb ⨾ ⦗E ∩₁ F ∩₁ Rel⦘) ⊆₁ D.
Proof.
arewrite (Rel ⊆₁ Acq/Rel) by mode_solver. 
apply dom_sb_F_AcqRel_in_D.
Qed.

Lemma R_Acq_codom_rfe : (R ∩₁ Acq ∩₁ codom_rel (Grfe)) ⊆₁ D.
Proof.
unfold D; basic_solver 21.
Qed.

Lemma R_Acq_codom_W_ex_rfi : (R ∩₁ Acq ∩₁ codom_rel (⦗GW_ex⦘ ⨾ Grfi)) ⊆₁ D.
Proof.
rewrite (dom_l (wf_rfiE WF)).
arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗GW_ex ∩₁ E⦘) by basic_solver.
rewrite W_ex_E.
unfold D.
basic_solver 21.
Qed.

Lemma dom_rfi_D : dom_rel (Grfi ⨾ ⦗D⦘) ⊆₁ D.
Proof.
unfold D.
rewrite !id_union; relsf; unionL; splits.
- ie_unfolder; generalize dom_rf_covered; basic_solver 21.
- rewrite (dom_r (wf_rfiD WF)), (issuedW TCCOH) at 1; type_solver.
- arewrite (Grfi ⊆ Gsb).
    rewrite (dom_l (@wf_sbE G)).
    rewrite sb_tid_init'; relsf; unionL; splits.
    unionR left -> left -> left -> right.
    by unfold same_tid; unfolder; ins; desf; eauto.
    transitivity D; [|unfold D; basic_solver 21].
    rewrite <- D_init; basic_solver.
- rewrite dom_rel_eqv_dom_rel.
  rewrite crE at 1; relsf; unionL; splits.
  2: by rewrite (dom_r (wf_rfiD WF)), (dom_l (wf_rfiD WF)); type_solver.
  basic_solver 12.
- ie_unfolder; unfolder; ins; desf.
  assert (x=z); subst; eauto 10.
  eapply WF; basic_solver.
- ie_unfolder; unfolder; ins; desc.
  assert (x=x0); subst.
  eapply WF; basic_solver.
  exfalso; auto.
Qed.

Lemma dom_rf_D : dom_rel (Grf ⨾ ⦗D⦘) ⊆₁ D.
Proof.
rewrite rfi_union_rfe at 1.
relsf; unionL; splits.
apply dom_rfi_D.
revert Grfe_E; generalize I_in_D; basic_solver.
Qed.

Lemma complete_D : D ∩₁ R  ⊆₁ codom_rel Grf.
Proof.
unfold D.
rewrite !set_inter_union_l.
unionL.
- apply COMP_C.
- rewrite (issuedW TCCOH); type_solver.
- apply COMP_NTID.
- rewrite crE; relsf; unionL; splits.
* apply COMP_PPO.
* rewrite (dom_l (wf_rfiD WF)); type_solver.
- ie_unfolder; basic_solver.
- ie_unfolder; basic_solver.
Qed.

Lemma dom_ppo_D : dom_rel (Gppo ⨾ ⦗D⦘) ⊆₁ D.
Proof.
cut (Gppo ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
by unfolder; ins; desf; eapply H; eauto.
unfold ppo.
arewrite_id ⦗R⦘.
arewrite_id ⦗W⦘.
rels.
rewrite (inclusion_t_rt).
apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
by eauto with hahn.
basic_solver.
intros k H; rewrite !seqA.
relsf; unionL.
- rewrite (dom_rel_helper dom_data_D); sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_ctrl_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_addr_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_rfi_D); sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_rmw_in_D). rewrite !seqA. sin_rewrite H; basic_solver.
- rewrite (dom_rel_helper dom_frmw_in_D); rewrite !seqA; sin_rewrite H; basic_solver.
Qed.

Lemma dom_ppo_CI : dom_rel (Gppo ⨾ ⦗C ∪₁ I⦘) ⊆₁ D.
Proof.
rewrite C_in_D, I_in_D; relsf.
apply dom_ppo_D.
Qed.


(******************************************************************************)
(**  new co relation  *)
(******************************************************************************)

Definition cert_co := new_co G I (E ∩₁ W ∩₁ Tid_ thread).


Lemma wf_cert_coE : cert_co ≡ ⦗E⦘ ⨾ cert_co ⨾ ⦗E⦘.
Proof.
apply wf_new_coE; [apply IT_new_co|apply (wf_coE WF)].
Qed.

Lemma wf_cert_coD : cert_co ≡ ⦗W⦘ ⨾ cert_co ⨾ ⦗W⦘.
Proof.
apply wf_new_coD; [apply IT_new_co|apply (wf_coD WF)].
Qed.


Lemma wf_cert_col : cert_co ⊆ Gsame_loc.
Proof.
apply wf_new_col; [apply IT_new_co|apply (wf_coD WF)].
Qed.

Lemma cert_co_trans : transitive cert_co.
Proof.
apply new_co_trans; try apply WF; apply IT_new_co.
Qed.

Lemma wf_cert_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => Gloc x = ol)) cert_co.
Proof.
intros.
apply wf_new_co_total.
apply IT_new_co.
all: apply WF.
Qed.

Lemma cert_co_irr : irreflexive cert_co.
Proof.
apply new_co_irr. 
  apply IT_new_co.
  all: apply WF.
Qed.

Lemma cert_co_I : cert_co ⨾ ⦗ I ⦘  ⊆ Gco ⨾ ⦗ I ⦘.
Proof.
apply new_co_I.
  apply IT_new_co.
  all: apply WF.
Qed.

Lemma I_co_in_cert_co : ⦗ I ⦘ ⨾ Gco ⊆ cert_co.
Proof.
apply I_co_in_new_co.
  apply IT_new_co.
  all: apply WF.
Qed.

Lemma cert_co_for_split: ⦗set_compl I⦘ ⨾ (immediate cert_co) ⊆ Gsb.
Proof.
unfold cert_co.
red; intros x y H.
assert (A: (E ∩₁ W ∩₁ Tid_ thread) y).
by apply (co_for_split IT_new_co (wf_coE WF) (wf_coD WF)); basic_solver.
unfolder in H; desf.
assert (B: (E ∩₁ W) x).
hahn_rewrite (wf_new_coE IT_new_co (wf_coE WF)) in H0.
hahn_rewrite (wf_new_coD IT_new_co (wf_coD WF)) in H0.
unfolder in H0; basic_solver.
apply IT_new_co in B; unfolder in B; desf.
unfolder in A; desf.
assert (D: (⦗ E ∩₁ W ∩₁ Tid_ (tid x) ⦘ ⨾ Gco) x y).
by eapply T_new_co; try edone; try apply WF; basic_solver.

eapply same_thread in A0; try edone.
-
desf.
exfalso.
unfolder in D; desf.
destruct A0; try subst.
eapply (co_irr WF); edone.
eapply COH.
hahn_rewrite <- (@sb_in_hb G).
hahn_rewrite <- (@co_in_eco G).
basic_solver.
- hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in D.
unfolder in D; basic_solver.
Qed.

Lemma cert_co_alt : cert_co  ⊆ Gco ∩ cert_co ⨾ ⦗ I ⦘ ∪ ⦗ Tid_ thread ⦘ ⨾ Gco ∩ cert_co ∪ 
  ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁ I ⦘.
Proof.
arewrite (I ∩₁ NTid_ thread ≡₁ I \₁ E ∩₁ W ∩₁ Tid_ thread).
{ revert IT_new_co; unfolder.
ins; desf; splits; ins; eauto; [tauto|].
desf; splits; eauto; intro; eapply H0; splits; eauto.
by apply (issuedE TCCOH).
by apply (issuedW TCCOH). }
arewrite (cert_co ⊆ cert_co ∩ cert_co) at 1.
unfold cert_co at 1.
rewrite new_co_in at 1.
basic_solver 40.
done.
all: apply WF.
Qed.

Lemma cert_co_alt' : cert_co  ⊆ Gco ∩ cert_co ∪ 
  ⦗ I ∩₁ NTid_ thread ⦘ ⨾ cert_co ⨾ ⦗ (E ∩₁ W ∩₁ Tid_ thread) \₁ I ⦘.
Proof.
rewrite cert_co_alt at 1.
basic_solver 12.
Qed.

(******************************************************************************)
(** Definition of the new rf edges   *)
(******************************************************************************)

(*Definition viewed l := Gurr l. *)
Definition new_rf := Gfurr ∩ Gsame_loc ⨾ ⦗(E \₁ D) ∩₁ R⦘ \ cert_co ⨾ Gfurr.
(* Definition new_rf_loc l := max_co' (viewed l) ⨾ ⦗(E \₁ D) ∩₁ Tid_ thread ∩₁ R_ l⦘. *)
(* Definition new_rf x y := exists l, new_rfl l x y.  *)

(* Definition new_rf := 
(((⦗W⦘ ⨾ Gsb \ (Gco ⨾ Gsb ∪ (Gco ⨾ ⦗I ∩₁ Tid_ thread⦘ ⨾ Gco ⨾ ⦗I⦘ ⨾ Gfurr)))
∪ ((⦗I⦘ ⨾ Gco^{-1} ⨾ ⦗I⦘ ⨾ Gsb) ∩ Gfurr \ (Gco ⨾ ⦗I⦘ ⨾ Gfurr))) ⨾
⦗(E \₁ D) ∩₁ Tid_ thread ∩₁ R⦘)
∩ Gsame_loc.
 *)

Lemma wf_new_rfE : new_rf ≡ ⦗E⦘ ⨾ new_rf ⨾ ⦗E \₁ D⦘.
Proof.
apply dom_helper_3.
unfold new_rf.
rewrite (wf_furrE WF WF_SC); basic_solver 21.
Qed.

Lemma wf_new_rfD : new_rf ≡ ⦗W⦘ ⨾ new_rf ⨾ ⦗R⦘.
Proof.
apply dom_helper_3.
unfold new_rf.
unfold furr, urr; basic_solver.
Qed.

Lemma wf_new_rfl : new_rf ⊆ Gsame_loc.
Proof.
unfold new_rf; basic_solver.
(* unfold new_rf, new_rf_loc, max_co', viewed, Events.same_loc.
red; ins; desc.
hahn_rewrite (@wf_urrD G) in H.
unfold seq, eqv_rel in H; desf.
unfolder in *; ins; desf; congruence.
 *)
Qed.

Lemma wf_new_rff : functional new_rf⁻¹.
Proof.
rewrite wf_new_rfD, wf_new_rfE.
red; ins.
assert (exists l, Gloc y = Some l).
by generalize (is_w_loc Glab); unfolder in *; basic_solver 12.
desc.

assert (Gloc z = Some l).
{ hahn_rewrite wf_new_rfl in H; hahn_rewrite wf_new_rfl in H0.
  unfold same_loc in *; unfolder in *; ins; desf; congruence. }
unfolder in *.
destruct (classic (y=z)) as [|X]; eauto; desf.
exfalso; eapply wf_cert_co_total in X; try basic_solver 22.
2: unfolder; splits; eauto; congruence.


unfold new_rf in *; desf; unfolder in *; basic_solver 40.
Qed.

Lemma new_rf_comp : forall b (IN: ((E \₁ D) ∩₁ R) b) , exists a, new_rf a b.
Proof.
ins; unfolder in *; desf.
assert (exists l, Gloc b = Some l); desc.
  by generalize (is_r_loc Glab); unfolder in *; basic_solver 12.
assert (E (InitEvent l)).
  by apply WF; eauto.
assert (Glab (InitEvent l) = Astore Xpln Opln l 0).
  by apply WF. 
assert (Gloc (InitEvent l) = Some l).
  by unfold loc; rewrite (wf_init_lab WF).
assert (W_ l (InitEvent l)).
  by unfolder; unfold is_w, loc; desf; eauto.
assert (Gsb (InitEvent l) b).
  by apply init_ninit_sb; eauto; eapply read_or_fence_is_not_init; eauto.
assert (Gurr l (InitEvent l) b).
  { exists (InitEvent l); splits.
    unfold eqv_rel; eauto.
    hahn_rewrite <- sb_in_hb.
    basic_solver 12. }

forward (eapply last_exists with (s:=cert_co ⨾ ⦗fun x=> Gfurr x b⦘) 
 (dom:= filterP (W_ l) G.(acts)) (a:=(InitEvent l))).
- eapply acyclic_mon.
  apply trans_irr_acyclic; [apply cert_co_irr| apply cert_co_trans].
  basic_solver.
- ins.
  assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) c).
  { apply rt_of_trans; try done.
    apply transitiveI; unfolder; ins; desf; splits; eauto.
    eapply cert_co_trans; eauto. }
  unfolder in A; desf.
  by apply in_filterP_iff; split; auto.
  apply in_filterP_iff.
  hahn_rewrite wf_cert_coE in A.
  hahn_rewrite wf_cert_coD in A.
  hahn_rewrite wf_cert_col in A.
   unfold same_loc in *; unfolder in *; desf; splits; eauto; congruence.
- ins; desf.
  assert (A: (cert_co ⨾ ⦗fun x : actid => Gfurr x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; try done.
    apply transitiveI; unfolder; ins; desf; splits; eauto.
    eapply cert_co_trans; eauto. }
  assert (Gloc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite wf_cert_col in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  * unfold furr, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence.
  * unfold max_elt in *.
    unfolder in *; ins; desf; intro; desf; basic_solver 11.
Qed.

Lemma new_rf_mod: (E \₁ D) ∩₁ is_r Glab ≡₁ codom_rel new_rf.
Proof.
split.
unfolder; ins; desf.
apply new_rf_comp; basic_solver.
unfold new_rf; basic_solver.
Qed.

Lemma new_rf_in_furr: new_rf ⊆ Gfurr.
Proof.
unfold new_rf; basic_solver.
Qed.

Lemma new_rf_hb: irreflexive (new_rf ⨾ Ghb ⨾ (sc ⨾ Ghb)^?).
Proof.
rewrite new_rf_in_furr.
apply furr_hb_sc_hb_irr; done.
Qed.

Lemma non_I_new_rf: ⦗E \₁ I⦘ ⨾ new_rf ⊆ Gsb.
Proof.
assert (new_rf_hb: irreflexive (new_rf ⨾ Ghb ⨾ (sc ⨾ Ghb)^?)).
by apply new_rf_hb. (* Coq bug ?! *)

rewrite (wf_new_rfD).
arewrite (⦗E \₁ I⦘ ⨾ ⦗W⦘ ⊆ ⦗E \₁ I⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗W⦘).
by revert IT_new_co; unfolder; firstorder.
rewrite (wf_new_rfE).
arewrite (E \₁ D ⊆₁ E ∩₁ Tid_ thread).
by unfold D; unfolder; ins; desf; tauto.
unfolder; ins; desf.
eapply (@same_thread G) in H3; desf.
destruct H3; [subst x; type_solver|].
2: by intro K; apply (init_w WF) in K; type_solver.
exfalso; generalize new_rf_hb.
generalize (@sb_in_hb G); basic_solver 12.
Qed.

Lemma new_rfe_Acq : (new_rf \ Gsb) ⨾ ⦗R∩₁Acq⦘ ⊆ ∅₂.
Proof.
rewrite wf_new_rfE.
arewrite (⦗E⦘ ⊆ ⦗E \₁ I⦘ ∪ ⦗E ∩₁ I⦘).
unfolder; ins; desf; tauto.
relsf.
rewrite minus_union_l.
relsf; unionL.
sin_rewrite non_I_new_rf.
basic_solver.
rewrite wf_new_rfD.
arewrite (new_rf ⊆ new_rf ∩ Gsame_loc).
generalize (wf_new_rfl); basic_solver.

unfolder; ins; desf.

assert (Lx:exists l, Gloc x = Some l); desc.
by apply is_w_loc.

assert (Ly:Gloc y = Some l).
unfold same_loc in *; congruence.

forward (apply COMP_ACQ).
by basic_solver.

ins; desc.

apply rfi_union_rfe in H10; unfolder in H10; desf; cycle 1.
by generalize R_Acq_codom_rfe; basic_solver 12.

ie_unfolder; unfolder in H10; desf.

hahn_rewrite (wf_rfD WF) in H10.
hahn_rewrite (wf_rfE WF) in H10.

unfolder in H10; desf.

assert (Lz:Gloc z = Some l).
by apply (wf_rfl WF) in H14; unfold same_loc in *; congruence.

forward (apply ((wf_co_total WF) (Some l) z)).
basic_solver.
instantiate (1 := x).
basic_solver.

intro; desf.

intro; desf.

-
eapply eco_furr_irr; try edone.
eexists; splits; [|eby apply new_rf_in_furr].
unfold eco, fr.
basic_solver 12.
- eapply H3.
exists z; split; [| apply furr_alt; basic_solver 12].
apply I_co_in_cert_co; basic_solver.
Qed.

(******************************************************************************)
(** The new label function   *)
(******************************************************************************)

Variable lab' : actid -> label.
Hypothesis SAME : same_lab_u2v lab' Glab.
Hypothesis NEW_VAL : forall r w (RF: new_rf w r), val lab' w = val lab' r.
Hypothesis OLD_VAL : forall a (NIN: ~ (E \₁ D) a), val lab' a = Gval a.

Lemma cert_R : is_r lab' ≡₁ R.
Proof. ins; erewrite same_lab_u2v_is_r; eauto. Qed.
Lemma cert_W : is_w lab' ≡₁ W.
Proof. ins; erewrite same_lab_u2v_is_w; eauto. Qed.
Lemma cert_F : is_f lab' ≡₁ F.
Proof. ins; erewrite same_lab_u2v_is_f; eauto. Qed.
Lemma cert_Rel : is_rel lab' ≡₁ Rel.
Proof. ins; erewrite same_lab_u2v_is_rel; eauto. Qed.
Lemma cert_Acq : is_acq lab' ≡₁ Acq.
Proof. ins; erewrite same_lab_u2v_is_acq; eauto. Qed.
Lemma cert_AcqRel : is_ra lab' ≡₁ Acq/Rel.
Proof. ins; erewrite same_lab_u2v_is_ra; eauto. Qed.
Lemma cert_Sc : is_sc lab' ≡₁ Sc.
Proof. ins; erewrite same_lab_u2v_is_sc; eauto. Qed.
Lemma cert_R_ex : R_ex lab' ≡₁ R_ex Glab.
Proof. ins; erewrite same_lab_u2v_R_ex; eauto. Qed.
Lemma cert_xacq : is_xacq lab' ≡₁ is_xacq Glab.
Proof. ins; erewrite same_lab_u2v_is_xacq; eauto. Qed.
Lemma cert_loc : loc lab' = Gloc.
Proof. ins; erewrite same_lab_u2v_loc; eauto. Qed.
Lemma cert_W_ l : (is_w lab') ∩₁ (fun x => loc lab' x = Some l) ≡₁ W_ l.
Proof. ins; erewrite same_lab_u2v_is_w, same_lab_u2v_loc; eauto. Qed.
Lemma cert_same_loc : same_loc lab' ≡ Gsame_loc.
Proof. ins; erewrite same_lab_u2v_same_loc; eauto. Qed.

(******************************************************************************)
(** Construction of the certification graph   *)
(******************************************************************************)

Definition certG :=
    {| acts := G.(acts);
       lab := lab' ;
       rmw := Grmw ;
       data := Gdata ;
       addr := Gaddr ;
       ctrl := Gctrl ;
       rmw_dep := Grmw_dep ;
       rf := Grf ⨾ ⦗D⦘ ∪ new_rf ;
       co := cert_co ;
    |}.

(* Notation "'CE'" := certG.(acts_set). *)
(* Notation "'Cacts'" := certG.(acts). *)
(* Notation "'Clab'" := certG.(lab). *)
(* Notation "'Csb'" := certG.(sb). *)
Notation "'Crf'" := certG.(rf).
Notation "'Cco'" := certG.(co).
(* Notation "'Crmw'" := certG.(rmw). *)
(* Notation "'Cdata'" := certG.(data). *)
(* Notation "'Caddr'" := certG.(addr). *)
(* Notation "'Cctrl'" := certG.(ctrl). *)
Notation "'Cdeps'" := certG.(deps).
(* Notation "'Crmw_dep'" := certG.(rmw_dep). *)

Notation "'Cfre'" := certG.(fre).
(* Notation "'Crfe'" := certG.(rfe). *)
Notation "'Ccoe'" := certG.(coe).
Notation "'Crfi'" := certG.(rfi).
Notation "'Cfri'" := certG.(fri).
Notation "'Ccoi'" := certG.(coi).
Notation "'Cfr'" := certG.(fr).
Notation "'Ceco'" := certG.(eco).
Notation "'Cdetour'" := certG.(detour).
Notation "'Csw'" := certG.(sw).
(* Notation "'Crelease'" := certG.(release). *)
Notation "'Crs'" := certG.(rs).
Notation "'Chb'" := certG.(hb).
Notation "'Cppo'" := certG.(ppo).
(* Notation "'Cbob'" := certG.(bob). *)
(* Notation "'Cfwbob'" := certG.(fwbob). *)
Notation "'Car'" := (certG.(ar) sc).
Notation "'Car_int'" := (certG.(ar_int)).
Notation "'Curr'" := (certG.(urr) sc).
Notation "'Cmsg_rel'" := (certG.(msg_rel) sc).

(******************************************************************************)
(** properties of the ceritifcation execution   *)
(******************************************************************************)

Lemma cert_lab_init : forall a (IN: is_init a), lab' a = Glab a.
Proof.
ins; cut (val lab' a = Gval a).
- assert (same_label_u2v (lab' a) (Glab a)) as SS by (by apply SAME).
  unfold same_label_u2v in *. unfold val; desf; desf.
  all: intros HH; inv HH.
- apply OLD_VAL.
  unfolder; desf.
  generalize (D_init); unfolder; ins; desf; intro; desf; eauto 20.
Qed.

Lemma cert_E : certG.(acts_set) ≡₁ E.
Proof. unfold certG; vauto. Qed.
Lemma cert_sb : certG.(sb) ≡ Gsb.
Proof. by unfold Execution.sb; rewrite cert_E. Qed.
Lemma cert_W_ex : certG.(W_ex) ≡₁ GW_ex.
Proof. unfold Execution.W_ex; ins. Qed.


Lemma cert_fwbob : certG.(fwbob) ≡ Gfwbob.
Proof. 
unfold imm_bob.fwbob.
rewrite cert_W, cert_F, cert_Rel, cert_AcqRel.
by rewrite cert_sb, cert_same_loc.
Qed.

Lemma cert_bob : certG.(bob) ≡ Gbob.
Proof. 
unfold imm_bob.bob.
by rewrite cert_R, cert_Acq, cert_fwbob, cert_sb.
Qed.

Lemma cert_W_ex_acq : certG.(W_ex) ∩₁ is_xacq lab' ≡₁ GW_ex ∩₁ xacq.
Proof. 
unfold Execution.W_ex.
by rewrite cert_xacq; ins.
Qed.

Lemma cert_rfe : certG.(rfe) ≡ ⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘ ∪ ⦗I⦘ ⨾ (new_rf \ Gsb).
Proof.
unfold Execution.rfe; ins.
rewrite cert_sb.
split; [|basic_solver 12].
rewrite minus_union_l; unionL.
generalize Grfe_E; ie_unfolder; basic_solver 21.
rewrite (dom_l wf_new_rfE) at 1.
  arewrite (⦗E⦘ ⊆ ⦗E ∩₁ I⦘ ∪ ⦗E \₁ I⦘) at 1.
  by unfolder; ins; desf; tauto.
relsf; rewrite minus_union_l; unionL.
basic_solver 21.
rewrite (non_I_new_rf).
basic_solver 21.
Qed.

Lemma cert_rfe_D : certG.(rfe) ⨾ ⦗D⦘ ⊆ ⦗I⦘ ⨾ Grfe.
Proof. 
rewrite cert_rfe.
rewrite (dom_r wf_new_rfE).
basic_solver 12.
Qed.

Lemma cert_rf_D : Crf ⨾ ⦗D⦘ ≡ Grf ⨾ ⦗D⦘.
Proof. ins; split; [rewrite wf_new_rfE|]; basic_solver 20. Qed.

Lemma cert_rfi_D : Crfi ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ Grfi ⨾ ⦗D⦘.
Proof. 
ie_unfolder; rewrite cert_sb.
rewrite <- seq_eqv_inter_lr.
rewrite cert_rf_D.
rewrite (dom_rel_helper dom_rf_D).
basic_solver.
Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma cert_release : certG.(release) ≡ Grelease.
Proof.
unfold imm_s_hb.release, imm_s_hb.rs; ins.
rewrite cert_F, cert_Rel, cert_W, cert_same_loc, cert_sb.
rewrite (dom_rel_helper dom_rmw_in_D) at 1.
seq_rewrite cert_rf_D.
rewrite (dom_rel_helper dom_rmw_in_D) at 2.
by rewrite !seqA.
Qed.

Lemma sw_helper :
  Grelease ⨾ ⦗E ∩₁ I⦘ ⨾ new_rf ⨾ ⦗Acq⦘ ⊆ 
  Gsb ∪ (Grelease ⨾ Grf ⨾ ⦗Acq⦘ ∪ Grelease ⨾ Grf ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
Proof.
unfold new_rf.
unfolder; ins; desf.
assert (A: exists w : actid, Grf w y); desc.
  by eapply COMP_ACQ; basic_solver.
destruct (classic (w=z)); subst; [eauto 20|].
exfalso.
unfold furr in *; desf; eauto.
assert (Gloc z = Some l).
  by hahn_rewrite (@wf_urrD G) in H1; unfolder in H1; desf.
eapply (transp_rf_co_urr_irr WF WF_SC CSC COH).
assert (W w).
  by hahn_rewrite (wf_rfD WF) in A; unfolder in A; desf.
assert (Loc_ l w).
  by hahn_rewrite (wf_rfl WF) in A; unfold same_loc in *; unfolder in A; desf; congruence.
exists w; splits.
basic_solver.
exists z; split; eauto.
exploit (new_co_I IT_new_co); try apply WF; [| basic_solver].
unfolder; splits; eauto.
eapply tot_ex.
+ eapply (wf_new_co_total IT_new_co); try apply WF; try done.
+ by unfolder; splits; eauto; apply (issuedW TCCOH).
+ assert (E w).
  by hahn_rewrite (wf_rfE WF) in A; unfolder in A; desf.
  basic_solver 10.
+ intro.
  eapply H3. exists w. splits; eauto.
  exists l; unfold urr.
  apply (wf_urrE WF WF_SC) in H1.
  basic_solver 12.
+ intro; subst; eauto.
Qed.

Lemma cert_sb_sw : Gsb ∪ Csw ≡ Gsb ∪ Gsw.
Proof.
unfold imm_s_hb.sw; ins.
rewrite cert_F, cert_Acq, cert_release, cert_sb.
rewrite !crE; relsf; rewrite !seqA.
relsf; split; unionL.
- basic_solver 12.
- basic_solver 12.
- arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
  by rewrite (dom_r (@wf_sbE G)); generalize dom_sb_F_Acq_in_D; basic_solver 12.
  basic_solver 12.
- rewrite (dom_l wf_new_rfE), !seqA.
  arewrite (⦗E⦘ ⊆ ⦗E ∩₁ I⦘ ∪ ⦗E \₁ I⦘) at 1.
  by unfolder; ins; desf; tauto.
  relsf; unionL.
  * apply sw_helper.
  * arewrite (⦗E \₁ I⦘ ⊆ ⦗E \₁ I⦘ ⨾ ⦗E \₁ I⦘).
    basic_solver.
    sin_rewrite non_I_new_rf.
    arewrite (Grelease ⨾ ⦗E \₁ I⦘ ⊆ Gsb^?).
    { rewrite release_int at 1; relsf; unionL.
      by revert W_ex_E; unfolder; ins; desf; exfalso; eauto.
      all: basic_solver 12. }
    generalize (@sb_trans G).
    basic_solver.
- arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
  by rewrite (dom_r (@wf_sbE G)); generalize dom_sb_F_Acq_in_D; basic_solver 12.
  rewrite (dom_r wf_new_rfE); basic_solver.
- basic_solver 12.
- rewrite rfi_union_rfe; relsf; unionL.
  2: by rewrite <- R_Acq_codom_rfe at 2; rewrite (dom_r (wf_rfeD WF)) at 1; basic_solver 21.
  arewrite (Grelease ⊆ Gsb^? ∪ Grelease ⨾ ⦗GW_ex⦘) at 1.
  { unfold imm_s_hb.release, imm_s_hb.rs.
    rewrite rtE at 1; relsf; unionL.
    generalize (@sb_trans G); basic_solver 12.
    rewrite rmw_W_ex at 1.
    rewrite <- !seqA, inclusion_ct_seq_eqv_r, !seqA.
    basic_solver 21. }
  relsf; unionL.
  by arewrite (Grfi ⊆ Gsb); generalize (@sb_trans G); basic_solver 12.
  rewrite <- R_Acq_codom_W_ex_rfi at 1; rewrite (dom_r (wf_rfiD WF)) at 1; basic_solver 21.
- arewrite (Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ ⦗D⦘ ⨾ Gsb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
  by rewrite (dom_r (@wf_sbE G)); generalize dom_sb_F_Acq_in_D; basic_solver 12.
  basic_solver 21.
Qed.

Lemma cert_hb : Chb ≡ Ghb.
Proof.
by unfold imm_s_hb.hb; rewrite cert_sb_sw.
Qed.


Lemma cert_msg_rel l : Cmsg_rel l ⨾ ⦗I⦘ ≡ Gmsg_rel l ⨾ ⦗I⦘.
Proof.
unfold CombRelations.msg_rel, urr.
rewrite cert_W_, cert_F, cert_Sc, cert_release, cert_hb, !seqA.
arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘).
split; [|basic_solver 21].
by rewrite (dom_rel_helper (urr_helper)) at 1.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
rewrite !crE; relsf.
arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 2.
by basic_solver.
arewrite (⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗C⦘) at 5.
by basic_solver.
split; unionL; try basic_solver.
rewrite C_in_D at 1. 
seq_rewrite cert_rf_D; basic_solver.
rewrite C_in_D at 1. 
seq_rewrite <- cert_rf_D; basic_solver.

done.
Qed.



Lemma cert_t_cur_thread l : t_cur certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_cur G sc thread l (covered T).
Proof.
unfold t_cur, c_cur, urr.
rewrite cert_W_, cert_F, cert_Sc, cert_hb, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.


arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.

remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.


Lemma cert_t_rel_thread l l' : t_rel certG sc thread l l'
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_rel G sc thread l l' (covered T).
Proof.
unfold t_rel, c_rel, urr.
rewrite !cert_W_, cert_F, cert_Sc, cert_hb, cert_Rel, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.

arewrite (⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘).
basic_solver 12.


arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.


Lemma cert_t_acq_thread l : t_acq certG sc thread l
  (covered T ∪₁ E ∩₁ NTid_ thread) ≡₁ t_acq G sc thread l (covered T).
Proof.
unfold t_acq, c_acq, urr.
rewrite !cert_W_, cert_F, cert_Sc, cert_hb, cert_release, !seqA.

arewrite  (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ≡  ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
unfolder; splits; ins; desf; splits; eauto.
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).
by apply (init_covered TCCOH); split; eauto; apply (sub_E_in SUB).

arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘) at 2.
basic_solver 12.

arewrite ((Grelease ⨾ Crf)^? ⨾ ⦗C⦘ ≡ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf.
rewrite !seqA.
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾  ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


remember (dom_rel
  (⦗W_ l⦘
   ⨾ Crf^?
     ⨾ ⦗C⦘
       ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
         ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ⨾ ⦗C⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘)) as X.

arewrite ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^?
          ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘ ≡ ⦗C⦘ ⨾ (Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘).
split; [generalize (urr_helper_C)|]; basic_solver 21.


subst.

arewrite (Crf^? ⨾ ⦗C⦘ ≡ Grf^? ⨾ ⦗C⦘).
{ arewrite (⦗C⦘ ≡ ⦗D⦘ ⨾ ⦗C⦘).
split.
generalize C_in_D; basic_solver.
basic_solver. 
rewrite !crE; relsf. 
seq_rewrite cert_rf_D.
rewrite !seqA.
done.
}
done.
Qed.




(******************************************************************************)
(** **   *)
(******************************************************************************)



Lemma WF_cert : Wf certG.
Proof.
constructor; ins.
all: rewrite ?cert_sb, ?cert_R, ?cert_W, ?cert_same_loc, ?cert_E, ?cert_rf, ?cert_co, ?cert_R_ex.
all: try by apply WF.
- apply dom_helper_3; rewrite (wf_rfE WF), wf_new_rfE; basic_solver.
- apply dom_helper_3; rewrite (wf_rfD WF), wf_new_rfD; basic_solver.
- rewrite (wf_rfl WF), wf_new_rfl; basic_solver.
- ins; unfolder; ins; desf; eauto.
  unfold funeq; ins.
  hahn_rewrite (wf_rfE WF) in H; unfolder in H; desc.
  rewrite !OLD_VAL.
  by apply wf_rfv; eauto.
  by intro B; eapply B; eauto.
  by intro A; eapply A; generalize dom_rf_D; basic_solver.
- rewrite transp_union; apply functional_union.
  by unfolder; ins; eapply (wf_rff WF); basic_solver.
  by apply wf_new_rff.
  by unfolder; ins; desf; apply wf_new_rfE in H0; unfolder in H0; basic_solver.
- apply wf_new_coE; [apply IT_new_co|apply (wf_coE WF)].
- apply wf_new_coD; [apply IT_new_co|apply (wf_coD WF)].
- apply wf_new_col; [apply IT_new_co|apply (wf_coD WF)].
- apply new_co_trans.
  apply IT_new_co.
  all: apply WF.
- intros. erewrite same_lab_u2v_loc; try edone.
  apply wf_new_co_total. 
  apply IT_new_co.
  all: apply WF.
- apply new_co_irr. 
  apply IT_new_co.
  all: apply WF.
- ins; desf; apply cert_E.
  by apply (wf_init WF); exists b; splits; [apply cert_E| rewrite <- cert_loc].
- ins; rewrite cert_lab_init.
  apply (wf_init_lab WF).
  by unfold is_init.
Qed.

Lemma WF_SC_cert : wf_sc certG sc.
Proof.
constructor.
- rewrite cert_E; apply WF_SC.
- rewrite cert_F, cert_Sc; apply WF_SC.
- apply WF_SC.
- rewrite cert_E, cert_F, cert_Sc; apply WF_SC.
- apply WF_SC.
Qed.



(******************************************************************************)
(** **   *)
(******************************************************************************)


Lemma cert_complete : complete certG.
Proof.
red; unfolder; ins; desf.
destruct (classic (D x)).
- forward (apply (complete_D)).
  unfolder; ins; desf; eauto 20.
  apply cert_R in H0.
  forward (apply H2); splits; try edone; desf; eexists; eauto.
- forward (apply new_rf_comp).
  by unfolder; ins; desf; splits; eauto; apply cert_R; ins.
  ins; desf; basic_solver 12.
Qed.

Lemma cert_coherece_detour_helper :
  irreflexive (Ghb ⨾ (sc ⨾ Ghb)^? ⨾ ⦗D⦘ ⨾ Grf⁻¹⨾ ⦗I ∩₁ NTid_ thread⦘ ⨾ cert_co ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘).
Proof.
assert (A: dom_rel (Gdetour ⨾ ⦗D⦘) ⊆₁ I).
by apply dom_detour_D. (* Ori: weird Coq behavior? *)

rewrite wf_cert_col.
unfold same_loc; unfolder; ins; desc; splits; eauto.
assert (CO: Gco x z1).
{ eapply tot_ex.
  apply WF.
  unfolder; splits; eauto.
  hahn_rewrite (wf_rfE WF) in H2; unfolder in H2; desc; done.
  hahn_rewrite (wf_rfD WF) in H2; unfolder in H2; desc; done.
  unfolder; splits; eauto.
  intro; generalize COH CSC; unfold coherence, coh_sc, eco, fr.
  desf; try subst z0; basic_solver 21.
  intro; subst x; auto. }
assert (SB: Gsb x z0).
  by apply hb_sc_hb_de; generalize (w_covered_issued TCCOH); basic_solver 21.
assert (RFE: Grfe z1 z0).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in SB.
  apply sb_tid_init in K.
  destruct SB, K.
  congruence.
  hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in CO.
  unfolder in CO; desc; done.
  generalize (init_issued WF TCCOH); basic_solver.
  generalize (init_issued WF TCCOH); basic_solver. }
assert (COE: Gcoe x z1).
{ ie_unfolder; unfolder; ins; desc; splits; eauto.
  intro K.
  apply sb_tid_init in K.
  destruct K.
  congruence.
  generalize (init_issued WF TCCOH); basic_solver. }
assert (DETOURE: Gdetour x z0).
  by unfold detour; basic_solver.
apply H6, A; unfolder; ins; desf; splits; eauto.
Qed.

Lemma coh_helper : irreflexive (Chb ⨾ (sc ⨾ Chb)^? ⨾ Ceco^?).
Proof.
apply coh_helper_alt; rewrite cert_hb; relsf; unionL.
- case_refl sc; [by apply hb_irr|].
  rewrite (wf_scD WF_SC); rotate 1.
  sin_rewrite (f_sc_hb_f_sc_in_ar WF).
  unfolder; ins; desc.
  eapply ACYC_EXT.
  eapply t_trans; [edone| apply t_step].
  by apply sc_in_ar.
- rewrite cert_rfe; relsf; unionL.
  * revert COH CSC; unfold coherence, coh_sc, eco; ie_unfolder; basic_solver 21.
  * generalize new_rf_hb; basic_solver 12.
- rewrite cert_co_alt'; relsf; unionL.
  * revert COH CSC; unfold coherence, coh_sc, eco; basic_solver 21.
  * revert W_hb_sc_hb_to_I_NTid; basic_solver 21.
- rewrite cert_rfe; relsf; unionL.
  * rewrite (dom_rel_helper Grfe_E).
    unfold certG; ins; rewrite !seqA.
    sin_rewrite cert_co_I.
    revert COH CSC; unfold coherence, coh_sc, eco; ie_unfolder; basic_solver 21.
  * rewrite cert_co_alt'; relsf; unionL.
    + rewrite new_rf_in_furr.
      rotate 1.
      arewrite (Gfurr \ Gsb ⊆ Gfurr).
      arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      by generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT); basic_solver 21.
      generalize (eco_furr_irr WF WF_SC CSC COH).
      unfold eco; basic_solver 21.
    + generalize non_I_new_rf; basic_solver 16.
- unfold fr; rewrite cert_co_alt'; unfold certG; ins.
  rewrite transp_union, transp_seq; relsf; unionL.
  * revert COH CSC; unfold coherence, coh_sc, eco, fr; ie_unfolder; basic_solver 21.
  * rotate 1.
    arewrite (Gco ∩ cert_co ⊆ cert_co).
    rewrite (dom_r (wf_cert_coD)), !seqA.
    arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    rewrite (furr_alt WF_SC); basic_solver 21.
    unfold new_rf; basic_solver 21.
  * rewrite !seqA; eapply cert_coherece_detour_helper.
  * rotate 1.
    arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⊆ ⦗W⦘) by basic_solver.
    arewrite (⦗W⦘ ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
    rewrite (furr_alt WF_SC); basic_solver 21.
    unfold new_rf; basic_solver 21.
- rewrite cert_rfe; relsf; unionL.
  * unfold fr; unfold certG; ins.
    rewrite transp_union, transp_seq; relsf; unionL.
    + rewrite (dom_rel_helper Grfe_E), !seqA.
      sin_rewrite cert_co_I.
      revert COH CSC; unfold coherence, coh_sc, eco, fr; ie_unfolder; basic_solver 21.
    + arewrite (Grfe ⨾ ⦗D⦘ ⊆ Grf) by ie_unfolder; basic_solver.
      rotate 1.
      arewrite (Grf ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
      rewrite (furr_alt WF_SC); rewrite (dom_l (wf_rfD WF)); basic_solver 21.
      unfold new_rf; basic_solver 21.
  * unfold fr; unfold certG; ins.
    rewrite transp_union, transp_seq; relsf; unionL.
    + rewrite cert_co_alt'; relsf; unionL.
      -- rewrite new_rf_in_furr.
         rotate 1.
         arewrite (Gfurr \ Gsb ⊆ Gfurr).
         arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
         by generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT); basic_solver 21.
         generalize (eco_furr_irr WF WF_SC CSC COH).
         unfold eco, fr; basic_solver 21.
      -- generalize non_I_new_rf; basic_solver 16.
    + rewrite cert_co_alt'; relsf; unionL.
      -- rewrite new_rf_in_furr at 2.
         rotate 1.
         arewrite (Gfurr \ Gsb ⊆ Gfurr).
         arewrite (Gfurr ⨾ Ghb ⨾ (sc ⨾ Ghb)^? ⊆ Gfurr).
         by generalize (furr_hb_sc_hb WF WF_SC ACYC_EXT); basic_solver 21.
         unfold new_rf; basic_solver 21.
      -- generalize non_I_new_rf; basic_solver 16.
Qed.

Lemma cert_coherence : coherence certG.
Proof.
red; generalize coh_helper; basic_solver 12.
Qed.

Lemma cert_coh_sc : coh_sc certG  sc.
Proof.
red; case_refl _.
- rewrite cert_hb.
  rewrite (wf_scD WF_SC); rotate 2.
  sin_rewrite (f_sc_hb_f_sc_in_ar WF).
  unfolder; ins; desc.
  eapply ACYC_EXT.
  eapply t_trans; [edone| apply t_step].
  by apply sc_in_ar.
- generalize coh_helper; basic_solver 21.
Qed.


Lemma cert_rmw_atomicity : rmw_atomicity certG.
Proof.
clear OLD_VAL NEW_VAL SAME W_hb_sc_hb_to_I_NTid ACYC_EXT CSC COMP_ACQ.
generalize (atomicity_alt WF (coherence_sc_per_loc COH) AT).
intro AT'; clear AT.

red; ins; cut (irreflexive (Cfr ⨾ (cert_co \ Gsb) ⨾ Grmw^{-1})).
by basic_solver 12.
rewrite (rmw_W_ex), (dom_r (wf_rmwE WF)), !transp_seq, !transp_eqv_rel.
arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗GW_ex ∩₁ E⦘) by basic_solver.
rewrite W_ex_E.
unfold cert_co.
rotate 1.
unfold fr; ins; rewrite transp_union.
rewrite (dom_rel_helper (dom_rmw_in_D)).
rewrite (dom_r (wf_new_rfE)).
rewrite !transp_seq, !transp_eqv_rel, !seqA.
relsf; unionL; [| basic_solver].
unfold cert_co.

arewrite ((new_co G I (E ∩₁ W ∩₁ Tid_ thread) \ Gsb) ⨾ ⦗I⦘ ⊆ (new_co G I (E ∩₁ W ∩₁ Tid_ thread) ∩ Gco \ Gsb) ⨾ ⦗I⦘).
{ cut (new_co G I (E ∩₁ W ∩₁ Tid_ thread) ⨾ ⦗I⦘ ⊆ Gco).
  basic_solver 21.
  rewrite (new_co_I IT_new_co); try apply WF.
  basic_solver. }

rewrite (new_co_in IT_new_co) at 1; try apply WF.
relsf; unionL.
1,2: generalize (co_trans WF); revert AT'; unfold fr; basic_solver 12.

arewrite (⦗I⦘ ⊆ ⦗I \₁ E ∩₁ W ∩₁ Tid_ thread⦘ +++ ⦗I ∩₁ E ∩₁ W ∩₁ Tid_ thread⦘).
unfolder; ins; desf; tauto.

relsf; unionL; cycle 1.

* unfolder; ins; desf.
  eapply (@same_thread G) in H7; desf.
  + destruct H7; desf; try subst z2; eauto.
    by eapply COH; eexists; splits; [apply sb_in_hb | right; apply co_in_eco]; edone.
  + intro.
    hahn_rewrite (no_co_to_init WF (coherence_sc_per_loc COH)) in H11.
    unfolder in H11; desf.
* arewrite (new_co G I (E ∩₁ W ∩₁ Tid_ thread) ∩ Gco \ Gsb ⊆ new_co G I (E ∩₁ W ∩₁ Tid_ thread)).
  arewrite (⦗I \₁ E ∩₁ W ∩₁ Tid_ thread⦘ ⊆ ⦗I \₁ E ∩₁ W ∩₁ Tid_ thread⦘ ⨾ ⦗I \₁ E ∩₁ W ∩₁ Tid_ thread⦘) at 1.
  by basic_solver.
  arewrite (⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⊆ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘ ⨾ ⦗E ∩₁ W ∩₁ Tid_ thread \₁ I⦘).
  by basic_solver.
  sin_rewrite (T_I_new_co_I_T); [|apply WF].
  unfolder; ins; desc; subst z0 z3 z5.
  assert (E z1).
  by hahn_rewrite (dom_l (wf_rfE WF)) in H1; unfolder in H1; desf.
  assert (W z1).
  by hahn_rewrite (dom_l (wf_rfD WF)) in H1; unfolder in H1; desf.
  assert (Gsame_loc z1 z4).
  { eapply same_loc_trans.
    eapply same_loc_trans.
    eby apply (wf_rfl WF).
    eby apply (wf_rmwl WF).
    eby apply same_loc_sym; apply (wf_col WF). }
  assert (K: Gco z4 z1 \/ Gco z1 z4).
  { eapply WF.
    unfolder; splits; eauto.
    unfolder; splits; eauto.
    intro; subst z4; eauto 10. }
  destruct K.
  2: revert AT'; unfold fr; basic_solver 12.
  eapply (new_co_irr IT_new_co); try apply WF.
  eapply (new_co_trans IT_new_co); try apply WF.
  edone.
  apply new_co_helper; try apply WF.
  basic_solver 21.
Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)


Lemma cert_ppo_D : Cppo ⨾ ⦗ D ⦘ ⊆ Gppo.
Proof.
  remember (Gdata ∪ Gctrl ∪ Gaddr ⨾ Gsb^? ∪ Grmw ∪ Grmw_dep ;; Gsb^?) as X.
  unfold ppo; ins.
  arewrite (Cppo ⊆ ⦗R⦘ ⨾ (X ∪ Crfi)⁺ ⨾ ⦗W⦘).
  { unfold ppo; rewrite cert_R, cert_W, cert_sb.
    rewrite HeqX; hahn_frame; apply inclusion_t_t; basic_solver 12. }
  arewrite (Gppo ≡ ⦗R⦘ ⨾ (X ∪ Grfi)⁺ ⨾ ⦗W⦘).
  { unfold ppo. rewrite HeqX. split; hahn_frame; apply inclusion_t_t; basic_solver 12. }
  arewrite (⦗W⦘ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗W⦘) by basic_solver.
  hahn_frame.
  rewrite path_union; relsf; unionL.
  generalize inclusion_t_t; basic_solver.
  rewrite !seqA.

  assert (X_D_helper: dom_rel (X ⨾ ⦗D⦘) ⊆₁ D).
  { rewrite HeqX.
    relsf; unionL; splits.
    { apply dom_data_D. }
    { rewrite (dom_rel_helper dom_ctrl_in_D). basic_solver. }
    { rewrite (dom_rel_helper dom_addr_in_D). basic_solver. }
    { rewrite (dom_rel_helper dom_rmw_in_D). basic_solver. }
    rewrite (dom_rel_helper dom_frmw_in_D). basic_solver. }

  assert (X_D: dom_rel (X＊ ⨾ ⦗D⦘) ⊆₁ D).
  { cut (X＊ ⨾ ⦗D⦘ ⊆ ⦗D⦘ ⨾ (fun _ _ => True)).
    { unfolder; ins; desf; eapply H; eauto. }
    apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
    { eauto with hahn. }
    { basic_solver. }
    intros h H; rewrite !seqA.
    rewrite (dom_rel_helper X_D_helper); sin_rewrite H.
    basic_solver. }

  rewrite (dom_rel_helper X_D).
  enough ((X＊ ⨾ Crfi)⁺ ⨾ ⦗D⦘ ⊆ (X ∪ Grfi)⁺).
  { sin_rewrite H; arewrite (X ⊆ (X ∪ Grfi)⁺) at 2; relsf; basic_solver. }

  apply ct_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
  { eauto with hahn. }
  { rewrite !seqA, ct_end.
    arewrite (X ⊆ X ∪ Grfi) at 1.
    rewrite cert_rfi_D.
    basic_solver 12. }

  intros k H.
  rewrite !seqA.
  rewrite cert_rfi_D.

  seq_rewrite (dom_rel_helper X_D).
  rewrite !seqA.
  sin_rewrite H.
  arewrite_id ⦗D⦘.
  arewrite (X ⊆ X ∪ Grfi) at 2.
  arewrite (Grfi ⊆ (X ∪ Grfi)＊) at 3.
  relsf.
Qed.

Lemma cert_ppo_CI : Cppo ⨾ ⦗ C ∪₁ I ⦘ ⊆ Gppo.
Proof.
rewrite C_in_D, I_in_D; relsf.
apply cert_ppo_D.
Qed.


Lemma cert_detour_D : Cdetour ⨾ ⦗ D ⦘ ⊆ ⦗ I ⦘ ⨾ Gdetour.
Proof.
enough (Cdetour ⨾ ⦗ D ⦘ ⊆ Gdetour).
- arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
sin_rewrite H.
rewrite (dom_rel_helper dom_detour_D).
basic_solver.
- 
unfold detour, Execution.coe.
rewrite cert_sb.
rewrite <- seq_eqv_inter_lr, !seqA.
rewrite cert_rfe_D.
seq_rewrite <- seq_eqv_minus_lr.
rewrite cert_co_I.

basic_solver 21.
Qed.



Lemma cert_detour_R_Acq_sb_D : Cdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb ⨾ ⦗ D ⦘ ⊆ 
  ⦗ I ⦘ ⨾ Gdetour ⨾ ⦗R∩₁Acq⦘ ⨾ Gsb.
Proof.
rewrite (detour_to_codom_rfe WF_cert), !seqA.
rewrite cert_rfe.
rewrite codom_union, id_union; relsf; unionL.
arewrite (⦗codom_rel (⦗I⦘ ⨾ Grfe ⨾ ⦗D⦘)⦘ ⊆ ⦗D⦘) by basic_solver.
sin_rewrite cert_detour_D; basic_solver 40.
unfolder; ins; desf; exfalso.
generalize new_rfe_Acq; basic_solver 21.
Qed.


Lemma W_rel_sb_loc_W_CI :
 (⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘) ⨾ ⦗C ∪₁ I⦘ ⊆
⦗C ∪₁ I⦘ ⨾ (⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘).
Proof.
(* case_refl _; [basic_solver|]. *)
rewrite !seqA.
arewrite (⦗W⦘ ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
generalize (w_covered_issued TCCOH); basic_solver.
generalize (dom_sb_loc_issued TCCOH); basic_solver 12.
Qed.

Lemma sb_W_rel_CI :
 (Gsb ⨾ ⦗W ∩₁ Rel⦘) ⨾ ⦗C ∪₁ I⦘ ⊆
⦗C ∪₁ I⦘ ⨾ (Gsb ⨾ ⦗W ∩₁ Rel⦘).
Proof.
generalize RELCOV, (dom_sb_covered TCCOH).
basic_solver 12.
Qed.

Lemma Crfi_Acq :
 ⦗set_compl Init⦘ ⨾ Crfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Grfi ⨾ ⦗R ∩₁ Acq⦘.
Proof.
arewrite (R ∩₁ Acq ⊆₁ R ∩₁ Acq ∩₁ D ∪₁ R ∩₁ Acq ∩₁ set_compl D).
by unfolder; ins; desf; destruct (classic (D x)); auto.
rewrite id_union; relsf; unionL.
{ generalize cert_rfi_D. clear. 
  unfolder; ins; desf; splits; auto.
  apply H; eauto. }
rewrite (wf_rfiE WF_cert).
rewrite cert_E.
unfolder; ins; desf; splits; try done.
exploit COMP_ACQ; [basic_solver|].
intros [w A]; desf.
unfold rfi in H0; unfolder in H0; desc.
hahn_rewrite cert_sb in H6.
apply rfi_union_rfe in A; unfolder in A; desf; cycle 1.
{ assert (D y). 
unfold D; right; basic_solver 21.
forward (eapply ((proj1 cert_rf_D) x y)); ins. }
destruct (classic (w = x)); subst; try done.
exfalso.
unfold rfi in A; unfolder in A; desf.
assert (LOC: Gsame_loc x w).
{ eapply same_loc_trans.
  apply cert_same_loc, WF_cert.(wf_rfl); edone.
  eapply same_loc_sym.
  apply WF.(wf_rfl); edone. }
eapply sb_semi_total_r in H7; try edone.
desf; cycle 1.
{ eapply cert_coherence.
  exists y; splits.
  clear H6; vauto.
  right; apply fr_in_eco.
  exists x; splits; try done.
  eapply (w_r_loc_w_in_co (WF_cert) (wf_sbE _)).
  by apply sb_irr.
  { rewrite sb_in_hb.
    generalize cert_coherence; unfold coherence.
    basic_solver 12. }
  unfolder; splits; eauto.
  by apply WF_cert.(wf_rfD) in H0; unfolder in H0; desf.
  by apply cert_same_loc.
  by apply cert_W; apply WF.(wf_rfD) in A; unfolder in A; desf. }
eapply COH.
exists y; splits.
clear A0; vauto.
right; apply fr_in_eco.
exists w; splits; try done.
eapply (w_r_loc_w_in_co (WF) (wf_sbE _)).
by apply sb_irr.
{ rewrite sb_in_hb.
  generalize COH; unfold coherence.
  basic_solver 12. }
unfolder; splits; eauto.
by apply WF.(wf_rfD) in A; unfolder in A; desf.
by apply same_loc_sym.
by apply cert_W; apply WF_cert.(wf_rfD) in H0; unfolder in H0; desf.
Qed.

Lemma cert_ar_int_I : Car_int⁺ ⨾ ⦗ C ∪₁ I ⦘ ⊆ ⦗ D ∪₁ R ∩₁ Acq ⦘ ⨾ Gar_int⁺.
Proof.
rewrite (ct_ar_int_alt WF_cert).
2: by apply (coherence_sc_per_loc cert_coherence).
rewrite cert_R, cert_Acq, cert_sb, cert_W_ex_acq, cert_W.
rewrite cert_same_loc, cert_Rel, cert_AcqRel, cert_F, cert_W_ex.
relsf; unionL.
- unfold ar_int, bob, fwbob.
case_refl Gsb.
rewrite (dom_l (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, C_in_D.
rewrite <- ct_step; basic_solver 12.
rewrite (dom_l (@wf_sbE G)) at 2.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite ct_begin, <- inclusion_t_rt, <- ct_step; basic_solver 32.
- unfold ar_int, bob.
rewrite <- ct_step; basic_solver 12.
- unfold ar_int, bob, fwbob.
case_refl Gsb.
rewrite (dom_r (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite <- ct_step; basic_solver 21.
rewrite (dom_r (@wf_sbE G)) at 1.
generalize E_F_AcqRel_in_C, (dom_sb_covered TCCOH), C_in_D.
rewrite ct_begin, <- inclusion_t_rt, <- ct_step; basic_solver 32.
- unfold ar_int, bob, fwbob.
rewrite W_rel_sb_loc_W_CI.
generalize C_in_D, I_in_D.
rewrite <- ct_step; basic_solver 21.
- unfold ar_int, bob, fwbob.
rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).
rewrite <- seqA.
sin_rewrite sb_W_rel_CI.
generalize C_in_D, I_in_D.
rewrite <- ct_cr, <- ct_step; basic_solver 32.

- rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.

arewrite (Cppo ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.


rewrite <-ct_step.

unfold ar_int; basic_solver 12.

- rewrite !seqA.
rewrite (cr_helper W_rel_sb_loc_W_CI).


arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 3.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.


arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^?⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo^?  ⊆ Gar_int^?).
unfold ar_int; basic_solver 12.

rewrite <- (ct_cr Gar_int).
hahn_frame_r.

apply ct_inclusion_from_rt_inclusion1.

{ rewrite detour_in_sb, !(ppo_in_sb WF_cert).
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗GW_ex_acq⦘ at 1.
arewrite (Gsb ∩ Gsame_loc ⊆ Gsb) at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗GW_ex⦘ at 1.
arewrite (Gsb ∩ Gsame_loc ⊆ Gsb) at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite (Crfi ⊆ sb certG) at 1.
rewrite cert_sb.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id ⦗W⦘ at 1.
generalize (@sb_trans G); ins; relsf.
apply sb_acyclic. }



apply rt_ind_right with (P:= fun r =>  r ⨾ ⦗D⦘).
by auto with hahn.
by basic_solver.

intros k H; rewrite !seqA.

 relsf; unionL.
* case_refl (⦗R ∩₁ Acq⦘ ⨾ Gsb).
+
rewrite cert_detour_D.

arewrite (Gdetour  ⊆ Gar_int).
rewrite (rt_end Gar_int); relsf; unionR right.
hahn_frame_r.

arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).


rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.

+
rewrite !seqA, cert_detour_R_Acq_sb_D.
arewrite (⦗R ∩₁ Acq⦘ ⨾ Gsb  ⊆ Gar_int).
by unfold ar_int, bob, fwbob; basic_solver 21.

rewrite (rt_end Gar_int); relsf; unionR right.
hahn_frame_r.

arewrite (Gdetour  ⊆ Gar_int^?).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.
arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘).
rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.


arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.
* 
rewrite (dom_l (@wf_sbE G)) at 3; rewrite !seqA.

arewrite (⦗GW_ex_acq⦘ ⨾ ⦗E⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ ⦗GW_ex_acq⦘ ⨾ ⦗E⦘).
generalize W_ex_E; basic_solver 21.

arewrite (⦗GW_ex_acq⦘ ⨾ ⦗E⦘ ⨾ Gsb ⨾ ⦗W⦘  ⊆ Gar_int^?).
by unfold ar_int, bob, fwbob; basic_solver 21.
arewrite_id ⦗D⦘; rels.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (rt_cr Gar_int).
hahn_frame_r.

rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.

*
arewrite (Crfi ⊆ ⦗E⦘ ⨾ Crfi).
{ unfold rfi.
  rewrite cert_sb.
  rewrite (dom_l (@wf_sbE G)).
  basic_solver. }


arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ ⦗GW_ex⦘).
generalize W_ex_E; basic_solver 21.

arewrite (⦗GW_ex⦘ ⊆ ⦗GW_ex⦘ ;; ⦗set_compl Init⦘).
by generalize (W_ex_not_init WF); basic_solver.
sin_rewrite Crfi_Acq.
rewrite !seqA.

arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ;; ⦗R ∩₁ Acq⦘).
basic_solver.
arewrite (⦗R ∩₁ Acq⦘ ⨾ Gsb^? ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
arewrite (⦗GW_ex⦘ ⨾ Grfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ Gar_int^*).
rels.

arewrite_id ⦗D⦘; rels.
rewrite <- (rt_rt Gar_int) at 2.
hahn_frame_r.
rewrite (cr_helper W_rel_sb_loc_W_CI).

arewrite ((⦗W ∩₁ Rel⦘ ⨾ Gsb ∩ Gsame_loc ⨾ ⦗W⦘)^?  ⊆ Gar_int^?) at 1.
unfold ar_int, bob, fwbob; basic_solver 21.

rewrite <- (rt_cr Gar_int).
hahn_frame_r.

rewrite (cr_helper sb_W_rel_CI).

arewrite ((Gsb ⨾ ⦗W ∩₁ Rel⦘)^?  ⊆ Gar_int^?).
unfold ar_int, bob, fwbob; basic_solver 21.
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

arewrite (Cppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ Gppo^? ⨾ ⦗C ∪₁ I⦘).
generalize cert_ppo_CI; basic_solver 12.

arewrite (Gppo^? ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗D⦘ ⨾ Gppo^?  ).
rewrite C_in_D, I_in_D; generalize dom_ppo_D; basic_solver.

arewrite (Gppo ⊆ Gar_int).
rewrite <- (rt_cr Gar_int).
hahn_frame_r.

done.
Qed.

Lemma  cert_acyc_ext_helper : (sc ∪ certG.(rfe))⁺ ⊆ sc ∪ certG.(rfe).
Proof.
rewrite path_union.
generalize (sc_trans WF_SC); ins; relsf; unionL; [basic_solver|].
rewrite crE at 2; relsf; unionL.
-
arewrite (sc^? ⨾ rfe certG ⊆ rfe certG ).
rewrite crE; relsf; unionL; [basic_solver|].
rewrite (dom_l (wf_rfeD WF_cert)), cert_W.
rewrite (dom_r (wf_scD WF_SC)) at 1.
type_solver.

rewrite ct_begin, rtE; relsf; unionL; [basic_solver|].
rewrite ct_begin.
rewrite (dom_l (wf_rfeD WF_cert)).
rewrite (dom_r (wf_rfeD WF_cert)).
type_solver.

-
rewrite (dom_r (wf_rfeD WF_cert)), cert_R.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r, !seqA.
rewrite (dom_l (wf_scD WF_SC)) at 2.
type_solver.

Qed.


Lemma cert_acyc_ext : acyc_ext certG sc.
Proof.
red; unfold imm_s.ar.
rewrite unionC.
apply acyclic_union1.
- rewrite (ar_int_in_sb WF_cert); apply sb_acyclic.
- red; rewrite cert_acyc_ext_helper; unionL.
apply WF_SC.
arewrite (certG.(rfe) ⊆ certG.(rf)).
apply rf_irr, WF_cert.
- 
rewrite cert_acyc_ext_helper.
arewrite ((sc ∪ rfe certG) ⊆ ⦗ C ∪₁ I ⦘ ⨾ (sc ∪ rfe certG)).
{ unionL.
- rewrite (dom_l (wf_scD WF_SC)) at 1.
rewrite (dom_l (wf_scE WF_SC)) at 1.
arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
generalize E_F_AcqRel_in_C; basic_solver 12.
- rewrite cert_rfe; basic_solver 12.
}
sin_rewrite cert_ar_int_I.

rotate 1.
rewrite <- seqA.
rewrite (seq_union_l).
arewrite_id  ⦗D ∪₁ R ∩₁ Acq⦘ at 1; rels.

arewrite (rfe certG ⨾ ⦗D ∪₁ R ∩₁ Acq⦘ ⊆ Grfe).
{ rewrite cert_rfe; relsf; unionL; [basic_solver 12|].

rewrite wf_new_rfE.
generalize new_rfe_Acq.
unfolder; ins; desf; exfalso; basic_solver 21. }

arewrite (sc ⊆ Gar＊).
arewrite (Grfe ⊆ Gar＊).
arewrite (Gar_int ⊆ Gar).
relsf.
red; relsf.
Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)


Lemma cert_imm_consistent : imm_consistent certG sc.
Proof.
red; splits; eauto using WF_SC_cert, cert_acyc_ext, cert_coh_sc, cert_complete, cert_coherence, cert_rmw_atomicity.
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma dom_fwbob_I : dom_rel (Gfwbob ⨾ ⦗C ∪₁ I⦘) ⊆₁ C ∪₁ I.
Proof.
unfold fwbob; relsf; unionL; splits.
- rewrite sb_W_rel_CI; basic_solver.
- rewrite W_rel_sb_loc_W_CI; basic_solver.
- rewrite (dom_r (@wf_sbE G)).
generalize dom_sb_F_AcqRel_in_CI. basic_solver 12.
- rewrite (dom_l (@wf_sbE G)).
generalize E_F_AcqRel_in_C; basic_solver 12.
Qed.

Lemma TCCOH_cert_old : tc_coherent_alt_old certG sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof.
  assert (dom_rel (⦗GW_ex_acq⦘ ⨾ sb certG ⨾ ⦗I⦘) ⊆₁ I) as AA.
  { rewrite cert_sb. eapply tc_W_ex_sb_I; eauto.
    apply tc_coherent_implies_tc_coherent_alt; eauto. }
  assert (dom_rel (⦗GW_ex⦘ ⨾ sb certG ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb certG ⨾ ⦗I⦘) ⊆₁ I) as BB.
  { arewrite (sb certG ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb certG ⊆ sb certG).
    2: by rewrite ACQEX.
    generalize (@sb_trans certG). basic_solver. }
  assert (Wf certG) as WFCERT by apply WF_cert.

  assert (TCCOH1:= TCCOH_rst_new_T).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  constructor.
  all: try by ins.
  { ins; rewrite cert_W; done. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    rewrite (dom_l (wf_rfiD WF_cert)), cert_W.
    arewrite (Crfi ⊆ Gsb).
    generalize tc_sb_C, tc_W_C_in_I; basic_solver 21.
    rewrite cert_rfe; basic_solver 21. }
  { ins; rewrite cert_W; done. }
  { ins; rewrite cert_fwbob; done. }
  2: { ins. by rewrite cert_W_ex_acq. }
  relsf; unionL; splits; simpls.
  3,4: rewrite cert_rfe; basic_solver.
  { rewrite I_in_D at 1.
    arewrite (⦗D⦘ ⊆ ⦗D⦘ ⨾ ⦗D⦘) by basic_solver.
    sin_rewrite cert_ppo_D.
    rewrite (dom_rel_helper dom_ppo_D).
    sin_rewrite cert_detour_D.
    basic_solver. }
  2,3: rewrite cert_R, cert_Acq, cert_W_ex.
  2,3: arewrite (Crfi ⊆ sb certG).
  2,3: by try rewrite bob_in_sb; try rewrite ppo_in_sb.
  unfold bob; relsf; unionL; splits; simpls.
  { arewrite (⦗I⦘ ⊆ ⦗C ∪₁ I⦘) at 1.
    rewrite cert_fwbob.
    rewrite (dom_rel_helper dom_fwbob_I).
    rewrite C_in_D, I_in_D at 1; relsf.
    sin_rewrite cert_detour_D.
    basic_solver. }
  rewrite I_in_D at 1.
  rewrite !seqA.
  rewrite cert_sb.
  rewrite cert_R, cert_Acq.
  rewrite cert_detour_R_Acq_sb_D.
  basic_solver.
Qed.

Lemma dom_cert_ar_I : dom_rel (⦗is_w certG.(lab)⦘ ⨾ Car⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
  eapply otc_I_ar_I_implied_helper_2 with (T:=mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
  { apply TCCOH_cert_old. }
  { apply WF_cert. }
  apply WF_SC_cert.
Qed.

Lemma TCCOH_cert : tc_coherent certG sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof.
  assert (TCCOH1:= TCCOH_rst_new_T).
  apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
  destruct TCCOH1.
  apply tc_coherent_alt_implies_tc_coherent; constructor.
  all: try by ins.
  { ins; rewrite cert_W; done. }
  { rewrite rfi_union_rfe; relsf; unionL; splits; ins.
    rewrite (dom_l (wf_rfiD WF_cert)), cert_W.
    arewrite (Crfi ⊆ Gsb).
    generalize tc_sb_C, tc_W_C_in_I; basic_solver 21.
    rewrite cert_rfe; basic_solver 21. }
  { ins; rewrite cert_W; done. }
  { ins; rewrite cert_fwbob; done. }
  ins. apply dom_cert_ar_I.
Qed.

End CertExec.

