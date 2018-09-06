Require Import Classical Peano_dec.
Require Import Setoid.
Require Import ClassicalDescription.

From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events Execution Execution_eco.
Require Import ph_common ph_s_hb ph_s.
Require Import SubExecution.
Require Import CertCOhelper.

Require Import CombRelations.
Require Import TraversalConfig TraversalConfigAlt.

Set Implicit Arguments.
Remove Hints plus_n_O.


Section RestExec.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Variable Gf : execution.
Variable sc : relation actid.

Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'FE'" := Gf.(acts_set).
Notation "'Facts'" := Gf.(acts).
Notation "'Flab'" := Gf.(lab).
Notation "'Fsb'" := Gf.(sb).
Notation "'Frf'" := Gf.(rf).
Notation "'Fco'" := Gf.(co).
Notation "'Frmw'" := Gf.(rmw).
Notation "'Fdata'" := Gf.(data).
Notation "'Faddr'" := Gf.(addr).
Notation "'Fctrl'" := Gf.(ctrl).
Notation "'Fdeps'" := Gf.(deps).
Notation "'Frmw_dep'" := Gf.(rmw_dep).

Notation "'Ffre'" := Gf.(fre).
Notation "'Frfe'" := Gf.(rfe).
Notation "'Fcoe'" := Gf.(coe).
Notation "'Frfi'" := Gf.(rfi).
Notation "'Ffri'" := Gf.(fri).
Notation "'Fcoi'" := Gf.(coi).
Notation "'Ffr'" := Gf.(fr).
Notation "'Feco'" := Gf.(eco).
Notation "'Fdetour'" := Gf.(detour).
Notation "'Fsw'" := Gf.(sw).
Notation "'Frelease'" := Gf.(release).
Notation "'Frs'" := Gf.(rs).
Notation "'Fhb'" := Gf.(hb).
Notation "'Fppo'" := Gf.(ppo).
Notation "'Fbob'" := Gf.(bob).
Notation "'Ffwbob'" := Gf.(fwbob).
Notation "'Far'" := (Gf.(ar) sc).
Notation "'Furr'" := (Gf.(urr) sc).
Notation "'Fmsg_rel'" := (Gf.(msg_rel) sc).

Notation "'Floc'" := (loc Flab).
Notation "'Fval'" := (val Flab).
Notation "'Fsame_loc'" := (same_loc Flab).

Notation "'FR'" := (fun a => is_true (is_r Flab a)).
Notation "'FW'" := (fun a => is_true (is_w Flab a)).
Notation "'FF'" := (fun a => is_true (is_f Flab a)).
Notation "'FR_ex'" := (fun a => is_true (R_ex Flab a)).
Notation "'FW_ex'" := Gf.(W_ex).
Notation "'FW_ex_acq'" := (FW_ex ∩₁ (fun a => is_true (is_xacq Flab a))).

Notation "'FLoc_' l" := (fun x => Floc x = Some l) (at level 1).
Notation "'FW_' l" := (FW ∩₁ FLoc_ l) (at level 1).
Notation "'FR_' l" := (FR ∩₁ FLoc_ l) (at level 1).

Notation "'FPln'" := (fun a => is_true (is_only_pln Flab a)).
Notation "'FRlx'" := (fun a => is_true (is_rlx Flab a)).
Notation "'FRel'" := (fun a => is_true (is_rel Flab a)).
Notation "'FAcq'" := (fun a => is_true (is_acq Flab a)).
Notation "'FAcqrel'" := (fun a => is_true (is_acqrel Flab a)).
Notation "'FAcq/Rel'" := (fun a => is_true (is_ra Flab a)).
Notation "'FSc'" := (fun a => is_true (is_sc Flab a)).
Notation "'Fxacq'" := (fun a => is_true (is_xacq Flab a)).

Variable T : trav_config.

Notation "'I'" := (issued T).
Notation "'C'" := (covered T).

Variable thread : BinNums.positive.

Lemma tid_set_dec : Tid_ thread ∪₁ NTid_ thread ≡₁ (fun x => True).
Proof. unfolder; split; ins; desf; tauto. Qed.

Hypothesis WF : Wf Gf.
Hypothesis WF_SC : wf_sc Gf sc.
Hypothesis PHCON : ph_consistent Gf sc.
Hypothesis RELCOV : FW ∩₁ FRel ∩₁ I ⊆₁ C.
Hypothesis TCCOH : tc_coherent Gf sc T.
Hypothesis ACQEX : FW_ex ⊆₁ FW_ex_acq.

Definition E0 :=  C ∪₁ I ∪₁ dom_rel (Fsb ⨾ ⦗Tid_ thread ∩₁ I⦘)
  ∪₁ (dom_rel (Frmw ⨾ ⦗ NTid_ thread ∩₁ I ⦘) \₁ codom_rel (⦗ set_compl FW_ex⦘ ⨾ Frfi)).

Definition rstG := restrict Gf E0.
Definition rst_sc := <| E0 |> ;; sc ;; <| E0 |>.

Notation "'E'" := rstG.(acts_set).
Notation "'Gacts'" := rstG.(acts).
Notation "'Glab'" := rstG.(lab).
Notation "'Gsb'" := rstG.(sb).
Notation "'Grf'" := rstG.(rf).
Notation "'Gco'" := rstG.(co).
Notation "'Grmw'" := rstG.(rmw).
Notation "'Gdata'" := rstG.(data).
Notation "'Gaddr'" := rstG.(addr).
Notation "'Gctrl'" := rstG.(ctrl).
Notation "'Gdeps'" := rstG.(deps).
Notation "'Grmw_dep'" := rstG.(rmw_dep).

Notation "'Gfre'" := rstG.(fre).
Notation "'Grfe'" := rstG.(rfe).
Notation "'Gcoe'" := rstG.(coe).
Notation "'Grfi'" := rstG.(rfi).
Notation "'Gfri'" := rstG.(fri).
Notation "'Gcoi'" := rstG.(coi).
Notation "'Gfr'" := rstG.(fr).
Notation "'Geco'" := rstG.(eco).
Notation "'Gdetour'" := rstG.(detour).
Notation "'Gsw'" := rstG.(sw).
Notation "'Grelease'" := rstG.(release).
Notation "'Grs'" := rstG.(rs).
Notation "'Ghb'" := rstG.(hb).
Notation "'Gppo'" := rstG.(ppo).
Notation "'Gbob'" := rstG.(bob).
Notation "'Gfwbob'" := rstG.(fwbob).
Notation "'Gar'" := (rstG.(ar) rst_sc).
Notation "'Gurr'" := (rstG.(urr) rst_sc).
Notation "'Gmsg_rel'" := (rstG.(msg_rel) rst_sc).

Notation "'Gloc'" := (loc Glab).
Notation "'Gval'" := (val Glab).
Notation "'Gsame_loc'" := (same_loc Glab).

Notation "'R'" := (fun a => is_true (is_r Glab a)).
Notation "'W'" := (fun a => is_true (is_w Glab a)).
Notation "'F'" := (fun a => is_true (is_f Glab a)).
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW_ex'" := rstG.(W_ex).
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

Lemma E0_in_Gf : E0 ⊆₁ FE.
Proof.
unfold E0.
rewrite coveredE, issuedE; try edone.
rewrite (dom_l (@wf_sbE Gf)).
rewrite (dom_l (wf_rmwE WF)).
basic_solver.
Qed.

Lemma E_E0 : E ≡₁ E0.
Proof. by apply restrict_E, E0_in_Gf. Qed.

Lemma I_in_E : I ⊆₁ E.
Proof.
rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma C_in_E : C ⊆₁ E.
Proof.
rewrite E_E0; unfold E0; basic_solver.
Qed.

Lemma SUB: sub_execution Gf rstG sc rst_sc.
Proof. eapply restrict_sub. done. eapply E0_in_Gf. Qed.

Lemma INIT : Init ∩₁ FE ⊆₁ E.
Proof. rewrite (init_issued WF TCCOH); rewrite E_E0; unfold E0; basic_solver. Qed.

Lemma rstWF : Wf rstG.
Proof.
apply (sub_WF INIT WF SUB).
Qed.

Lemma Wex_rfi_rmw_E   :  dom_rel (⦗FW_ex⦘ ⨾ Frfi ⨾ Frmw ⨾ ⦗E⦘) ⊆₁ I.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- rewrite (rmw_in_sb WF) at 1 2.
  arewrite (Frfi ⊆ Fsb) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  rewrite ACQEX at 1.
  unfold dom_cond; basic_solver 41.
- rewrite (rmw_in_sb WF) at 1.
  arewrite (Frfi ⊆ Fsb) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  rewrite ACQEX at 1.
  unfold dom_cond; basic_solver 41.
- rewrite (rmw_in_sb WF) at 1 2.
  arewrite (Frfi ⊆ Fsb) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  rewrite ACQEX at 1.
  unfold dom_cond; basic_solver 41.
Qed.

Lemma rfe_rmw_E   :  dom_rel (Frfe ⨾ Frmw ⨾ ⦗E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  rewrite (rmw_in_ppo WF) at 1.
  unfold dom_cond; basic_solver 21.
- unionR left -> left -> right.
  rewrite <- seqA, dom_rel_eqv_dom_rel, !seqA.
  arewrite (⦗Tid_ thread ∩₁ I⦘ ⊆ ⦗I⦘ ;; ⦗Tid_ thread ∩₁ I⦘) at 1.
  basic_solver.
  rewrite (issuedW TCCOH) at 1.
  sin_rewrite (rmw_sb_W_in_ppo WF).
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  unfold dom_cond; basic_solver 21.
- rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  type_solver.
Qed.

Lemma rfe_rmw_I   :  dom_rel (Frfe ⨾ Frmw ⨾ ⦗I⦘) ⊆₁ I.
Proof.
rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  rewrite (rmw_in_ppo WF) at 1.
  unfold dom_cond; basic_solver 21.
Qed.

Lemma rmw_E_rfe :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel Frfe ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
  by unfolder; ins; desf; tauto.
  relsf; unionL; splits.
  * rewrite (rmw_in_sb WF) at 1.
    basic_solver 12.
  * unionR right.
    unfolder; ins; desf; splits; eauto.
    intro; ie_unfolder; unfolder in *; desf.
    assert (x0 = x1).
    eapply WF; basic_solver 12.
    subst; eauto.
- rewrite dom_rel_eqv_dom_rel.
  rewrite (rmw_in_sb WF) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  basic_solver 12.
- rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  type_solver.
Qed.

Lemma rmw_E_rfi :  dom_rel (Frmw ⨾ ⦗E⦘) ∩₁ codom_rel (⦗FW_ex⦘ ⨾ Frfi) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (rmw_in_sb WF) at 1.
  generalize dom_sb_covered, dom_rf_covered; ie_unfolder; basic_solver 21.
- arewrite (⦗I⦘ ⊆ ⦗Tid_ thread ∩₁ I⦘ ∪ ⦗NTid_ thread ∩₁ I⦘).
  by unfolder; ins; desf; tauto.
  relsf; unionL; splits.
  * rewrite (rmw_in_sb WF) at 1.
    basic_solver 12.
  * unionR right.
    unfolder; ins; desf; splits; eauto.
    intro; ie_unfolder; unfolder in *; desf.
    assert (x0 = x1).
    eapply WF; basic_solver 12.
    subst; eauto.
- rewrite dom_rel_eqv_dom_rel.
  rewrite (rmw_in_sb WF) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  basic_solver 12.
- rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite (dom_l (wf_rmwD WF)) at 2.
  type_solver.
Qed.
(*
Lemma rt_rf_rmw_E : (Frf ⨾ Frmw)＊ ⨾ ⦗E⦘ ⊆  (Frfi ⨾  Frmw)^? ⨾ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾  Frmw ⨾ ⦗E⦘)＊ ⨾ ⦗E⦘.
Proof.
rewrite rt_begin, !seqA.
relsf; unionL; [basic_solver 12|].
rewrite rmw_W_ex at 1 2; rewrite !seqA.
rewrite <- !(seqA Frf Frmw).
seq_rewrite <- rt_seq_swap.
arewrite_id ⦗FW_ex⦘ at 2; relsf.
apply rt_ind_left with (P:= fun r => Frf ⨾ Frmw ⨾ r ⨾ ⦗E⦘).
- eauto with hahn.
- rewrite rfi_union_rfe at 1; relsf.
  unionL; [basic_solver 42|].
  rewrite <- inclusion_t_rt, <- ct_step.
  generalize rfe_rmw_E rmw_E_rfe; ie_unfolder; basic_solver 80.
- intros k H. 
  rewrite !seqA, H.
  arewrite (⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘ )^?).
  generalize rmw_E_rfi Wex_rfi_rmw_E; ie_unfolder; basic_solver 80.
  relsf; rewrite rfi_union_rfe at 1; relsf.
  unionL; [basic_solver 40|].
  arewrite (Frfe ⨾ Frmw ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘)^?).
  generalize rmw_E_rfe rfe_rmw_E; ie_unfolder; basic_solver 80.
  relsf; basic_solver 21.
Qed.
*)

Lemma rt_rf_rmw_I : (Frf ⨾ Frmw)＊ ⨾ ⦗I⦘ ⊆  (Frfi ⨾  Frmw)^? ⨾ ⦗I⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾  Frmw ⨾ ⦗E⦘)＊ ⨾ ⦗E⦘.
Proof.
rewrite rt_begin, !seqA.
relsf; unionL.
generalize I_in_E; basic_solver 12.
rewrite rmw_W_ex at 1 2; rewrite !seqA.
rewrite <- !(seqA Frf Frmw).
seq_rewrite <- rt_seq_swap.
arewrite_id ⦗FW_ex⦘ at 2; relsf.
apply rt_ind_left with (P:= fun r => Frf ⨾ Frmw ⨾ r ⨾ ⦗I⦘).
- eauto with hahn.
- rewrite rfi_union_rfe at 1; relsf.
  unionL; [generalize I_in_E; basic_solver 42|].
  rewrite <- inclusion_t_rt, <- ct_step.
  rewrite (dom_rel_helper_in rfe_rmw_I).
  generalize I_in_E rfe_rmw_I rmw_E_rfe; ie_unfolder; basic_solver 80.
- intros k H. 
  rewrite !seqA, H.
arewrite (⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘ ⊆ ⦗I⦘ ;; ⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗I⦘).
eapply dom_rel_helper_in.



rewrite crE; relsf; unionL; splits; [basic_solver 12|].
rewrite (issued_in_issuable TCCOH) at 1.
rewrite ACQEX at 1.
generalize (wex_rfi_rfe_rmw_issuable_is_issued WF TCCOH).
basic_solver 21.


rewrite I_in_E at 2.
  arewrite (⦗FW_ex⦘ ⨾ (Frfi ⨾ Frmw)^? ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘ )^?).
  generalize I_in_E rmw_E_rfi Wex_rfi_rmw_E; ie_unfolder; basic_solver 80.
  relsf; rewrite rfi_union_rfe at 1; relsf.
  remember (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘) as X.

  unionL; [basic_solver 40|].

  arewrite (Frfe ⨾ Frmw ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ Frfe ⨾ Frmw).
generalize rfe_rmw_I; basic_solver 12.
  arewrite (Frfe ⨾ Frmw ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘)^?).

  generalize rmw_E_rfe rfe_rmw_E; ie_unfolder; basic_solver 80.
subst.
  relsf. 
  remember (⦗E⦘ ⨾ Frf ⨾ ⦗E⦘ ⨾ Frmw ⨾ ⦗E⦘) as X.
basic_solver 21.
Qed.

(*
Lemma W_Rel_sb_loc_E : dom_rel (⦗FW ∩₁ FRel⦘ ⨾  (Fsb ∩  Fsame_loc) ⨾ ⦗FW ∩₁ E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_r.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_sb_covered; ie_unfolder; basic_solver 21.
- generalize (dom_sb_loc_issued TCCOH); basic_solver 21.
- generalize (@sb_trans Gf); basic_solver 21.
- rewrite (dom_l (wf_rmwD WF)) at 1; type_solver.
Qed.
*)
Lemma W_Rel_sb_loc_I : dom_rel (⦗FW ∩₁ FRel⦘ ⨾  (Fsb ∩  Fsame_loc) ⨾ ⦗FW ∩₁ I⦘) ⊆₁ I.
Proof.
generalize (dom_sb_loc_issued TCCOH), (w_covered_issued TCCOH); basic_solver 21.
Qed.
(*
Lemma F_sb_E :  dom_rel (⦗FF ∩₁ FAcq/Rel⦘ ⨾  Fsb ⨾ ⦗E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_sb_covered; ie_unfolder; basic_solver 21.
- generalize (dom_F_sb_issued TCCOH); basic_solver 21.
- generalize (@sb_trans Gf); basic_solver 21.
- rewrite (rmw_in_sb WF) at 1.
  generalize (@sb_trans Gf); ins; relsf.
  unionR left -> left -> left.
  generalize (dom_F_sb_issued TCCOH); basic_solver 12.
Qed. 

Lemma F_Rel_sb_E :  dom_rel (⦗FF ∩₁ FRel⦘ ⨾  Fsb ⨾ ⦗E⦘) ⊆₁ E.
Proof. etransitivity; [|apply F_sb_E]; mode_solver 21. Qed.

Lemma F_Acq_sb_E :  dom_rel (⦗FF ∩₁ FAcq⦘ ⨾  Fsb ⨾ ⦗E⦘) ⊆₁ E.
Proof. etransitivity; [|apply F_sb_E]; mode_solver 12. Qed.
*)

(* next three lemmas belong to traversal_config.v *)

Lemma F_sb_I :  dom_rel (⦗FF ∩₁ FAcq/Rel⦘ ⨾  Fsb ⨾ ⦗I⦘) ⊆₁ C.
Proof.
generalize (dom_F_sb_issued TCCOH); basic_solver 21.
Qed. 

Lemma F_Rel_sb_I :  dom_rel (⦗FF ∩₁ FRel⦘ ⨾  Fsb ⨾ ⦗I⦘) ⊆₁ C.
Proof. etransitivity; [|apply F_sb_I]; mode_solver 21. Qed.

Lemma F_Acq_sb_I :  dom_rel (⦗FF ∩₁ FAcq⦘ ⨾  Fsb ⨾ ⦗I⦘) ⊆₁ C.
Proof. etransitivity; [|apply F_sb_I]; mode_solver 12. Qed.
(*
Lemma release_E : Frelease ⨾ ⦗E⦘ ⊆ Grelease.
Proof.
unfold ph_s_hb.release.
rewrite (sub_F SUB), (sub_Rel SUB).
rewrite !seqA; unfold ph_s_hb.rs.
rewrite (sub_W SUB), (sub_same_loc SUB).
rewrite !seqA.
rewrite rt_rf_rmw_E.
arewrite (⦗E⦘ ⊆  ⦗E⦘ ⨾ ⦗E⦘) at 3.
basic_solver.
seq_rewrite <- (sub_rf SUB).
seq_rewrite <- (sub_rmw SUB).
arewrite ((Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ (Frfi ⨾ Frmw)^? ⊆ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘).
{ case_refl (Frfi ⨾ Frmw); [done|].
  arewrite_id  ⦗W⦘.
  rewrite (dom_r (wf_rmwD WF)).
  rewrite (rfi_in_sbloc' WF).
  rewrite (rmw_in_sb_loc WF) at 1.
  generalize (@sb_same_loc_trans Gf); ins; relsf. }
case_refl (⦗F⦘ ⨾ Fsb).
- arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ ((⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘) ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗E⦘).
  generalize W_Rel_sb_loc_E; basic_solver 21.
  seq_rewrite <- (sub_sb SUB); basic_solver 40.
- arewrite ((Fsb ∩ Fsame_loc)^? ⊆ Fsb^?) at 1.
  arewrite_id ⦗FW⦘ at 1.
  generalize (@sb_trans Gf); ins; relsf.
  arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ Fsb ⨾ ⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ ⦗Rel⦘ ⨾ ⦗F⦘ ⨾ ⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘).
  generalize F_Rel_sb_E; basic_solver 21.
  remember (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⨾ ⦗E0⦘ ⨾ Frmw ⨾ ⦗E0⦘) as X.
  ins; seq_rewrite <- (sub_sb SUB); basic_solver 21.
Qed.
*)
Lemma release_I : Frelease ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ Grelease.
Proof.
unfold ph_s_hb.release.
rewrite (sub_F SUB), (sub_Rel SUB).
rewrite !seqA; unfold ph_s_hb.rs.
rewrite (sub_W SUB), (sub_same_loc SUB).
rewrite !seqA.
rewrite rt_rf_rmw_I.
arewrite (⦗E⦘ ⊆  ⦗E⦘ ⨾ ⦗E⦘) at 2.
basic_solver.
seq_rewrite <- (sub_rf SUB).
seq_rewrite <- (sub_rmw SUB).
arewrite ((Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ (Frfi ⨾ Frmw)^? ⊆ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘).
{ case_refl (Frfi ⨾ Frmw); [done|].
  arewrite_id  ⦗W⦘.
  rewrite (dom_r (wf_rmwD WF)).
  rewrite (rfi_in_sbloc' WF).
  rewrite (rmw_in_sb_loc WF) at 1.
  generalize (@sb_same_loc_trans Gf); ins; relsf. }
case_refl (⦗F⦘ ⨾ Fsb).
- arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Fsb ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ ((⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘) ∩ Fsame_loc)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘).
  generalize W_Rel_sb_loc_I I_in_E; basic_solver 21.

  seq_rewrite <- (sub_sb SUB); revert RELCOV; basic_solver 40.
- arewrite ((Fsb ∩ Fsame_loc)^? ⊆ Fsb^?) at 1.
  arewrite_id ⦗FW⦘ at 1.
  generalize (@sb_trans Gf); ins; relsf.
  arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ Fsb ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗F⦘ ⨾ ⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘).
  generalize F_Rel_sb_I, C_in_E, I_in_E; basic_solver 21.
  remember (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⨾ ⦗E0⦘ ⨾ Frmw ⨾ ⦗E0⦘) as X.
  ins; seq_rewrite <- (sub_sb SUB); basic_solver 21.
Qed.


Lemma sb_F_E : dom_rel (Fsb ⨾ ⦗FF ∩₁ FAcq/Rel ∩₁ E⦘) ⊆₁ C ∪₁ I.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_r.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (issuedW TCCOH) at 1; type_solver.
- generalize F_sb_I, (dom_sb_covered TCCOH); basic_solver 21.
- rewrite (dom_l (wf_rmwD WF)) at 1; type_solver.
Qed.

Lemma rfe_E :  dom_rel (Frfe ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_rf_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_r (wf_rfeD WF)) at 1; rewrite (issuedW TCCOH) at 1.
  type_solver.
- arewrite (Frfe ⊆ Frfe  ⨾  ⦗set_compl Init⦘).
  { rewrite (dom_r (wf_rfeD WF)).
    rewrite (init_w WF).
    unfolder; ins; desf; splits; eauto.
    intro; type_solver. }
  unfolder; ins; desf.
  apply sb_tid_init in H1; desf.
- arewrite (⦗NTid_ thread ∩₁ I⦘ ⊆ ⦗I⦘ ;; ⦗NTid_ thread ∩₁ I⦘) at 1.
  basic_solver.
  rewrite (issuedW TCCOH) at 1.
  rewrite (rmw_in_ppo WF).
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  unfold dom_cond; basic_solver 21.
Qed.

Lemma Grfe_E :  dom_rel (Grfe) ⊆₁ I.
Proof.
rewrite (dom_l (wf_rfeE rstWF)).
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (dom_l (wf_rfeD rstWF)).
  generalize (w_covered_issued TCCOH).
  basic_solver.
- basic_solver.
- rewrite (dom_r (wf_rfeE rstWF)).
  arewrite (⦗E⦘ ⊆ ⦗E ∩₁ NTid_ thread⦘ ∪ ⦗E ∩₁ Tid_ thread⦘).
  unfolder; ins; desf; tauto.
  relsf; splits.
  rewrite (sub_rfe_in SUB), rfe_E; basic_solver.
  rewrite (sub_rfe_in SUB).
  unfolder; ins; desf; exfalso.
  cdes PHCON.
  generalize (thread_rfe_sb WF (coherence_sc_per_loc Cint)).
  unfold same_tid; basic_solver 21. 
- rewrite (dom_l (wf_rmwD WF)).
  rewrite (dom_l (wf_rfeD rstWF)).
  type_solver.
Qed.

Lemma rfi_E : dom_rel (Frfi ⨾ ⦗E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_r (wf_rfiD WF)) at 1; rewrite (issuedW TCCOH) at 1; type_solver.
- generalize (@sb_trans Gf); ie_unfolder; basic_solver 21.
- rewrite (dom_l (wf_rfiD WF)) at 1.
  arewrite (⦗W⦘ ⊆ ⦗FW_ex⦘ ∪ ⦗set_compl FW_ex⦘).
  by unfolder; ins; desf; tauto.
  relsf; unionL; splits.
  * unionR left -> left -> right.
    rewrite (rmw_in_sb WF) at 1.
    arewrite (Frfi ⊆ Fsb) at 1.
    generalize (@sb_trans Gf); ins; relsf.
    rewrite (issued_in_issuable TCCOH) at 1.
    unfold issuable.
    rewrite ACQEX at 1.
    unfold dom_cond; basic_solver 41.
  * unfolder; ins; desf; exfalso; eauto 10.
Qed.

Lemma rfe_Acq_E   :  dom_rel (Frfe ⨾ ⦗E ∩₁ FAcq⦘) ⊆₁ I.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_rf_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_r (wf_rfeD WF)) at 1; rewrite (issuedW TCCOH) at 1; type_solver.
- rewrite (dom_r (wf_rfeD WF)).
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable.
  unfold bob.
  unfold dom_cond; basic_solver 21.
- generalize rfe_rmw_I; basic_solver 21.
Qed.

Lemma rfe_sb_F_E   :  dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq/Rel⦘) ⊆₁ I.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_rf_covered dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (issuedW TCCOH) at 1; type_solver.
- arewrite (dom_rel (Fsb ⨾ ⦗Tid_ thread ∩₁ I⦘) ∩₁ FF ∩₁ FAcq/Rel ⊆₁ C).
  { arewrite (⦗Tid_ thread ∩₁ I⦘ ⊆ ⦗I⦘ ;; ⦗Tid_ thread ∩₁ I⦘) at 1.
    basic_solver.
    rewrite (issued_in_issuable TCCOH) at 1.
    unfold issuable.
    unfold fwbob.
    unfold dom_cond; 
    basic_solver 40. }
  generalize dom_rf_covered dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_l (wf_rmwD WF)) at 1; type_solver.
Qed.

Lemma rfe_sb_F_Acq_E   :  dom_rel (Frfe ⨾ Fsb ⨾ ⦗E ∩₁ FF ∩₁ FAcq⦘) ⊆₁ I.
Proof. 
etransitivity; [|apply rfe_sb_F_E].
unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

Lemma rfe_sb_F_Rel_E   :  dom_rel (Frfe ⨾  Fsb ⨾ ⦗E ∩₁ FF ∩₁ FRel⦘) ⊆₁ I.
Proof.
etransitivity; [|apply rfe_sb_F_E].
unfolder; ins; desf; eexists; eexists; splits; eauto; mode_solver 21. 
Qed.

(*
Lemma sw_E : Fsw ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ Gsw.
Proof.
rewrite (dom_r (wf_swE WF)).
rewrite (dom_r (wf_swD WF)).
arewrite (⦗FE⦘ ⊆ ⦗FE \₁ E⦘ ∪ ⦗E⦘) by (unfolder; ins; desf; tauto).
relsf; unionL; [basic_solver 12|].
arewrite (⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘) by basic_solver.
unfold ph_s_hb.sw.
rewrite (sub_F SUB), (sub_Acq SUB).
rewrite !seqA.
arewrite ((Fsb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ (Fsb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗E⦘).
by generalize sb_F_E; basic_solver 21.
arewrite (Frf ⨾ ⦗E⦘ ⨾ (Fsb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾  Frf ⨾ ⦗E⦘ ⨾ (Fsb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗E⦘).
{ rewrite rfi_union_rfe; relsf; unionL.
  by generalize rfi_E; basic_solver 21.
  generalize rfe_Acq_E rfe_sb_F_Acq_E; basic_solver 21. }
arewrite (⦗E⦘ ⊆ ⦗E⦘ ⨾ ⦗E⦘) at 1.
basic_solver.
sin_rewrite release_E.
rewrite (sub_rf SUB), (sub_sb SUB).
basic_solver 80.
Qed.

Lemma dom_sw_E : dom_rel (Fsw ⨾ ⦗E⦘) ⊆₁ E.
Proof. rewrite sw_E, (dom_l (wf_swE rstWF)); basic_solver. Qed.

Lemma sb_W_Rel_E : dom_rel (Fsb ⨾ ⦗FW ∩₁ FRel ∩₁ E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !set_inter_union_r.
rewrite !id_union; relsf; unionL; splits.
- generalize dom_rf_covered dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite RELCOV; generalize dom_sb_covered; basic_solver 21.
- generalize (@sb_trans Gf); basic_solver 21.
- rewrite (dom_l (wf_rmwD WF)) at 1; type_solver.
Qed.

Lemma dom_sb_sw_E : dom_rel ((Fsb^? ⨾ Fsw) ⨾ ⦗E⦘) ⊆₁ E.
Proof.
rewrite (dom_l (wf_swD WF)).
rewrite !seqA, sw_E.
rewrite (dom_l (wf_swE rstWF)).
generalize sb_F_E sb_W_Rel_E; basic_solver 21.
Qed.



Lemma hb_Rel_E : Fhb ⨾ ⦗E ∩₁ (FF ∪₁ FW) ∩₁ Rel⦘ ⊆ Ghb.
Proof.
cut (Fhb ⨾ ⦗E ∩₁ (FF ∪₁ FW) ∩₁ Rel⦘ ⊆ Ghb ⨾ ⦗E ∩₁ (FF ∪₁ FW) ∩₁ Rel⦘).
by intro H; rewrite H; basic_solver 12.
unfold ph_s_hb.hb.
apply ct_ind_left with (P:= fun r => r ⨾ ⦗E ∩₁ (FF ∪₁ FW) ∩₁ Rel⦘).
* by eauto with hahn.
* relsf; unionL.
rewrite <- ct_step; generalize (sub_sb SUB), sb_F_E, sb_W_Rel_E; basic_solver 40.
rewrite <- ct_step; generalize dom_sw_E, sw_E; basic_solver 40.
* intros k H; rewrite !seqA, H.
rewrite (dom_l (wf_hbE rstWF)).
unfold ph_s_hb.hb.
relsf; unionL.
2: { rewrite !seqA.
sin_rewrite sw_E.
rewrite (dom_l (wf_swE rstWF)) at 1.
arewrite (Gsw ⊆ (Gsb ∪ Gsw)＊) at 1; relsf. }

rewrite !seqA.
arewrite_id ⦗E⦘ at 1; rels.
sin_rewrite hb_helper.
rewrite (sub_sb_in SUB) at 1 2.
generalize (@sb_trans Gf); ins; relsf.
rewrite !seqA; relsf.
unionL.
- rewrite <- ct_step.
rewrite (sub_sb SUB); generalize sb_F_E sb_W_Rel_E; basic_solver 40.
- 
arewrite (Fsb ⨾ ⦗E ∩₁ F ∩₁ Rel ∪₁ E ∩₁ W ∩₁ Rel⦘ ⊆ ⦗E⦘ ⨾ Gsb).
rewrite (sub_sb SUB); generalize sb_F_E sb_W_Rel_E; basic_solver 40.

unfold ph_s_hb.hb.
arewrite (Gsb ⊆ (Gsb ∪ Gsw)＊).
relsf.
Qed.
*)
Lemma rf_C : Frf ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Grf.
Proof.
rewrite (sub_rf SUB).
rewrite <- I_in_E at 1.
rewrite <- C_in_E at 1.
generalize dom_rf_covered; basic_solver 21.
Qed.

Lemma sw_C : Fsw ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsw.
Proof.
unfold sw; rewrite !seqA.
arewrite ((Fsb ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (⦗E⦘ ⨾ Fsb ⨾ ⦗E⦘ ⨾ ⦗FF⦘)^? ⨾ ⦗FAcq⦘).
by generalize (dom_sb_covered TCCOH) C_in_E; basic_solver 21.
sin_rewrite rf_C.
rewrite !seqA.
sin_rewrite release_I.
seq_rewrite <- (sub_sb SUB). 
by rewrite !seqA.
Qed.


Lemma sb_C : Fsb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Gsb.
Proof.
rewrite (sub_sb SUB).
rewrite <- C_in_E.
generalize dom_sb_covered; basic_solver 21.
Qed.

Lemma hb_C : Fhb ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ Ghb.
Proof.
unfold hb.
apply ct_ind_left with (P:= fun r => r ⨾ ⦗C⦘).
- eauto with hahn.
- rewrite <- ct_step.
by relsf; rewrite sb_C, sw_C.
- intros k H; rewrite !seqA; sin_rewrite H.
relsf; sin_rewrite sb_C; sin_rewrite sw_C.
rewrite !seqA.
arewrite (Gsb ⊆ (Gsb ∪ Gsw)^*) at 1.
arewrite (Gsw ⊆ (Gsb ∪ Gsw)^*) at 3.
relsf.
Qed.

Lemma sc_C : sc ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ rst_sc.
Proof.
unfold rst_sc.
rewrite <- E_E0.
rewrite <- C_in_E.
cut (dom_rel (sc ⨾ ⦗C⦘) ⊆₁ C).
by basic_solver 21.
rewrite (covered_in_coverable TCCOH) at 1.
rewrite (dom_r (wf_scD WF_SC)) at 1.
unfold coverable, dom_cond; type_solver 21.
Qed.
(*
Lemma sc_E : dom_rel (sc ⨾ ⦗E⦘) ⊆₁ E.
Proof.
rewrite E_E0; unfold E0.
rewrite !id_union; relsf; unionL; splits.
- rewrite (covered_in_coverable TCCOH) at 1.
  rewrite (dom_r (wf_scD WF_SC)) at 1.
  unfold coverable, dom_cond; type_solver 21.
- rewrite (dom_r (wf_scD WF_SC)) at 1.
  rewrite (issuedW TCCOH) at 1.
  type_solver.
- rewrite (dom_r (wf_scD WF_SC)) at 1.
  rewrite !seqA.
  arewrite (FSc ⊆₁ FAcq/Rel) by mode_solver. 
  arewrite (⦗FF ∩₁ FAcq/Rel⦘ ⨾ ⦗dom_rel (Fsb ⨾ ⦗Tid_ thread ∩₁ I⦘)⦘ ⊆ ⦗C⦘).
  { arewrite (⦗Tid_ thread ∩₁ I⦘ ⊆ ⦗I⦘ ;; ⦗Tid_ thread ∩₁ I⦘) at 1.
    basic_solver.
    rewrite (issued_in_issuable TCCOH) at 1.
    unfold issuable.
    unfold fwbob.
    unfold dom_cond; 
    basic_solver 40. }
  rewrite (covered_in_coverable TCCOH) at 1.
  rewrite (dom_r (wf_scD WF_SC)) at 1.
  unfold coverable, dom_cond; type_solver 21.
- rewrite (dom_r (wf_scD WF_SC)) at 1; rewrite (dom_l (wf_rmwD WF)) at 1; type_solver.
Qed.
*)


Lemma urr_C l : Furr l  ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ Gurr l.
Proof.
unfold CombRelations.urr.
rewrite !seqA, (sub_W_ SUB), (sub_F SUB), (sub_Sc SUB).
rewrite (cr_helper hb_C).
sin_rewrite (cr_helper sc_C).
rewrite !seqA.
arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
{ generalize hb_C.
unfolder; ins; desf; splits; eauto 20.
eapply H; eauto.
right; eexists; splits; eauto.
eapply H; eauto. }
arewrite (⦗FW_ l⦘ ⨾ Frf^? ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ ⦗FW_ l⦘ ⨾ Grf^?).
{ rewrite crE; relsf; unionL.
generalize w_covered_issued; basic_solver 21.
sin_rewrite rf_C; basic_solver 21. }
done.
Qed.

Lemma msg_rel_I l : Gmsg_rel l ⨾ ⦗ I ⦘ ≡ Fmsg_rel l ⨾ ⦗ I ⦘.
Proof.
unfold CombRelations.msg_rel.
split.
by rewrite (sub_urr_in SUB), (sub_release_in SUB).
arewrite (⦗I⦘ ⊆ ⦗I⦘ ⨾ ⦗I⦘) at 1.
by basic_solver.
sin_rewrite release_I.
rewrite !seqA.
sin_rewrite urr_C.
basic_solver.
Qed.


Lemma t_cur_thread l : t_cur rstG rst_sc thread l
  (covered T) ≡₁ t_cur Gf sc thread l (covered T).
Proof.
unfold t_cur, c_cur.
split.
rewrite (sub_urr_in SUB); basic_solver 12.
arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ;; ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma t_rel_thread l l' : t_rel rstG rst_sc thread l l'
  (covered T) ≡₁ t_rel Gf sc thread l l' (covered T).
Proof.
unfold t_rel, c_rel.
split.
rewrite (sub_urr_in SUB); basic_solver 12.
arewrite (⦗FRel⦘ ⨾ ⦗FW_ l' ∪₁ FF⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ;; 
⦗FRel⦘ ⨾ ⦗FW_ l' ∪₁ FF⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma t_acq_thread l : t_acq rstG rst_sc thread l
  (covered T) ≡₁ t_acq Gf sc thread l (covered T).
Proof.
unfold t_acq, c_acq.
split.
rewrite (sub_urr_in SUB), (sub_release_in SUB), (sub_rf_in SUB) ; basic_solver 12.
arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ;; ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗C⦘).
basic_solver.
arewrite ((Frelease ⨾ Frf)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ;; (Grelease ⨾ Grf)^? ).
{ case_refl _; [basic_solver|].
  rewrite !seqA.
  sin_rewrite rf_C.
  sin_rewrite release_I. 
  basic_solver 12. }
  sin_rewrite (@urr_C l).
basic_solver 21.
Qed.

Lemma WF_rst : Wf rstG.
Proof. eapply sub_WF; eauto. apply INIT. apply SUB. Qed.

Lemma WF_SC_rst : wf_sc rstG rst_sc.
Proof. unfold rstG; eapply sub_WF_SC; eauto; apply SUB. Qed.

Lemma coh_sc_rst : coh_sc rstG rst_sc.
Proof. eapply sub_coh_sc; eauto; [eapply SUB| eapply PHCON]. Qed.

Lemma coherence_rst : coherence rstG .
Proof. eapply sub_coherence; eauto; [eapply SUB| eapply PHCON]. Qed.

Lemma acyc_ext_rst : acyc_ext rstG rst_sc.
Proof. eapply sub_acyc_ext; eauto; [eapply SUB| eapply PHCON]. Qed.

Lemma rmw_atomicity_rst : rmw_atomicity rstG.
Proof. eapply sub_rmw_atomicity; eauto; [eapply INIT| eapply SUB| eapply PHCON]. Qed.

(******************************************************************************)
(******************************************************************************)

Lemma sb_total_W : (W ∩₁ (E \₁ I)) × (W ∩₁ (E \₁ I)) ⊆ Gsb^? ∪ Gsb⁻¹.
Proof.
unfolder; ins; desf.
cut (Fsb x y \/ Fsb y x \/ x = y).
- intro; desf; eauto.
  left; right; apply (sub_sb SUB); basic_solver.
  right; apply (sub_sb SUB); basic_solver.
- apply E_E0 in H3.
  apply E_E0 in H1.
  unfold E0 in *; unfolder in *; ins; desf.
  all: try by exfalso; generalize (w_covered_issued TCCOH); basic_solver 4.
  * assert (FE x).
    by apply (dom_l (@wf_sbE Gf)) in H3; unfolder in H3; desf.
    assert (FE y).
    by apply (dom_l (@wf_sbE Gf)) in H1; unfolder in H1; desf.
    assert (~ is_init x).
    by intro; apply H4, (init_issued WF TCCOH); basic_solver.
    assert (~ is_init y).
    by intro; apply H2, (init_issued WF TCCOH); basic_solver.
    assert (X: tid x = tid y).
    apply sb_tid_init in H3.
    apply sb_tid_init in H1.
    desf; congruence.
    apply (@same_thread Gf) in X; eauto.
    unfolder in X; desf; eauto.
  * apply (dom_l (wf_rmwD WF)) in H3; unfolder in H3; type_solver.
  * apply (dom_l (wf_rmwD WF)) in H1; unfolder in H1; type_solver.
  * apply (dom_l (wf_rmwD WF)) in H1; unfolder in H1; type_solver.
Qed.

Lemma IT_new_co: I ∪₁ E ∩₁ W ∩₁ Tid_ thread ≡₁ E ∩₁ W.
Proof.
split.
- arewrite (I  ⊆₁ W ∩₁ E).
  generalize I_in_E (issuedW TCCOH); basic_solver.
  basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto.
  apply E_E0 in H.
  unfold E0 in *.
  unfolder in *; desf; eauto.
  * generalize (w_covered_issued TCCOH); basic_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    left.
    apply (w_covered_issued TCCOH).
    cdes TCCOH.
    unfolder in ICOV; basic_solver 21.
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma CT_F: C ∩₁ F ∪₁ E ∩₁ F ∩₁ Tid_ thread ≡₁ E ∩₁ F.
Proof.
split.
- rewrite C_in_E; basic_solver.
- unfolder; ins; desf.
  destruct (classic (tid x = thread)); eauto.
  apply E_E0 in H.
  unfold E0 in *.
  unfolder in *; desf; eauto.
  * apply (issuedW TCCOH) in H; type_solver.
  * apply (dom_l (@wf_sbE Gf)) in H; unfolder in H; desf.
    apply sb_tid_init in H2; desf.
    apply (init_w WF) in H2; type_solver.
  * apply (dom_l (wf_rmwD WF)) in H; unfolder in H; type_solver.
Qed.

Lemma E_to_I: E ⊆₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘).
Proof.
cut (E ⊆₁ C ∪₁ dom_rel (Fsb^? ⨾ ⦗I⦘)).
- unfolder; ins; desf; eauto.
  specialize (H x H0); desf; eauto.
  right; exists y; splits; eauto.
  right; apply (sub_sb SUB); unfolder; splits; eauto.
  by apply I_in_E.
- rewrite E_E0; unfold E0; unfolder; ins; desf; eauto 10.
  apply (rmw_in_sb WF) in H.
  basic_solver 21.
Qed.

Lemma E_F_AcqRel_in_C: E ∩₁ F ∩₁ Acq/Rel ⊆₁ C.
Proof.
rewrite E_to_I.
rewrite (sub_sb_in SUB).
unfolder; ins; desf.
apply (issuedW TCCOH) in H2; type_solver.
generalize (dom_F_sb_issued TCCOH); basic_solver 21.
Qed.

Lemma E_F_Sc_in_C: E ∩₁ F ∩₁ Sc ⊆₁ C.
Proof.
arewrite (Sc ⊆₁ Acq/Rel) by mode_solver.
apply E_F_AcqRel_in_C.
Qed.

Lemma W_ex_E: GW_ex ∩₁ E ⊆₁ I.
Proof.
rewrite E_to_I, (sub_W_ex_in SUB), ACQEX, (sub_sb_in SUB).
rewrite set_inter_union_r; unionL.
by generalize (W_ex_in_W) (w_covered_issued TCCOH); basic_solver 21.
rewrite crE at 1; relsf; unionL; splits.
basic_solver.
rewrite (issued_in_issuable TCCOH) at 1.
unfold issuable, dom_cond; basic_solver 21.
Qed.

Lemma COMP_ACQ: forall r (IN: (E ∩₁ R ∩₁ Acq) r), exists w, Grf w r.
Proof.
ins.
cdes PHCON.
unfolder in IN; desf.
exploit (Comp r).
- split.
apply (sub_E SUB); basic_solver.
apply (sub_R SUB); basic_solver.
- unfolder; ins ;desf.
cut (E0 x /\ E0 r).
basic_solver 12.
split; apply E_E0; [|done].
hahn_rewrite rfi_union_rfe in x0; unfolder in x0; desf.
eapply rfi_E.
 basic_solver 21.
eapply I_in_E.
eapply rfe_Acq_E.
 basic_solver 21.
Qed.

Lemma COMP_C : C ∩₁ R ⊆₁ codom_rel Grf.
Proof.
unfolder; ins; desf.
cdes PHCON.
exploit (Comp x).
- split; [by apply (coveredE TCCOH)| done].
- unfolder; ins ;desf.
cut (E0 x0 /\ E0 x).
basic_solver 12.
unfold E0; split; [|basic_solver].
generalize (dom_rf_covered WF TCCOH).
basic_solver 12.
Qed.

Lemma COMP_NTID : E ∩₁ NTid_ thread ∩₁ R ⊆₁ codom_rel Grf.
Proof.
unfolder; ins; desf.
cdes PHCON.
exploit (Comp x).
- split.
apply (sub_E SUB); basic_solver.
apply (sub_R SUB); basic_solver.
- unfolder; ins ;desf.
cut (E0 x0 /\ E0 x).
basic_solver 12.
split; apply E_E0; [|done].
hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
eapply rfi_E.
 basic_solver 21.
eapply I_in_E.
eapply rfe_E.
basic_solver 21.
Qed.

Lemma COMP_PPO : dom_rel (Gppo ⨾ ⦗I⦘) ∩₁ R ⊆₁ codom_rel Grf.
Proof.
rewrite (dom_l (wf_ppoE rstWF)).
unfolder; ins; desf.
cdes PHCON.
exploit (Comp x).
- split.
apply (sub_E SUB); basic_solver.
apply (sub_R SUB); basic_solver.
- unfolder; ins ;desf.
cut (E0 x0 /\ E0 x).
basic_solver 12.
split; apply E_E0; [|done].
hahn_rewrite rfi_union_rfe in x1; unfolder in x1; desf.
eapply rfi_E.
 basic_solver 21.
eapply I_in_E.
generalize (dom_rfe_ppo_issued TCCOH).
apply (sub_ppo_in SUB) in H1.
basic_solver 21.
Qed.

Lemma urr_helper: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ Grelease ⨾ ⦗I⦘) ⊆₁ C.
Proof.
rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.
rewrite release_I.
sin_rewrite (cr_helper hb_C).
rewrite !seqA.
sin_rewrite (cr_helper sc_C).
rewrite !seqA.
arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
{ generalize hb_C.
unfolder; ins; desf; splits; eauto 20.
eapply H; eauto.
right; eexists; splits; eauto.
eapply H; eauto. }
basic_solver.
Qed.


Lemma urr_helper_C: 
  dom_rel ((Ghb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ rst_sc^? ⨾ Ghb^? ⨾ (Grelease ⨾ Grf)^? ⨾ ⦗C⦘) ⊆₁ C.
Proof.
rewrite (sub_hb_in SUB), (sub_release_in SUB), (sub_F SUB), (sub_Sc SUB).
rewrite (sub_rf_in SUB).
arewrite (rst_sc ⊆ sc) by unfold rst_sc; basic_solver.

arewrite ((Frelease ⨾ Frf)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ;; (Grelease ⨾ Grf)^?).
{ case_refl _; [basic_solver 12|].
rewrite !seqA.
rewrite rf_C.
sin_rewrite release_I.
basic_solver 12. }


sin_rewrite (cr_helper hb_C).
rewrite !seqA.
sin_rewrite (cr_helper sc_C).
rewrite !seqA.
arewrite ((Fhb ⨾ ⦗FF ∩₁ FSc⦘)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (Ghb ⨾ ⦗FF ∩₁ FSc⦘)^?).
{ generalize hb_C.
unfolder; ins; desf; splits; eauto 20.
eapply H; eauto.
right; eexists; splits; eauto.
eapply H; eauto. }
basic_solver.
Qed.


Lemma release_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Grelease ⊆ Gsb^? ;; ⦗(E \₁ C) ∩₁ (E \₁ I)⦘.
Proof.
rewrite (wf_releaseE rstWF); relsf; unionL; [basic_solver 21|].
arewrite_id ⦗E⦘ at 1; rels.
rewrite release_int; relsf; unionL.
- rewrite !seqA.
arewrite (⦗GW_ex⦘ ⨾ ⦗E⦘ ⊆ ⦗I⦘).
by generalize W_ex_E; basic_solver.
rewrite (sub_release_in SUB).
rewrite release_I.
basic_solver.
- arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗C ∪₁ I⦘) at 1.
unfolder; ins; desf; tauto.
relsf; unionL; [basic_solver 12|].
rewrite (sub_sb_in SUB) at 1.
rewrite (sub_F SUB), (sub_Rel SUB).
unfolder; ins; desf; exfalso.
generalize (dom_sb_covered TCCOH); unfolder; basic_solver 21.
generalize F_Rel_sb_I; unfolder; basic_solver 21.
-
rewrite crE at 1; relsf; unionL; [basic_solver 12|].
arewrite (⦗E⦘ ⊆ ⦗E \₁ (C ∪₁ I)⦘ ∪ ⦗C ∪₁ I⦘) at 1.
unfolder; ins; desf; tauto.

relsf; unionL; [basic_solver 12|].

rewrite (sub_sb_in SUB) at 1.
rewrite (sub_same_loc SUB), (sub_Rel SUB), (sub_W SUB).
unfolder; ins; desf; exfalso.
generalize (dom_sb_covered TCCOH); unfolder; basic_solver 21.
generalize W_Rel_sb_loc_I; unfolder; basic_solver 21.
Qed.


Lemma sw_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Gsw ⊆ Gsb.
Proof.
unfold sw.
sin_rewrite release_de.
rewrite rfi_union_rfe; relsf; unionL.
by arewrite (Grfi ⊆ Gsb); generalize (@sb_trans rstG); basic_solver 21.
case_refl (Gsb ⨾ ⦗F⦘).
- rewrite (dom_r (wf_rfeE rstWF)).
 rewrite (sub_rfe_in SUB) at 1.
rewrite !seqA.
unfolder; ins; desf; exfalso; generalize rfe_Acq_E; basic_solver 12.
- rewrite (dom_r (@wf_sbE rstG)).
 rewrite (sub_rfe_in SUB) at 1.
 rewrite (sub_sb_in SUB) at 2.
rewrite !seqA.
unfolder; ins; desf; exfalso; generalize rfe_sb_F_Acq_E; basic_solver 12.
Qed.

Lemma sb_sw_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Gsb^? ⨾ Gsw ⊆ Gsb.
Proof.
case_refl _; [by apply sw_de|].
rewrite (dom_l (wf_swE rstWF)).
rewrite (dom_l (wf_swD rstWF)).

arewrite (⦗(FF ∪₁ FW) ∩₁ FRel⦘ ⊆ ⦗FF ∩₁ FRel⦘ ∪ ⦗FW ∩₁ FRel⦘) by basic_solver.
relsf; unionL.
-
rewrite (sub_sb_in SUB) at 1.
 arewrite (FRel ⊆₁ FAcq/Rel) by mode_solver.
generalize sb_F_E; unfolder; ins; desf; exfalso.
assert (~ (C x \/ I x)) by tauto.
basic_solver 12.
- 


arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗C ∪₁ I⦘).
by unfolder; ins; desf; tauto.
relsf; unionL.
* generalize sw_de, (@sb_trans rstG); basic_solver 21.
* rewrite (sub_sb_in SUB) at 1.
generalize RELCOV (dom_sb_covered TCCOH); unfolder; ins; desf; exfalso; basic_solver 21.
Qed.

Lemma hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⊆ Gsb.
Proof.
unfold hb.
rewrite path_union.
generalize (@sb_trans rstG); ins; relsf; unionL.
basic_solver 12.
apply ct_ind_right with (P:= fun r => ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ r ⨾ Gsb^?).
- eauto with hahn.
- rewrite !seqA; sin_rewrite sb_sw_de.
generalize (@sb_trans rstG); ins; relsf.
- intros k H1.
arewrite (⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘).
basic_solver.
sin_rewrite H1.
arewrite (Gsb ⊆ Gsb^?) at 1.
sin_rewrite sb_sw_de.
generalize (@sb_trans rstG); ins; relsf.
Qed.

Lemma hb_sc_hb_de : ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ Ghb ⨾ (rst_sc ⨾ Ghb)^? ⊆ Gsb.
Proof.
arewrite (⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ⨾ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘).
basic_solver.
sin_rewrite hb_de.
case_refl _; [basic_solver|].
rewrite (dom_l (wf_scD WF_SC_rst)).
rewrite (dom_l (wf_scE WF_SC_rst)).
rewrite !seqA.
arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⊆ ⦗C⦘).
generalize E_F_Sc_in_C; basic_solver.
rewrite (sub_sb_in SUB) at 1.
generalize (dom_sb_covered TCCOH).
unfolder; ins; desf.
exfalso; eauto 21.
Qed. 

Lemma W_hb_to_I_NTid: 
  dom_rel (⦗W⦘ ⨾ Ghb ⨾  ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof.
rewrite (dom_l (wf_hbE rstWF)) at 1; rewrite !seqA.
arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗E ∩₁ C ∪₁ E ∩₁ I⦘).
by unfolder; ins; desf; tauto.
relsf; unionL; splits; [|generalize (w_covered_issued TCCOH); basic_solver| basic_solver].
rewrite <- !dom_eqv1.
sin_rewrite hb_de.
rewrite (dom_l (@wf_sbE rstG)), !seqA.
rewrite sb_tid_init'; relsf; unionL; splits.
- rewrite <- set_interA, (set_interC W).
  seq_rewrite <- IT_new_co.
  unfold same_tid in *.
  unfolder; ins; desf; congruence.
- unfolder; ins.
  eapply init_issued; unfolder; ins; desf; splits; eauto.
  by apply (sub_E_in SUB).
Qed.

Lemma F_hb_to_I_NTid: 
  dom_rel (⦗F⦘ ⨾ Ghb ⨾  ⦗I ∩₁ NTid_ thread⦘) ⊆₁ C.
Proof.
rewrite (dom_l (wf_hbE rstWF)) at 1; rewrite !seqA.
arewrite (⦗E⦘ ⊆ ⦗(E \₁ C) ∩₁ (E \₁ I)⦘ ∪ ⦗E ∩₁ C ∪₁ E ∩₁ I⦘).
by unfolder; ins; desf; tauto.
relsf; unionL; splits.
2: basic_solver.
2: rewrite (issuedW TCCOH); type_solver.
rewrite <- !dom_eqv1.
sin_rewrite hb_de.
rewrite (dom_l (@wf_sbE rstG)), !seqA.
rewrite sb_tid_init'; relsf; unionL; splits.
- rewrite <- set_interA, (set_interC F).
seq_rewrite <- CT_F.

unfold same_tid in *.
unfolder; ins; desf; congruence.
- 
unfolder; ins; desf.
apply (init_w WF) in H1; type_solver.
Qed.


Lemma W_hb_sc_hb_to_I_NTid: 
  dom_rel (⦗W⦘ ⨾ Ghb ⨾ (rst_sc ⨾ Ghb)^? ;; ⦗I ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof.
rewrite crE; relsf; split.
generalize W_hb_to_I_NTid; basic_solver 21.
rewrite !seqA.
rewrite (dom_l (wf_scD WF_SC_rst)).
rewrite (dom_l (wf_scE WF_SC_rst)).
rewrite !seqA.
arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⊆ ⦗C⦘).
generalize E_F_Sc_in_C; basic_solver.
rewrite (sub_hb_in SUB).
sin_rewrite hb_C.
generalize (w_covered_issued TCCOH); basic_solver 21.
Qed.

Lemma detour_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ I.
Proof.
rewrite (sub_detour_in SUB).
rewrite E_E0; unfold E0.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
  generalize w_covered_issued, dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_r (wf_detourD WF)) at 1; rewrite (issuedW TCCOH) at 1; type_solver.
- arewrite (Fdetour ⊆ Fdetour  ⨾  ⦗set_compl Init⦘).
  { rewrite (dom_r (wf_detourD WF)).
    rewrite (init_w WF).
    unfolder; ins; desf; splits; eauto.
    intro; type_solver. }
  unfolder; ins; desf.
  apply sb_tid_init in H1; desf.
- rewrite (rmw_in_ppo WF).
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable, dom_cond; basic_solver 21.
Qed.

Lemma detour_Acq_E : dom_rel (Gdetour ⨾ ⦗E ∩₁ R ∩₁ Acq⦘) ⊆₁ I.
Proof.
rewrite (sub_detour_in SUB).
rewrite E_E0; unfold E0.
rewrite !set_inter_union_l.
rewrite !id_union; relsf; unionL; splits.
- rewrite (dom_l (wf_detourD WF)), detour_in_sb. 
  generalize w_covered_issued, dom_sb_covered; ie_unfolder; basic_solver 21.
- rewrite (dom_r (wf_detourD WF)) at 1; rewrite (issuedW TCCOH) at 1; type_solver.
- rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable, bob, dom_cond; basic_solver 21.
- rewrite (rmw_in_ppo WF).
  rewrite (issued_in_issuable TCCOH) at 1.
  unfold issuable, dom_cond; basic_solver 21.
Qed.



Lemma TCCOH_rst : tc_coherent rstG rst_sc T.
Proof.
cdes TCCOH.
red; splits.
- rewrite (sub_E_in SUB); apply TCCOH.
- unfold coverable in *; repeat (splits; try apply set_subset_inter_r).
  * rewrite E_E0; unfold E0; basic_solver.
  * rewrite (sub_sb_in SUB); rewrite CC at 1; basic_solver 12.
  * rewrite (sub_rf_in SUB), (sub_W SUB), (sub_R SUB), (sub_F SUB).
    arewrite (rst_sc ⊆ sc) by (unfold rst_sc; basic_solver).
    rewrite CC at 1; basic_solver 21.
- unfold issuable in *; repeat (splits; try apply set_subset_inter_r).
  * rewrite E_E0; unfold E0; basic_solver.
  * rewrite (sub_W SUB); rewrite II at 1; basic_solver 12.
  * rewrite (sub_fwbob_in SUB); rewrite II at 1; basic_solver 12.
  * rewrite (sub_detour_in SUB), (sub_rfe_in SUB), (sub_ppo_in SUB), (sub_bob_in SUB).
    rewrite II at 1; basic_solver 12.
  * rewrite (sub_W_ex_in SUB), (sub_xacq SUB), (sub_sb_in SUB).
    rewrite II at 1; basic_solver 12.
Qed.


Lemma C_E_NTid : C ∪₁ (E ∩₁ NTid_ thread) ≡₁
C ∪₁ (I ∩₁ NTid_ thread) ∪₁ 
(dom_rel (Frmw ⨾ ⦗ NTid_ thread ∩₁ I ⦘) \₁ codom_rel (⦗ set_compl FW_ex⦘ ⨾ Frfi))
.
Proof.
assert (TCCOH1:= TCCOH).
apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
destruct TCCOH1.
rewrite E_E0; unfold E0; split; relsf; unionL; splits.

- basic_solver.
- basic_solver.
- basic_solver.
- 

rewrite sb_tid_init'.
relsf; splits.
basic_solver.
rewrite (dom_l (@wf_sbE Gf)).
revert tc_init; basic_solver 12.


- basic_solver 12.
- basic_solver.
- basic_solver 12.
- unionR right -> right.
apply set_subset_inter_r; splits.
basic_solver.
rewrite (rmw_from_non_init WF).
rewrite (rmw_in_sb WF).
rewrite sb_tid_init'.
basic_solver.
Qed.

Lemma TCCOH_rst_new_T : tc_coherent rstG rst_sc (mkTC (C ∪₁ (E ∩₁ NTid_ thread)) I).
Proof.
assert (TCCOH1:= TCCOH).
apply (tc_coherent_implies_tc_coherent_alt WF WF_SC) in TCCOH1.
destruct TCCOH1.
apply tc_coherent_alt_implies_tc_coherent; constructor; ins.
- rewrite (sub_E_in SUB) at 1; rewrite tc_init; basic_solver.
- unionL; [by rewrite C_in_E|basic_solver].
- rewrite C_E_NTid at 1.


rewrite !id_union; relsf; unionL; splits.
*
  rewrite (sub_sb_in SUB); rewrite tc_sb_C; basic_solver.
* 

rewrite sb_tid_init'.
relsf; splits.
rewrite (dom_l (@wf_sbE rstG)); basic_solver.
rewrite (dom_l (@wf_sbE rstG)); rewrite (sub_E_in SUB) at 1. 
revert tc_init; basic_solver.
* arewrite (dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘) \₁
      codom_rel (⦗set_compl FW_ex⦘ ⨾ Frfi) ⊆₁dom_rel (Frmw ⨾ ⦗NTid_ thread ∩₁ I⦘)).
basic_solver.
rewrite dom_rel_eqv_dom_rel.

rewrite (rmw_in_sb WF).
rewrite (dom_l (@wf_sbE rstG)), !seqA.
rewrite (sub_sb_in SUB) at 1.
generalize (@sb_trans Gf); ins; relsf.


rewrite sb_tid_init'.
relsf; splits.
basic_solver.
rewrite (sub_E_in SUB) at 1. 
revert tc_init; basic_solver.

- rewrite C_E_NTid.
  rewrite !set_inter_union_l.
  unionL; [done| basic_solver| rewrite (dom_l (wf_rmwD WF)); type_solver].

- 

arewrite (⦗E0⦘ ⨾ Frf ⨾ ⦗E0⦘ ⊆ Grf).
rewrite rfi_union_rfe; relsf; splits.
*
rewrite C_E_NTid.
rewrite !id_union; relsf; unionL; splits.

+ rewrite (dom_l (wf_rfiD WF_rst)).

arewrite (Grfi ⊆ Gsb).
rewrite (sub_W SUB), (sub_sb_in SUB).


generalize tc_W_C_in_I tc_sb_C; basic_solver 21.
+
 rewrite (dom_r (wf_rfiD WF_rst)); rewrite tc_I_in_W at 1.
type_solver.
+ rewrite (sub_rfi_in SUB).

(*arewrite (Frfi ⊆ Frfi ∩ Fsb).
rewrite sb_tid_init'.

arewrite (Frmw ⊆ Frmw ∩ Fsb).
generalize (rmw_in_sb WF); basic_solver.

rewrite sb_tid_init' at 3.*)
unfolder; ins; desc.

destruct (classic (FW_ex x)) as [X|X]; cycle 1.

by exfalso; eapply H1; exists x,x; eauto 10.

apply Wex_rfi_rmw_E.
generalize I_in_E;  unfolder; basic_solver 12.


* 
rewrite (dom_r (wf_rfeE WF_rst)), !seqA.
sin_rewrite (dom_rel_helper_in Grfe_E).
basic_solver.
- rewrite (dom_r (wf_scE WF_SC_rst)), (dom_r (wf_scD WF_SC_rst)), !seqA.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ⨾ ⦗C ∪₁ E ∩₁ NTid_ thread⦘ ⊆ ⦗C⦘).
  generalize E_F_Sc_in_C; basic_solver.
  rewrite (sub_sc_in SUB).
  rewrite tc_sc_C; basic_solver.
- apply I_in_E.
- rewrite (sub_fwbob_in SUB), tc_fwbob_I; basic_solver.
- rewrite (sub_detour_in SUB), (sub_rfe_in SUB).
  rewrite (sub_ppo_in SUB), (sub_bob_in SUB).
  rewrite tc_dr_pb_I; basic_solver.
- rewrite (sub_W_ex_in SUB), (sub_sb_in SUB); apply tc_W_ex_sb_I.
Qed.




End RestExec.

