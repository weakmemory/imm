Require Import Classical Peano_dec.
Require Import Setoid.

From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_common_more.

Require Import TraversalConfig.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TCCOH_ALT.

 Variable G : execution.
 Variable sc : relation actid.

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rf'" := G.(rf).
  Notation "'co'" := G.(co).
  Notation "'coe'" := G.(coe).
  Notation "'fr'" := G.(fr).

  Notation "'eco'" := G.(eco).

  Notation "'bob'" := G.(bob).
  Notation "'fwbob'" := G.(fwbob).
  Notation "'ppo'" := G.(ppo).
  Notation "'fre'" := G.(fre).
  Notation "'rfi'" := G.(rfi).
  Notation "'rfe'" := G.(rfe).
  Notation "'deps'" := G.(deps).
  Notation "'detour'" := G.(detour).
  Notation "'release'" := G.(release).
  Notation "'sw'" := G.(sw).
  Notation "'hb'" := G.(hb).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Implicit Type WF : Wf G.
Implicit Type WF_SC : wf_sc G sc.

  Lemma dom_rel_to_cond {A} r (s t : A -> Prop) :
    dom_rel (r ⨾ ⦗t⦘) ⊆₁ s -> t ⊆₁ dom_cond r s.
  Proof.
    unfold dom_cond; unfolder.
    intro H; ins; desf; eapply H; eauto.
  Qed.

  Lemma dom_cond_to_rel {A} r (s t : A -> Prop) :
    t ⊆₁ dom_cond r s -> dom_rel (r ⨾ ⦗t⦘) ⊆₁ s.
  Proof.
    unfold dom_cond; unfolder.
    intro H; ins; desf; eapply H; eauto.
  Qed.

Record tc_coherent_alt T :=
  { tc_init : Init ∩₁ E ⊆₁ covered T ;
    tc_C_in_E : covered T ⊆₁ E ;
    tc_sb_C : dom_rel ( sb ⨾ ⦗covered T⦘) ⊆₁ covered T ;
    tc_W_C_in_I : covered T ∩₁ W ⊆₁ issued T ;
    tc_rf_C : dom_rel ( rf ⨾ ⦗covered T⦘) ⊆₁ issued T ;
    tc_sc_C : dom_rel ( sc ⨾ ⦗covered T⦘) ⊆₁ covered T ;
    tc_I_in_E : issued T ⊆₁ E ;
    tc_I_in_W : issued T ⊆₁ W ;
    tc_fwbob_I : dom_rel ( fwbob ⨾ ⦗issued T⦘) ⊆₁ covered T ;
    tc_dr_pb_I : dom_rel ( (detour ∪ rfe) ⨾ (ppo ∪ bob) ⨾ ⦗issued T⦘) ⊆₁ issued T ;
    tc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T ;
  }.



Lemma tc_coherent_alt_implies_tc_coherent T: 
  tc_coherent_alt T  -> tc_coherent G sc T.
Proof.
intro H; destruct H.
red; splits; eauto.
- unfold coverable.
  repeat (splits; try apply set_subset_inter_r); ins.
  by eapply dom_rel_to_cond.
  arewrite (covered T ⊆₁ covered T ∩₁ E).
  revert tc_C_in_E0; basic_solver.
  arewrite (E ⊆₁ R ∪₁ W ∪₁ F).
  unfolder; intro a; forward (apply (lab_rwf lab a)); tauto.
  rewrite !set_inter_union_r; unionL.
  * unionR left -> right.
    repeat (splits; try apply set_subset_inter_r); ins.
    basic_solver.
    eapply dom_rel_to_cond.
    revert tc_rf_C0; basic_solver 21.
  * unionR left -> left.
    repeat (splits; try apply set_subset_inter_r); ins.
    basic_solver.
  * unionR right.
    repeat (splits; try apply set_subset_inter_r); ins.
    basic_solver.
    eapply dom_rel_to_cond.
    revert tc_sc_C0; basic_solver 21.
- unfold issuable.
  repeat (splits; try apply set_subset_inter_r); ins.
  by eapply dom_rel_to_cond.
  by eapply dom_rel_to_cond; rewrite !seqA.
  by eapply dom_rel_to_cond; rewrite !seqA.
Qed.

Lemma tc_coherent_implies_tc_coherent_alt WF WF_SC T: 
  tc_coherent G sc T  -> tc_coherent_alt T.
Proof.
intro H; red in H; desf.
unfold coverable, issuable in *.
apply set_subset_inter_r in CC; desf.
apply set_subset_inter_r in CC; desf.
apply set_subset_inter_r in II; desf.
apply set_subset_inter_r in II; desf.
apply set_subset_inter_r in II; desf.
apply set_subset_inter_r in II; desf.
constructor.
- done.
- done.
- by apply dom_cond_to_rel.
- rewrite CC0.
  type_solver.
- rewrite CC0, !id_union; relsf; unionL; splits.
  rewrite (dom_r (wf_rfD WF)); type_solver.
  apply dom_cond_to_rel; basic_solver.
  rewrite (dom_r (wf_rfD WF)); type_solver.
- rewrite CC0 at 1; rewrite !id_union; relsf; unionL; splits.
  rewrite (dom_r (wf_scD WF_SC)); type_solver.
  rewrite (dom_r (wf_scD WF_SC)); type_solver.
  apply dom_cond_to_rel; basic_solver.
- done.
- done.
- by apply dom_cond_to_rel.
- rewrite <- seqA; apply dom_cond_to_rel; basic_solver.
- by rewrite <- seqA; apply dom_cond_to_rel.
Qed.


End TCCOH_ALT.