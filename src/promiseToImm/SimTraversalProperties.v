Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

Require Import AuxRel.

Require Import Events Execution.
Require Import imm_s imm_s_hb imm_common.
Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section SimTraversalProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

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

Notation "'R_ex'" := (R_ex G).
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

Lemma sim_trav_step_coherence (C C' : trav_config) (T : sim_trav_step G sc C C')
      (H : tc_coherent G sc C):
  tc_coherent G sc C'.
Proof.
  red in T. destruct T as [thread T].
  destruct T.
  1-4: by eapply trav_step_coherence; eauto; eexists; eauto.
  { eapply trav_step_coherence.
    { eexists. apply TS2. }
    eapply trav_step_coherence; eauto.
    eexists; eauto. }
  { eapply trav_step_coherence.
    { eexists. apply TS2. }
    eapply trav_step_coherence; eauto.
    eexists; eauto. }
  eapply trav_step_coherence.
  { eexists. apply TS3. }
  eapply trav_step_coherence.
  { eexists. apply TS2. }
  eapply trav_step_coherence; eauto.
  eexists; eauto.
Qed.

Lemma sim_trav_steps_coherence (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C')
      (H : tc_coherent G sc C):
  tc_coherent G sc C'.
Proof.
  generalize H. induction T; auto.
    by apply sim_trav_step_coherence.
Qed.

Lemma sim_trav_step_covered_le (C C' : trav_config) (T : sim_trav_step G sc C C') :
  covered C ⊆₁ covered C'.
Proof.
  red in T. destruct T as [thread T].
  destruct T.
  all: basic_solver.
Qed.

Lemma sim_trav_steps_covered_le (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C') :
  covered C ⊆₁ covered C'.
Proof.
  induction T; auto.
  { by apply sim_trav_step_covered_le. }
  etransitivity; eauto.
Qed.

Lemma sim_trav_step_rel_covered (C C' : trav_config) (T : sim_trav_step G sc C C')
      (RELCOV : W ∩₁ Rel ∩₁ issued C ⊆₁ covered C) :
  W ∩₁ Rel ∩₁ issued C' ⊆₁ covered C'.
Proof.
  red in T. destruct T as [thread T].
  destruct T; simpls.
  1,2,4,6: by etransitivity; eauto; basic_solver.
  { etransitivity.
    2: by apply RELCOV.
    basic_solver. }
  { rewrite set_inter_union_r. rewrite RELCOV.
    basic_solver. }
  rewrite set_inter_union_r. rewrite RELCOV.
  basic_solver.
Qed. 

Lemma sim_trav_steps_rel_covered (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C')
      (RELCOV : W ∩₁ Rel ∩₁ issued C ⊆₁ covered C) :
  W ∩₁ Rel ∩₁ issued C' ⊆₁ covered C'.
Proof.
  induction T.
  2: done.
  { eapply sim_trav_step_rel_covered; eauto. }
  apply IHT2. by apply IHT1.
Qed.

Lemma sim_trav_step_rmw_covered (C C' : trav_config) (T : sim_trav_step G sc C C')
      (RMWCOV : forall r w (RMW : rmw r w), covered C r <-> covered C w) :
  forall r w (RMW : rmw r w), covered C' r <-> covered C' w.
Proof.
  ins.
  red in T. destruct T as [thread T].
  apply WF.(wf_rmwD) in RMW.
  apply seq_eqv_l in RMW. destruct RMW as [RR RMW].
  apply seq_eqv_r in RMW. destruct RMW as [RMW WW].
  destruct T; simpls.
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; left. 
    all: type_solver. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { by apply RMWCOV. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { specialize (RMWCOV r w RMW).
    split; intros [HH|HH]; subst; left. 
    all: try type_solver.
    exfalso. apply NRMW. eexists; eauto. }
  { split; intros [[HH|HH]|HH]; subst. 
    { left. left. by apply (RMWCOV r w RMW). }
    { right. eapply WF.(wf_rmwf); eauto. }
    { apply (dom_r WF.(wf_rmwD)) in RMW0. apply seq_eqv_r in RMW0.
      type_solver. }
    { left. left. by apply (RMWCOV r w RMW). }
    { apply (dom_l WF.(wf_rmwD)) in RMW0. apply seq_eqv_l in RMW0.
      type_solver. }
    left. right. eapply wf_rmw_invf; eauto. }
  split; intros [[HH|HH]|HH]; subst. 
  { left. left. by apply (RMWCOV r w RMW). }
  { right. eapply WF.(wf_rmwf); eauto. }
  { apply (dom_r WF.(wf_rmwD)) in RMW0. apply seq_eqv_r in RMW0.
    type_solver. }
  { left. left. by apply (RMWCOV r w RMW). }
  { apply (dom_l WF.(wf_rmwD)) in RMW0. apply seq_eqv_l in RMW0.
    type_solver. }
  left. right. eapply wf_rmw_invf; eauto.
Qed. 

Lemma sim_trav_steps_rmw_covered (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C')
      (RMWCOV : forall r w (RMW : rmw r w), covered C r <-> covered C w) :
  forall r w (RMW : rmw r w), covered C' r <-> covered C' w.
Proof.
  induction T.
  2: done.
  { eapply sim_trav_step_rmw_covered; eauto. }
  apply IHT2. by apply IHT1.
Qed.

End SimTraversalProperties.