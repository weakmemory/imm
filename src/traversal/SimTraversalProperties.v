From hahn Require Import Hahn.
Require Import Events Execution.
Require Import imm_s.
Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.
Require Import AuxDef.

Set Implicit Arguments.

Section SimTraversalProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := (acts G).
  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
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
Proof using.
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
Proof using.
  generalize H. induction T; auto.
    by apply sim_trav_step_coherence.
Qed.

Lemma sim_trav_step_issued_le (C C' : trav_config) (T : sim_trav_step G sc C C') :
  issued C ⊆₁ issued C'.
Proof using.
  red in T. destruct T as [thread T].
  destruct T.
  all: basic_solver.
Qed.

Lemma sim_trav_steps_issued_le (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C') :
  issued C ⊆₁ issued C'.
Proof using.
  induction T; auto.
  { by apply sim_trav_step_issued_le. }
  etransitivity; eauto.
Qed.

Lemma sim_trav_step_covered_le (C C' : trav_config) (T : sim_trav_step G sc C C') :
  covered C ⊆₁ covered C'.
Proof using.
  red in T. destruct T as [thread T].
  destruct T.
  all: basic_solver.
Qed.

Lemma sim_trav_steps_covered_le (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C') :
  covered C ⊆₁ covered C'.
Proof using.
  induction T; auto.
  { by apply sim_trav_step_covered_le. }
  etransitivity; eauto.
Qed.

Lemma sim_trav_step_rel_covered (C C' : trav_config) (T : sim_trav_step G sc C C')
      (RELCOV : W ∩₁ Rel ∩₁ issued C ⊆₁ covered C) :
  W ∩₁ Rel ∩₁ issued C' ⊆₁ covered C'.
Proof using.
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
Proof using.
  induction T.
  2: done.
  { eapply sim_trav_step_rel_covered; eauto. }
  apply IHT2. by apply IHT1.
Qed.

Lemma sim_trav_step_rmw_covered (C C' : trav_config) (T : sim_trav_step G sc C C')
      (RMWCOV : forall r w (RMW : rmw r w), covered C r <-> covered C w) :
  forall r w (RMW : rmw r w), covered C' r <-> covered C' w.
Proof using WF.
  ins.
  red in T. destruct T as [thread T].
  apply (wf_rmwD WF) in RMW.
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
    { right. eapply (wf_rmwf WF); eauto. }
    { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
      type_solver. }
    { left. left. by apply (RMWCOV r w RMW). }
    { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
      type_solver. }
    left. right. eapply wf_rmw_invf; eauto. }
  split; intros [[HH|HH]|HH]; subst. 
  { left. left. by apply (RMWCOV r w RMW). }
  { right. eapply (wf_rmwf WF); eauto. }
  { apply (dom_r (wf_rmwD WF)) in RMW0. apply seq_eqv_r in RMW0.
    type_solver. }
  { left. left. by apply (RMWCOV r w RMW). }
  { apply (dom_l (wf_rmwD WF)) in RMW0. apply seq_eqv_l in RMW0.
    type_solver. }
  left. right. eapply wf_rmw_invf; eauto.
Qed. 

Lemma sim_trav_steps_rmw_covered (C C' : trav_config) (T : (sim_trav_step G sc)＊ C C')
      (RMWCOV : forall r w (RMW : rmw r w), covered C r <-> covered C w) :
  forall r w (RMW : rmw r w), covered C' r <-> covered C' w.
Proof using WF.
  induction T.
  2: done.
  { eapply sim_trav_step_rmw_covered; eauto. }
  apply IHT2. by apply IHT1.
Qed.

Lemma sim_trav_step_in_trav_steps : sim_trav_step G sc ⊆ (trav_step G sc)⁺.
Proof using.
  intros C C' [tid TT].
  inv TT.
  1-4: by apply t_step; eexists; eauto.
  1,2: by eapply t_trans; apply t_step; eexists; eauto.
  eapply t_trans.
  2: by apply t_step; eexists; eauto.
  eapply t_trans; apply t_step; eexists; eauto.
Qed.

Lemma isim_trav_step_new_e_tid thread (C C' : trav_config)
      (T : isim_trav_step G sc thread C C') :
  covered C' ∪₁ issued C' ≡₁
  covered C ∪₁ issued C ∪₁ (covered C' ∪₁ issued C') ∩₁ Tid_ thread.
Proof using WF.
  inv T; simpls.
  all: split; [|basic_solver].
  all: unionL; eauto with hahn.
  all: unionR right.
  1-7,9: basic_solver.
  all: arewrite (tid r = tid w); [|basic_solver].
  all: eapply wf_rmwt; eauto.
Qed.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).



Lemma isim_trav_step_new_e_tid_alt thread TC TC' 
      (ITV : isim_trav_step G sc thread TC TC') : 
  covered TC' ∪₁ issued TC' ≡₁ 
    (covered TC ∪₁ issued TC) ∩₁ NTid_ thread ∪₁ (covered TC' ∪₁ issued TC') ∩₁ Tid_ thread.
Proof using WF. 
  assert (sim_trav_step G sc TC TC') as ST by (eexists; eauto).
  rewrite isim_trav_step_new_e_tid at 1; eauto.
  split; [|basic_solver].
  rewrite set_subset_union_l. splits.
  2: basic_solver.
  rewrite <- sim_trav_step_covered_le with (C':=TC'); eauto.
  rewrite <- sim_trav_step_issued_le with (C':=TC'); eauto.
  apply ntid_tid_set_inter.
Qed.

Lemma isim_trav_step_new_covered_tid thread TC TC' 
      (ITV : isim_trav_step G sc thread TC TC') : 
  covered TC' ≡₁ 
    covered TC ∩₁ NTid_ thread ∪₁ covered TC' ∩₁ Tid_ thread.
Proof using WF. 
  assert (covered TC ⊆₁ covered TC ∩₁ NTid_ thread ∪₁ covered TC ∩₁ Tid_ thread) as BB.
  { apply ntid_tid_set_inter. }
  assert (sim_trav_step G sc TC TC') as ST by (eexists; eauto).
  split.
  2: { rewrite sim_trav_step_covered_le with (C':=TC'); eauto.
       basic_solver. }
  inv ITV; simpls; unionL.
  all: try (rewrite BB at 1; basic_solver 10).
  all: try basic_solver 10.
  all: try (apply (wf_rmwt WF) in RMW; rewrite RMW).
  all: basic_solver 10.
Qed.

Lemma isim_trav_step_new_issued_tid thread TC TC' 
      (ITV : isim_trav_step G sc thread TC TC') : 
  issued TC' ≡₁ 
    issued TC ∩₁ NTid_ thread ∪₁ issued TC' ∩₁ Tid_ thread.
Proof using WF. 
  assert (issued TC ⊆₁ issued TC ∩₁ NTid_ thread ∪₁ issued TC ∩₁ Tid_ thread) as BB.
  { apply ntid_tid_set_inter. }
  assert (sim_trav_step G sc TC TC') as ST by (eexists; eauto).
  split.
  2: { rewrite sim_trav_step_issued_le with (C':=TC'); eauto.
       basic_solver. }
  inv ITV; simpls; unionL.
  all: try (rewrite BB at 1; basic_solver 10).
  1,2: basic_solver 10.
  apply (wf_rmwt WF) in RMW. rewrite RMW.
  basic_solver 10.
Qed.

End SimTraversalProperties.
