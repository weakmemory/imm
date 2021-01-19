Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_s.
Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.
Require Import SimTraversalProperties.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition countP (f: actid -> Prop) l :=
  length (filterP f l).

Add Parametric Morphism : countP with signature
    set_subset ==> eq ==> le as countP_mori.
Proof using.
  ins. unfold countP.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  1,3: lia.
  exfalso. apply n. by apply H.
Qed.

Add Parametric Morphism : countP with signature
    set_equiv ==> eq ==> eq as countP_more.
Proof using.
  ins. unfold countP.
  erewrite filterP_set_equiv; eauto.
Qed.

Section TraversalCounting.
  Variable G : execution.
  Variable sc : relation actid.
  Variable WF : Wf G.
  
  Notation "'E'" := (acts_set G).
  Notation "'lab'" := (lab G).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
  Notation "'rmw'" := (rmw G).

  Definition trav_steps_left (T : trav_config) :=
    countP (set_compl (covered T)) (acts G) +
    countP (W ∩₁ set_compl (issued T)) (acts G).
  
  Lemma trav_steps_left_decrease (T T' : trav_config)
        (STEP : trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using.
    red in STEP. desc. red in STEP.
    desf.
    { unfold trav_steps_left.
      rewrite ISSEQ.
      assert (countP (set_compl (covered T)) (acts G) >
              countP (set_compl (covered T')) (acts G)) as HH.
      2: lia.
      rewrite COVEQ.
      unfold countP.
      assert (List.In e (acts G)) as LL.
      { apply COV. }
      induction (acts G).
      { done. }
      destruct l as [|h l].
      { assert (a = e); subst.
        { inv LL. }
        simpls. desf.
        exfalso. apply s0. by right. }
      destruct LL as [|H]; subst.
      2: { apply IHl in H. clear IHl.
           simpls. desf; simpls; try lia.
           all: try by (exfalso; apply s0; left; apply NNPP).
             by exfalso; apply s; left; apply NNPP. }
      clear IHl.
      assert (exists l', l' = h :: l) as [l' HH] by eauto.
      rewrite <- HH. clear h l HH.
      simpls. desf; simpls.
      { exfalso. apply s0. by right. }
      assert (length (filterP (set_compl (covered T ∪₁ eq e)) l') <=
              length (filterP (set_compl (covered T)) l')).
      2: lia.
      eapply countP_mori; auto.
      basic_solver. }
    unfold trav_steps_left.
    rewrite COVEQ.
    assert (countP (W ∩₁ set_compl (issued T )) (acts G) >
            countP (W ∩₁ set_compl (issued T')) (acts G)) as HH.
    2: lia.
    rewrite ISSEQ.
    unfold countP.
    assert (List.In e (acts G)) as LL.
    { apply ISS. }
    assert (W e) as WE.
    { apply ISS. }
    induction (acts G).
    { done. }
    destruct l as [|h l].
    { assert (a = e); subst.
      { inv LL. }
      simpls. desf.
      { exfalso. apply s0. by right. }
      all: by exfalso; apply n; split. }
    destruct LL as [|H]; subst.
    2: { apply IHl in H. clear IHl.
         simpls. desf; simpls; try lia.
         1-2: by exfalso; apply n; destruct s0 as [H1 H2];
           split; auto; intros HH; apply H2; left.
         all: by exfalso; apply n; destruct s as [H1 H2];
           split; auto; intros HH; apply H2; left. }
    clear IHl.
    assert (exists l', l' = h :: l) as [l' HH] by eauto.
    rewrite <- HH. clear h l HH.
    simpls. desf; simpls.
    { exfalso. apply s0. by right. }
    2: { exfalso. apply s. by right. }
    2: { exfalso. apply n. by split. }
    assert (length (filterP (W ∩₁ set_compl (issued T ∪₁ eq e)) l') <=
            length (filterP (W ∩₁ set_compl (issued T)) l')).
    2: lia.
    eapply countP_mori; auto.
    basic_solver.
  Qed.

  Lemma trav_steps_left_decrease_sim (T T' : trav_config)
        (STEP : sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using.
    red in STEP. desc.
    destruct STEP.
    1-4: by apply trav_steps_left_decrease; red; eauto.
    { eapply Nat.lt_trans.
      all: apply trav_steps_left_decrease; red; eauto. }
    { eapply Nat.lt_trans.
      all: apply trav_steps_left_decrease; red; eauto. }
    eapply Nat.lt_trans.
    eapply Nat.lt_trans.
    all: apply trav_steps_left_decrease; red; eauto.
  Qed.
  
  Lemma trav_steps_left_null_cov (T : trav_config)
        (NULL : trav_steps_left T = 0) :
    E ⊆₁ covered T.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (set_compl (covered T)) (acts G) = 0) as HH by lia.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (covered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (set_compl (covered T)) (acts G))) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. by split.
  Qed.

  Lemma trav_steps_left_ncov_nnull (T : trav_config) e
        (EE : E e) (NCOV : ~ covered T e):
    trav_steps_left T <> 0.
  Proof using.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto.
    exfalso. apply NCOV. apply trav_steps_left_null_cov; auto.
  Qed.

  Lemma trav_steps_left_nnull_ncov (T : trav_config) (TCCOH : tc_coherent G sc T)
        (NNULL : trav_steps_left T > 0):
    exists e, E e /\ ~ covered T e.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (set_compl (covered T)) (acts G) > 0 \/
            countP (W ∩₁ set_compl (issued T)) (acts G) > 0) as YY by lia.
    assert (countP (set_compl (covered T)) (acts G) > 0) as HH.
    { destruct YY as [|YY]; auto.
      assert (countP (set_compl (covered T)) (acts G) >=
              countP (W ∩₁ set_compl (issued T)) (acts G)).
      2: lia.
      apply countP_mori; auto.
      intros x [WX NN] COV.
      apply NN. eapply w_covered_issued; eauto. by split. }
    clear YY.
    unfold countP in HH.
    assert (exists h l, filterP (set_compl (covered T)) (acts G) = h :: l) as YY.
    { destruct (filterP (set_compl (covered T)) (acts G)); eauto.
      inv HH. }
    desc. exists h.
    assert (In h (filterP (set_compl (covered T)) (acts G))) as GG.
    { rewrite YY. red. by left. }
    apply in_filterP_iff in GG. simpls.
  Qed.

  Lemma trav_steps_left_decrease_sim_trans (T T' : trav_config)
        (STEPS : (sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using.
    induction STEPS.
    { by apply trav_steps_left_decrease_sim. }
    eapply Nat.lt_trans; eauto.
  Qed.

  Theorem nat_ind_lt (P : nat -> Prop)
          (HPi : forall n, (forall m, m < n -> P m) -> P n) :
    forall n, P n.
  Proof using.
    set (Q n := forall m, m <= n -> P m).
    assert (forall n, Q n) as HH.
    2: { ins. apply (HH n). lia. }
    ins. induction n.
    { unfold Q. ins. inv H. apply HPi. ins. inv H0. }
    unfold Q in *. ins.
    apply Compare_dec.le_lt_eq_dec in H.
    destruct H as [Hl | Heq].
    { unfold lt in Hl. apply le_S_n in Hl. by apply IHn. }
    rewrite Heq. apply HPi. ins.
    apply le_S_n in H. by apply IHn.
  Qed.

  Lemma sim_traversal_helper T
        (IMMCON : imm_consistent G sc)
        (TCCOH : tc_coherent G sc T)
        (RELCOV :  W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w) :
    exists T', (sim_trav_step G sc)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF.
    assert
      (exists T' : trav_config, (sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    2: { desc. eexists. splits; eauto. by apply trav_steps_left_null_cov. }
    assert (exists n, n = trav_steps_left T) as [n NN] by eauto.
    generalize dependent T. generalize dependent n.
    set (P n :=
           forall T,
             tc_coherent G sc T ->
             W ∩₁ Rel ∩₁ issued T ⊆₁ covered T ->
             (forall r w, rmw r w -> covered T r <-> covered T w) ->
             n = trav_steps_left T ->
             exists T', (sim_trav_step G sc)＊ T T' /\ trav_steps_left T' = 0).
    assert (forall n, P n) as YY.
    2: by apply YY.
    apply nat_ind_lt. unfold P. 
    ins.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ].
    { eexists. splits; eauto. apply rt_refl. }
    assert (trav_steps_left T > 0) as HH by lia.
    eapply trav_steps_left_nnull_ncov in HH; auto.
    desc. eapply exists_next in HH0; eauto. desc.
    eapply exists_trav_step in HH1; eauto.
    desc.
    apply exists_sim_trav_step in HH1; eauto. desc.
    clear T'. subst.
    specialize (H (trav_steps_left T'')).
    edestruct H as [T' [II OO]].
    { by apply trav_steps_left_decrease_sim. }
    { eapply sim_trav_step_coherence; eauto. }
    { eapply sim_trav_step_rel_covered; eauto. }
    { eapply sim_trav_step_rmw_covered; eauto. }
    { done. }
    exists T'. splits; auto. apply rt_begin.
    right. eexists. eauto.
  Qed.

  Lemma sim_traversal (IMMCON : imm_consistent G sc) :
    exists T, (sim_trav_step G sc)＊ (init_trav G) T /\ ((acts_set G) ⊆₁ covered T).
  Proof using WF.
    apply sim_traversal_helper; auto.
    { by apply init_trav_coherent. }
    { unfold init_trav. simpls. basic_solver. }
    ins. split; intros [HH AA].
    { apply (init_w WF) in HH.
      apply (dom_l (wf_rmwD WF)) in RMW. apply seq_eqv_l in RMW.
      type_solver. }
    apply (rmw_in_sb WF) in RMW. apply no_sb_to_init in RMW.
    apply seq_eqv_r in RMW. desf.
  Qed.

  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
  Notation "'Tid_' t"  := (fun x => tid x =  t) (at level 1).

  Lemma sim_step_cov_full_thread T T' thread thread'
        (TCCOH : tc_coherent G sc T)
        (TS : isim_trav_step G sc thread' T T')
        (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T) :
    thread' = thread.
  Proof using.
    destruct (classic (thread' = thread)) as [|NEQ]; [by subst|].
    exfalso.
    apply sim_trav_step_to_step in TS; auto. desf.
    red in TS. desf.
    { apply NEXT. apply NCOV. split; eauto. apply COV. }
    apply NISS. eapply w_covered_issued; eauto.
    split; auto.
    { apply ISS. }
    apply NCOV. split; auto. apply ISS.
  Qed.

  Lemma sim_step_cov_full_traversal T thread
        (IMMCON : imm_consistent G sc)
        (TCCOH : tc_coherent G sc T) (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w : actid, rmw r w -> covered T r <-> covered T w) : 
    exists T', (isim_trav_step G sc thread)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF.
    edestruct sim_traversal_helper as [T']; eauto.
    desc. exists T'. splits; auto.
    clear H0.
    induction H.
    2: ins; apply rt_refl.
    { ins. apply rt_step. destruct H as [thread' H].
      assert (thread' = thread); [|by subst].
      eapply sim_step_cov_full_thread; eauto. }
    ins. 
    set (NCOV' := NCOV).
    apply IHclos_refl_trans1 in NCOV'; auto.
    eapply rt_trans; eauto.
    eapply IHclos_refl_trans2.
    { eapply sim_trav_steps_coherence; eauto. }
    { etransitivity; eauto.
      eapply sim_trav_steps_covered_le; eauto. }
    { eapply sim_trav_steps_rel_covered; eauto. }
    eapply sim_trav_steps_rmw_covered; eauto.
  Qed.
End TraversalCounting.
