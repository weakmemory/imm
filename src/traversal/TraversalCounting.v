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
From hahnExt Require Import HahnExt.
Require Import imm_s_rfppo.
Require Import FinExecution.

Set Implicit Arguments.

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
  Variable WFsc : wf_sc G sc.
  Variable COMP : complete G.
  
  Notation "'E'" := (acts_set G).
  Notation "'lab'" := (lab G).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
  Notation "'rmw'" := (rmw G).
  
Section Helpers.
  Variable findom : list actid.
  (* TODO: this is too strict (fin_exec should be sufficient),
     but since the file seems unused, we'll keep it as is *)
  Hypothesis AFINDOM : forall x (EX : E x), In x findom.

  Definition trav_steps_left (T : trav_config) :=
    countP (E \₁ covered T) findom +
    countP (E ∩₁ W ∩₁ set_compl (issued T)) findom.
  
  Lemma trav_steps_left_decrease (T T' : trav_config)
        (STEP : trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using AFINDOM.
    red in STEP. desc. red in STEP.
    desf.
    { unfold trav_steps_left.
      rewrite ISSEQ.
      assert (countP (E \₁ (covered T)) findom >
              countP (E \₁ (covered T')) findom) as HH.
      2: lia.
      rewrite COVEQ.
      unfold countP.
      assert (E e) as EE by (by apply COV).
      assert (List.In e findom) as LL by (by apply AFINDOM).
      clear AFINDOM.
      induction findom.
      { done. }
      destruct l as [|h l].
      { assert (a = e); subst.
        { inv LL. }
        simpls. desf.
        { exfalso; apply s0. by right. }
        { exfalso; apply s.  by right. }
        exfalso. apply n. by split. }
      destruct LL as [|H]; subst.
      2: { apply IHl in H. clear IHl.
           simpls. desf; simpls; try lia.
           all: try
             by (exfalso; apply s0; left; apply NNPP;
                 intros HH; apply n; split; auto; apply s0).
           all:
             by (exfalso; apply s; left; apply NNPP;
                 intros HH; apply n; split; auto; apply s). }
      clear IHl.
      assert (exists l', l' = h :: l) as [l' HH] by eauto.
      rewrite <- HH. clear h l HH.
      assert (length (filterP (E \₁ (covered T ∪₁ eq e)) l') <=
              length (filterP (E \₁ (covered T)) l')).
      { eapply countP_mori; auto.
        basic_solver. }
      simpls. desf; simpls.
      { exfalso. apply s0. by right. }
      { lia. }
      { exfalso. apply s. by right. }
      exfalso. apply n. by split. }

    unfold trav_steps_left.
    rewrite COVEQ.
    assert (countP (E ∩₁ W ∩₁ set_compl (issued T )) findom >
            countP (E ∩₁ W ∩₁ set_compl (issued T')) findom) as HH.
    2: lia.
    rewrite ISSEQ.
    unfold countP.
    assert (E e) as EE.
    { apply ISS. }
    assert (List.In e findom) as LL.
    { by apply AFINDOM. }
    assert (W e) as WE.
    { apply ISS. }
    clear AFINDOM.
    induction findom.
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
    assert (length (filterP (E ∩₁ W ∩₁ set_compl (issued T ∪₁ eq e)) l') <=
            length (filterP (E ∩₁ W ∩₁ set_compl (issued T)) l')).
    2: lia.
    eapply countP_mori; auto.
    basic_solver.
  Qed.

  Lemma trav_steps_left_decrease_sim (T T' : trav_config)
        (STEP : sim_trav_step G sc T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using AFINDOM.
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
  Proof using AFINDOM.
    unfold trav_steps_left in *.
    assert (countP (E \₁ (covered T)) findom = 0) as HH by lia.
    clear NULL.
    unfold countP in *.
    apply length_zero_iff_nil in HH.
    intros x EX.
    destruct (classic (covered T x)) as [|NN]; auto.
    exfalso. 
    assert (In x (filterP (E \₁ (covered T)) findom)) as UU.
    2: { rewrite HH in UU. inv UU. }
    apply in_filterP_iff. do 2 (split; auto).
  Qed.

  Lemma trav_steps_left_ncov_nnull (T : trav_config) e
        (EE : E e) (NCOV : ~ covered T e):
    trav_steps_left T <> 0.
  Proof using AFINDOM.
    destruct (classic (trav_steps_left T = 0)) as [EQ|NEQ]; auto.
    exfalso. apply NCOV. apply trav_steps_left_null_cov; auto.
  Qed.

  Lemma trav_steps_left_nnull_ncov (T : trav_config) (TCCOH : tc_coherent G sc T)
        (NNULL : trav_steps_left T > 0):
    exists e, E e /\ ~ covered T e.
  Proof using.
    unfold trav_steps_left in *.
    assert (countP (E \₁ (covered T)) findom > 0 \/
            countP (E ∩₁ W ∩₁ set_compl (issued T)) findom > 0) as YY by lia.
    assert (countP (E \₁ (covered T)) findom > 0) as HH.
    { destruct YY as [|YY]; auto.
      assert (countP (E \₁  (covered T)) findom >=
              countP (E ∩₁ W ∩₁ set_compl (issued T)) findom).
      2: lia.
      apply countP_mori; auto.
      intros x [[EX WX] NN].
      split; auto. intros COV.
      apply NN. eapply w_covered_issued; eauto. by split. }
    clear YY.
    unfold countP in HH.
    assert (exists h l, filterP (E \₁ (covered T)) findom = h :: l) as YY.
    { destruct (filterP (E \₁ (covered T)) findom); eauto.
      inv HH. }
    desc. exists h.
    assert (In h (filterP (E \₁ (covered T)) findom)) as GG.
    { rewrite YY. red. by left. }
    apply in_filterP_iff in GG. apply GG.
  Qed.

  Lemma trav_steps_left_decrease_sim_trans (T T' : trav_config)
        (STEPS : (sim_trav_step G sc)⁺ T T') :
    trav_steps_left T > trav_steps_left T'.
  Proof using AFINDOM.
    induction STEPS.
    { by apply trav_steps_left_decrease_sim. }
    eapply Nat.lt_trans; eauto.
  Qed.
End Helpers.

  Lemma sim_traversal_helper T
        (FINDOM : set_finite E)
        (IMMCON : imm_consistent G sc)
        (TCCOH : tc_coherent G sc T)
        (RELCOV :  W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w) :
    exists T', (sim_trav_step G sc)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF WFsc COMP.
    cdes FINDOM.
    assert
      (exists T' : trav_config, (sim_trav_step G sc)＊ T T' /\
                                trav_steps_left findom T' = 0).
    2: { desc. eexists. splits; eauto. eapply trav_steps_left_null_cov; eauto. }
    assert (exists n, n = trav_steps_left findom T) as [n NN] by eauto.
    generalize dependent T. generalize dependent n.
    set (P n :=
           forall T,
             tc_coherent G sc T ->
             W ∩₁ Rel ∩₁ issued T ⊆₁ covered T ->
             (forall r w, rmw r w -> covered T r <-> covered T w) ->
             n = trav_steps_left findom T ->
             exists T', (sim_trav_step G sc)＊ T T' /\ trav_steps_left findom T' = 0).
    assert (forall n, P n) as YY.
    2: by apply YY.
    apply nat_ind_lt. unfold P. 
    ins.
    destruct (classic (trav_steps_left findom T = 0)) as [EQ|NEQ].
    { eexists. splits; eauto. apply rt_refl. }
    assert (trav_steps_left findom T > 0) as HH by lia.
    eapply trav_steps_left_nnull_ncov in HH; auto.
    desc. eapply exists_next in HH0; eauto. desc.
    eapply exists_trav_step in HH1; eauto.
    2: { apply fsupp_ar_rf_ppo_loc_fin; auto.
         eapply set_finite_mori; [| by apply FINDOM].
         red. basic_solver. }
    desc.
    apply exists_sim_trav_step in HH1; eauto. desc.
    clear T'. subst.
    specialize (H (trav_steps_left findom T'')).
    edestruct H as [T' [II OO]].
    { by apply trav_steps_left_decrease_sim. }
    { eapply sim_trav_step_coherence; eauto. }
    { eapply sim_trav_step_rel_covered; eauto. }
    { eapply sim_trav_step_rmw_covered; eauto. }
    { done. }
    exists T'. splits; auto. apply rt_begin.
    right. eexists. eauto.
  Qed.

  Lemma sim_traversal (FINDOM : set_finite E) (IMMCON : imm_consistent G sc) :
    exists T, (sim_trav_step G sc)＊ (init_trav G) T /\ (G.(acts_set) ⊆₁ covered T).
  Proof using WF WFsc COMP.
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
        (FINDOM : set_finite E)
        (IMMCON : imm_consistent G sc)
        (TCCOH : tc_coherent G sc T) (NCOV : NTid_ thread ∩₁ (acts_set G) ⊆₁ covered T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        (RMWCOV : forall r w : actid, rmw r w -> covered T r <-> covered T w) : 
    exists T', (isim_trav_step G sc thread)＊ T T' /\ ((acts_set G) ⊆₁ covered T').
  Proof using WF WFsc COMP.
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
