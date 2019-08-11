From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import TView View Time Event Cell Thread Memory Configuration.

Require Import Events.
Require Import Execution.
Require Import imm_s.
Require Import imm_s_hb.
Require Import imm_common.

Require Import PArith.
Require Import Event_imm_promise.
Require Import CombRelations.
Require Import CombRelationsMore.
Require Import TraversalConfig.
Require Import MaxValue.
Require Import ViewRelHelpers.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ViewRel.
Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := G.(msg_rel).
Notation "'urr'" := (urr G sc).
Notation "'release'" := G.(release).
Notation "'t_cur'" := (t_cur G sc).
Notation "'t_acq'" := (t_acq G sc).
Notation "'t_rel'" := (t_rel G sc).
Notation "'rfe'" := G.(rfe).
Notation "'rfi'" := G.(rfi).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Definition sim_msg f_to b rel :=
  forall l, max_value f_to 
              (fun a => msg_rel sc l a b \/ Loc_ l b /\ a = b) 
              (LocFun.find l rel.(View.rlx)).

Definition sim_mem_helper f_to b from v rel :=
  ⟪ VAL: Some v = val lab b ⟫ /\
  ⟪ FROM: Time.lt from (f_to b) \/ 
    is_init b /\ from = Time.bot /\ (f_to b) = Time.bot ⟫ /\ 
  ⟪ SIMMSG: sim_msg f_to b rel ⟫.

Definition sim_rel C f_to rel i :=
  forall l' l, max_value f_to 
    (t_rel i l l' C ∪₁
     if Loc.eq_dec l l'
     then W_ l' ∩₁ Tid_ i ∩₁ C
     else ∅)
    (LocFun.find l (LocFun.find l' rel).(View.rlx)).

Definition sim_cur C f_to cur i :=
  forall l,
    max_value f_to (t_cur i l C) 
    (LocFun.find l cur.(View.rlx)).

Definition sim_acq C f_to acq i :=
  forall l,
    max_value f_to (t_acq i l C) 
    (LocFun.find l acq.(View.rlx)).

Definition sim_tview C f_to tview i :=
  ⟪ CUR: sim_cur C f_to tview.(TView.cur) i ⟫ /\
  ⟪ ACQ: sim_acq C f_to tview.(TView.acq) i ⟫ /\
  ⟪ REL: sim_rel C f_to tview.(TView.rel) i ⟫.

Lemma sim_tview_read_step
      f_to f_from
      w r locr valr xrmw ordr C tview thread rel mem
      (COH : coherence G)
      (Wf_sc : wf_sc G sc)
      (SIMTVIEW : sim_tview C f_to tview thread)
      (RRLX : Rlx r)
      (NC : ~ C r)
      (SBC : forall y, C y /\ tid y = tid r -> sb y r)
      (PRC : doma (sb ⨾ ⦗ eq r ⦘) C)
      (RF : rf w r)
      (TID : tid r = thread)
      (RPARAMS : lab r = Aload xrmw ordr locr valr)
      (GET : Memory.get locr (f_to w) mem =
             Some (f_from w, Message.mk valr rel))
      (HELPER : sim_mem_helper f_to w (f_from w) valr rel.(View.unwrap)) :
  sim_tview
    (C ∪₁ eq r) f_to
    (TView.read_tview tview locr (f_to w) rel (rmod ordr))
    thread.
Proof.
  assert (R r) as RR by type_solver.
  assert (W w) as WW by (apply (wf_rfD WF) in RF; revert RF; basic_solver).
  assert (Loc_ locr w) as WLOC.
  { assert (loc lab w = loc lab r) as H.
    { eapply loceq_rf; eauto. }
    by rewrite H; unfold loc; rewrite RPARAMS. }
  assert (~ is_init r) as RNINIT.
  { intros INIT. apply (init_w WF) in INIT. type_solver. }
  assert (E r) as RACTS by (apply (wf_rfE WF) in RF; revert RF; basic_solver).
  assert (loc lab r = Some locr) as RLOC.
  { by unfold loc; rewrite RPARAMS. }

  assert (~ F r) as NF.
  { intros H. type_solver. }
  
  assert (Ordering.le Ordering.relaxed (rmod ordr) = Rlx r) as ORDRLX.
    by unfold is_rlx, mode_le, mod; rewrite RPARAMS; destruct ordr; simpls.
  assert (Ordering.le Ordering.acqrel (rmod ordr) = Acq r) as ORDACQ.
    by unfold is_acq, mode_le, mod; rewrite RPARAMS; destruct ordr; simpls.

  assert 
    (forall l (P : actid -> bool),
     dom_rel
     ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗P⦘ ⨾ ⦗eq r⦘) ≡₁
     if P r
     then
       (fun a => msg_rel sc l a w \/ loc lab w = Some l /\ a = w)
     else ∅) as MSGALT.
  { ins; desf; [|basic_solver 21].
    split; [|basic_solver 21].
    unfolder; ins; desc.
    assert (z = w); subst.
      by eapply (wf_rff WF); eauto.
    basic_solver 21. }

  assert (forall l, W_ l ∩₁ eq r ≡₁ ∅) as DR'.
    by type_solver 21.

  assert (forall S l, W_ l ∩₁ eq r ∪₁ S ≡₁ S) as DR.
   by intros; rewrite DR'; apply set_union_empty_l.

  assert (forall l l',
   t_rel (tid r) l l' (C ∪₁ eq r) ∪₁
   (if LocSet.Facts.eq_dec l l'
    then W ∩₁ Loc_ l' ∩₁ Tid_ (tid r) ∩₁ (C ∪₁ eq r)
    else ∅) ≡₁
   t_rel (tid r) l l' C ∪₁
   (if LocSet.Facts.eq_dec l l'
    then W ∩₁ Loc_ l' ∩₁ Tid_ (tid r) ∩₁ C
    else ∅)) as RELALT.
  { ins; rewrite t_rel_union_eqv; auto.
    by desf; apply set_equiv_union; [done| type_solver 21].
    by revert PRC; basic_solver. }

  red in SIMTVIEW; desf.
  red in CUR; desf.
  red in ACQ; desf.
  red in REL; desf.
  cdes HELPER; clear FROM.
  red in SIMMSG; desf.
  red; splits; intros l; simpls;
    unfold LocFun.find, TimeMap.join in *;
    (try rewrite ORDRLX); try (rewrite ORDACQ).
  { eapply max_value_same_set.
    2: apply t_cur_urr_union_eqv; auto; revert PRC; basic_solver.
    rewrite Time.join_assoc.
    unfold CombRelations.t_cur, CombRelations.c_cur in CUR.
    eapply max_value_join; eauto.
    eapply max_value_join; eauto.
    { eapply max_value_same_set; [|by apply DR].
      eapply max_value_same_set; [|by eapply dom_rel_r; eauto].
      unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      destruct (LocSet.Facts.eq_dec l locr); simpls; subst.
      all: unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      { by apply max_value_singleton; rewrite Loc.eq_dec_eq. }
      rewrite Loc.eq_dec_neq; auto.
      apply max_value_empty; intros x HH; desf. }
    specialize (MSGALT l (Acq)).
    eapply max_value_same_set; [|by apply MSGALT].
    destruct (Acq r) eqn: RACQ; unfold View.rlx; simpls.
    by apply max_value_empty; intros x HH; desf. }
  { eapply max_value_same_set.
    2: apply t_acq_urr_union_eqv; auto; revert PRC; basic_solver.
    rewrite Time.join_assoc.
    unfold CombRelations.t_acq, CombRelations.c_acq in ACQ.
    eapply max_value_join; eauto.
    eapply max_value_join; eauto.
    { eapply max_value_same_set; [|by apply DR].
      eapply max_value_same_set; [|by eapply (dom_rel_r WF l); eauto].
      destruct (LocSet.Facts.eq_dec l locr); simpls; subst;
        unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      { by rewrite Loc.eq_dec_eq; apply max_value_singleton. }
      rewrite Loc.eq_dec_neq; auto.
      apply max_value_empty; intros x HH; desf. }
    apply set_equiv_union; [reflexivity|].
    specialize (MSGALT l (fun x => true)).
    simpl in MSGALT. rewrite <- MSGALT.
    arewrite (⦗fun _ : actid => true⦘ ≡ ⦗fun _ : actid => True⦘).
    { split; intros x y H; red; red in H; desf. }
    by rewrite seq_id_l. }
  intros l'.
  by eapply max_value_same_set; [apply REL| apply RELALT].
Qed.

Lemma sim_tview_write_step f_to f_from
      w locw valw xmw ordw C tview thread rel mem sc_view
      (COH : coherence G)
      (Wf_sc : wf_sc G sc)
      (CINE : C ⊆₁ E)
      (CCLOS : doma (sb ⨾ ⦗C⦘) C)
      (SIMTVIEW : sim_tview C f_to tview thread)
      (NC : ~ C w)
      (SBC : forall y, C y /\ tid y = tid w -> sb y w)
      (PRC : doma (sb ⨾ ⦗ eq w ⦘) C)
      (TID : tid w = thread)
      (NINIT : ~ is_init w)
      (WACTS : E w)
      (WPARAMS : lab w = Astore xmw ordw locw valw)
      (GET : Memory.get locw (f_to w) mem =
             Some (f_from w, Message.mk valw rel))
      (HELPER : sim_mem_helper f_to w (f_from w) valw rel.(View.unwrap))
 : sim_tview
    (C ∪₁ eq w) f_to
    (TView.write_tview
       tview sc_view locw (f_to w) (wmod ordw))
    thread.
Proof.
  assert (W w) as WW.
  { by unfold is_w; rewrite WPARAMS. }
  assert (loc lab w = Some locw) as LOC.
  { by unfold loc; rewrite WPARAMS. }
  assert (~ F w) as NF.
  { intros H; type_solver. }

  assert (forall S l, S ∪₁ dom_rel (⦗Loc_ l⦘ ⨾ rf ⨾ ⦗eq w⦘) ≡₁ S) as DR1.
    by ins; rewrite (dom_r (wf_rfD WF)); type_solver.

  assert (forall S O l,
             S ∪₁
             dom_rel ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗O⦘ ⨾ ⦗eq w⦘) ≡₁ S)
    as DR2.
    by ins; rewrite (dom_r (wf_rfD WF)); type_solver.

  assert (forall S l,
             S ∪₁
             dom_rel ((msg_rel sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗eq w⦘) ≡₁ S)
    as DR5.
  { ins.
    arewrite (⦗eq w⦘ ≡ ⦗ fun _ => True ⦘ ⨾ ⦗eq w⦘).
    2: by apply DR2.
    by rewrite seq_id_l. }
  
  assert (forall l,
             W_ l ∩₁ eq w ≡₁
             if LocSet.Facts.eq_dec l locw then eq w else ∅) as DR3.
    by basic_solver.

  assert (Ordering.le Ordering.acqrel (wmod ordw) = Rel w)
    as ORDREL.
  { unfold is_rel, mode_le, mod; rewrite WPARAMS; destruct ordw; simpls. }
  
  red in SIMTVIEW; desf.
  red in CUR; desf.
  red in ACQ; desf.
  red in REL; desf.
  cdes HELPER; clear FROM.
  red in SIMMSG; desf.
  red; splits; intros l; simpls;
    unfold LocFun.find, TimeMap.join in *; try (rewrite ORDREL).
  { eapply max_value_same_set.
    2: apply t_cur_urr_union_eqv; auto; revert PRC; basic_solver.
    unfold CombRelations.t_cur, CombRelations.c_cur in CUR.
    eapply max_value_join; eauto.
    eapply max_value_same_set; [|eapply DR2].
    eapply max_value_same_set; [|eapply DR1].
    eapply max_value_same_set; [|eapply DR3].
    unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
    destruct (LocSet.Facts.eq_dec l locw); simpls; subst.
    { by apply max_value_singleton. }
    apply max_value_empty; intros x HH; desf. }
  { eapply max_value_same_set.
    2: apply t_acq_urr_union_eqv; auto; revert PRC; basic_solver.
    unfold CombRelations.t_acq, CombRelations.c_acq in ACQ.
    eapply max_value_join; eauto.
    eapply max_value_same_set; [|eapply DR5].
    eapply max_value_same_set; [|eapply DR1].
    eapply max_value_same_set; [|eapply DR3].
    unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
    destruct (LocSet.Facts.eq_dec l locw); simpls; subst.
    { by apply max_value_singleton. }
    apply max_value_empty; intros x HH; desf. }
  { intros l0; eapply max_value_same_set; [|eapply t_rel_w_union_eqv; eauto]; cycle 2.
    3: by apply urr_refl.
{
ins.
rewrite ((urr_rel_n_f_alt_union_eqv WF) sc Wf_sc l1 l' C w (tid w)); eauto.
basic_solver 42.
revert PRC; basic_solver 42.
}
    unfold TimeMap.join, TimeMap.singleton,View.singleton_ur,
    LocFun.add, LocFun.find, LocFun.init.
    destruct (LocSet.Facts.eq_dec l locw); simpls; subst.
    destruct (Rel w); simpls; eapply max_value_join; eauto.
    all: unfold LocFun.find, LocFun.init, TimeMap.singleton, LocFun.add.
    all: destruct (Loc.eq_dec l0 locw).
    1,3: by apply max_value_singleton; auto.
    all: by apply max_value_empty; auto. }
Qed.

Lemma sim_tview_f_issued f_to f_to' T tview thread
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ : forall e (ISS: issued T e), f_to' e = f_to e)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread):
  sim_tview (covered T) f_to' tview thread.
Proof.
  cdes SIMTVIEW.
  red; splits; red; ins; eapply max_value_new_f.
  1, 3, 5: by eauto.
  { intros x H. apply t_cur_covered in H; auto. }
  { intros x H. apply t_acq_covered in H; auto. }
  intros x [H|H].
  { apply t_rel_covered in H; auto. }
  destruct (classic (l = l')) as [LEQ|LNEQ].
  2: by rewrite Loc.eq_dec_neq in H; desf.
  apply ISSEQ.
  subst; rewrite Loc.eq_dec_eq in H.
  generalize (w_covered_issued TCCOH).
  revert H; basic_solver 21.
Qed.

Lemma sim_sc_fence_step
      T f_to
      f ordf ordr ordw tview thread sc_view
      (TCCOH : tc_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (IMMCON : imm_consistent G sc)
      (NEXT : next G (covered T) f)
      (TID : tid f = thread)
      (FPARAMS : lab f = Afence ordf)
      (SAME_MOD : fmod ordf ordr ordw)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread)
      (SC_VIEW :
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)) :
  forall l : Loc.t,
    max_value f_to (S_tm G l (covered T ∪₁ eq f))
              (LocFun.find
                 l (TView.write_fence_sc
                      (TView.read_fence_tview tview ordr) 
                      sc_view ordw)).
Proof.
  cdes IMMCON.
  intros l. specialize (SC_VIEW l).
  destruct (classic (is_sc lab f)) as [FISSC|FISNOSC].
  all: unfold TView.write_fence_sc.
  { assert (Ordering.le Ordering.seqcst ordw /\
            Ordering.le Ordering.acqrel ordr) as [LLW LLR].
    { red in SAME_MOD.
      unfold is_sc, mod in FISSC. rewrite FPARAMS in FISSC.
      desf; desf. }
    unfold TView.read_fence_tview.
    rewrite LLW, LLR; simpls.
    unfold LocFun.find, TimeMap.join.
    eapply max_value_same_set.
    2: by eapply s_tm_cov_sc_fence; eauto.
    eapply max_value_join.
    3: by eauto.
    { done. }
    apply SIMTVIEW. }
  assert (covered T ⊆₁ covered T ∪₁ eq f) as CCC.
  { basic_solver. }
  eapply max_value_same_set.
  2: apply s_tm_n_f_steps.
  3: by apply CCC.
  2: by apply TCCOH.
  2: by intros r COVEQ COVT [FF FF']; destruct COVEQ; subst.
  assert (~ Ordering.le Ordering.seqcst ordw) as LL; [|by desf].
  intros H. subst.
  assert (ordw = Ordering.seqcst) as SS.
  { destruct ordw; desf. }
  unfold is_sc, mod in FISNOSC.
  red in SAME_MOD; simpls;
    rewrite FPARAMS in *; simpls.
  destruct ordf; desf.
Qed.

Lemma sim_tview_fence_step T
      f_to
      f ordf ordr ordw tview thread sc_view
      (TCCOH : tc_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (IMMCON : imm_consistent G sc)
      (COV : coverable G sc T f)
      (NCOV : ~ covered T f)
      (TID : tid f = thread)
      (SAME_MOD : fmod ordf ordr ordw)
      (FPARAMS : lab f = Afence ordf)
      (SIMTVIEW : sim_tview (covered T) f_to tview thread)
      (SC_VIEW :
         ~ (E∩₁F∩₁Sc ⊆₁ (covered T)) ->
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)) :
  sim_tview (covered T ∪₁ eq f) f_to
    (TView.write_fence_tview
       (TView.read_fence_tview tview ordr) 
       sc_view ordw) (tid f).
Proof.
  cdes IMMCON.
  assert (is_f lab f) as FENCE.
  { by unfold is_f; rewrite FPARAMS. }
  assert (E f) as EF.
  { apply COV. }
  red; splits.
  all: unfold TView.read_fence_tview, TView.write_fence_tview,
    TView.write_fence_sc; simpls.
  all: red; simpls.
  { intros l.
    eapply max_value_same_set.
    2: apply t_cur_fence_step; eauto.
    red in SAME_MOD.
    unfold is_sc, is_acq, mod; rewrite FPARAMS in *.
    destruct ordf; simpls; destruct SAME_MOD; subst.
    all: desf; simpls.
    1-5: by apply SIMTVIEW.
    unfold set_union; unfold LocFun.find.
    eapply max_value_join.
    { apply SC_VIEW.
      intros H. apply NCOV. apply H; split; [split|]; auto.
      unfold is_sc, mod. by rewrite FPARAMS. }
    { by apply SIMTVIEW. }
    basic_solver. }
  { intros l.
    eapply max_value_same_set.
    2: by apply t_acq_fence_step.
    red in SAME_MOD.
    unfold is_sc, is_acq, mod; rewrite FPARAMS in *.
    destruct ordf; simpls; destruct SAME_MOD; subst.
    all: desf; simpls.
    1-5: unfold LocFun.find, TimeMap.join, TimeMap.bot; simpls.
    1-5: eapply max_value_join; eauto; [|apply max_value_empty; intros x H; desf].
    1-5: by apply SIMTVIEW.
    rewrite TimeMap.join_comm, TimeMap.join_assoc, TimeMap.join_comm.
    eapply max_value_join; eauto.
    { rewrite TimeMap.le_join_r; [by apply SIMTVIEW|].
      apply TimeMap.le_PreOrder. }
    apply SC_VIEW.
    intros H. apply NCOV. apply H; split; [split|]; auto.
    unfold is_sc, mod. by rewrite FPARAMS. }
  intros l' l.
  eapply max_value_same_set; [| by eapply t_rel_fence_step].
  red in SAME_MOD.
  unfold is_sc, is_acq, is_acqrel, is_rel, mod; rewrite FPARAMS in *.
  destruct ordf; simpls; destruct SAME_MOD; subst.
  all: cdes SIMTVIEW; red in REL.
  all: desf; simpls.
  unfold LocFun.find, TimeMap.join, TimeMap.bot; simpls.
  eapply max_value_join; eauto.
  apply SC_VIEW.
  intros H. apply NCOV. apply H; split; [split|]; auto.
  unfold is_sc, mod. by rewrite FPARAMS.
Qed.

Lemma sim_tview_other_thread_step f_to
      C C' tview thread
      (CINIT : is_init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a)
      (SIMTVIEW : sim_tview C f_to tview thread) :
  sim_tview C' f_to tview thread.
Proof.
  red; splits; red; splits; ins.
  all: eapply max_value_same_set.
  all: try by (apply SIMTVIEW).
  { apply t_cur_other_thread; eauto. }
  { apply t_acq_other_thread; eauto. }
  apply t_rel_if_other_thread; eauto.
Qed.

End ViewRel.
