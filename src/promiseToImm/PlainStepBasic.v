From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Configuration TView View Time Event Cell Thread Memory.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_common.

Require Import PArith.
Require Import CombRelations.
Require Import CombRelationsMore.

Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.

Require Import MaxValue.
Require Import ViewRel.
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimulationPlainStepAux.
Require Import SimulationRelAux.
Require Import MemoryAux.
Require Import SimState.

Set Implicit Arguments.

(* It's a version of Configuration.step which doesn't require
   consistency of the new configuration. *)
Inductive plain_step :
  forall (e:option Event.t) (tid:Ident.t)
         (c1 c2:Configuration.t), Prop :=
| plain_step_intro
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3)):
    plain_step (ThreadEvent.get_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.

Lemma pair_app :
  forall (A B : Prop), A -> (A -> A /\ B) -> A /\ B.
Proof. ins. intuition. Qed.

Section PlainStepBasic.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Definition msg_preserved memory memory' :=
  forall loc ts from msg (INMEM : Memory.get loc ts memory = Some (from, msg)),
    exists from', Memory.get loc ts memory' = Some (from', msg).

Definition msg_preserved_refl memory : msg_preserved memory memory.
Proof. red. ins. eauto. Qed.

Definition msg_preserved_add memory memory' loc from to val released
           (ADD : Memory.add memory loc from to val released memory') :
  msg_preserved memory memory'.
Proof. red. ins. exists from0. eapply memory_add_le; eauto. Qed.

Definition msg_preserved_split memory memory'
           loc ts1 ts2 ts3 val2 val3 released2 release3
           (SPLIT : Memory.split
                      memory loc ts1 ts2 ts3
                      val2 val3 released2 release3 memory'):
  msg_preserved memory memory'.
Proof.
  red. ins.
  erewrite Memory.split_o; eauto.
  edestruct Memory.split_get0 as [HH BB]; eauto.
  destruct (loc_ts_eq_dec (loc0, ts) (loc, ts2)) as [EQ|NEQ].
  { simpls. desf. rewrite HH in INMEM. desf. }
  simpls.
  destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)) as [EQ|NNEQ].
  { simpls. desf. rewrite BB in INMEM. inv INMEM. eauto. }
  eauto.
Qed.

Lemma full_simrel_step thread PC PC' T T' label f_to f_from
      (COVE  : covered T' ⊆₁ E)
      (ISSE  : issued  T' ⊆₁ E)
      (COVIN : covered T ⊆₁ covered T')
      (ISSIN : issued T ⊆₁ issued T')
      (NINCOV : covered T' \₁ covered T ⊆₁ Tid_ thread)
      (NINISS : issued  T' \₁ issued  T ⊆₁ Tid_ thread)
      (PCSTEP : plain_step label thread PC PC')
      (CLOSED_PRES :
         closedness_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (MSG_PRES :
         msg_preserved PC.(Configuration.memory) PC'.(Configuration.memory))
      (TPEQ : forall thread,
          IdentMap.In thread PC.(Configuration.threads) <->
          IdentMap.In thread PC'.(Configuration.threads))
      (SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to f_from sim_normal)
      (SIMREL : simrel G sc PC T f_to f_from) :
  simrel G sc PC' T' f_to f_from.
Proof.
  red. splits; auto.
  { apply SIMREL_THREAD. }
  cdes SIMREL.
  intros thread' TP'.
  destruct (Ident.eq_dec thread thread') as [|NEQ]; subst.
  { apply SIMREL_THREAD. }
  assert (IdentMap.In thread' PC.(Configuration.threads)) as TP.
  { by apply TPEQ. }
  specialize (THREADS thread' TP).
  cdes THREADS.
  assert (IdentMap.find thread' (Configuration.threads PC') =
          Some (existT _ (PromiseLTS.thread_lts thread') state,
                local)) as TID.
  { destruct PCSTEP. simpls. rewrite IdentMap.gso; auto. }
  assert
  (forall a : actid, tid a = thread' -> covered T' a -> covered T a) as PP.
  { intros a TT YY.
    destruct (classic (covered T a)) as [GG|GG]; [done|].
    exfalso.
    assert (tid a = thread) as RR; [|by subst].
    by apply NINCOV; split. }
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  red; splits; simpls.
  rewrite TID.
  exists state; exists local; splits; auto.
  2: { red. ins.
       edestruct SIM_PROM as [w H]; eauto.
       des. exists w; splits; auto. }
  5: { eapply sim_state_other_thread_step; eauto; desf. }
  4: { by red; splits; ins; apply CLOSED_PRES; apply MEM_CLOSE. }
  3: { destruct T as [C I]. destruct T' as [C' I'].
       eapply sim_tview_other_thread_step.
       2: by apply COVIN.
       all: eauto.
       etransitivity; [apply TCCOH|]. done. }
  { clear TNNULL0 TNNULL.
    ins. destruct (classic (thread'0 = thread)) as [|TNEQ']; subst.
    { apply or_comm. cdes SIMREL_THREAD.
      rewrite LLH0 in TID'. inv TID'. clear TID'.
      eapply PROM_DISJOINT0; eauto. }
    assert (IdentMap.find thread'0 (Configuration.threads PC) = Some (langst', local'))
      as TT.
    { destruct PCSTEP. simpls. rewrite IdentMap.gso in TID'; auto. }
    eapply PROM_DISJOINT; eauto. }
  red. ins. unnw.
  edestruct SIM_MEM0 as [rel]; eauto.
  simpls; desc.
  exists rel; splits; auto.
  intros BTID.
  assert (~ covered T' b <-> ~ covered T b) as CCB.
  { split; intros CC1 CC2.
      by apply COVIN in CC2.
      assert (tid b = thread) as TT.
      2: by subst; desf.
        by apply NINCOV; split. }
  assert (issued T' b <-> issued T b) as IIB.
  { split; auto.
    intros II.
    destruct (classic (issued T b)) as [|NN]; [done|].
    assert (tid b = thread) as TT.
    2: by subst; desf.
      by apply NINISS; split. }
  rewrite CCB.
  edestruct SIM_MEM as [rel']; eauto.
  { by apply IIB. }
  simpls; desc.
  intros CC.
  destruct H2; auto.
  assert (rel' = rel); [|subst; split; vauto].
  { cdes COMMON0. eapply PROM_IN_MEM0 in H; eauto.
    rewrite INMEM in H. inv H. }
  destruct H0 as [p_rel H0]; desc.
  eexists; split; eauto.
  desf.
  { left; splits; auto.
    intros [y HH]. apply NINRMW.
    exists y. apply seq_eqv_l in HH; destruct HH as [ISSY HH]. 
    apply seq_eqv_l; split; auto.
    destruct (classic (issued T y)) as [|NISS]; [done|exfalso].
    destruct (classic (tid y = thread)) as [|TNEQ]; subst.
    2: by apply TNEQ; apply NINISS; split.
    assert ((rfe ⨾ rmw) y b) as RFERMW.
    2: { apply NISS.
         apply IIB in ISSB. apply TCCOH in ISSB.
         apply ISSB.
         exists b; apply seq_eqv_r; split; auto.
         destruct RFERMW as [oo [RFE RMW]].
         apply (dom_l WF.(wf_rfeD)) in RFE.
         apply seq_eqv_l in RFE. destruct RFE as [WY RFE].
         apply seq_eqv_l. split; auto.
         apply ct_ct. exists oo. split; apply ct_step.
         { by apply rfe_in_ar. }
         apply ppo_in_ar. by apply rmw_in_ppo. }
    hahn_rewrite rfi_union_rfe in HH. hahn_rewrite seq_union_l in HH.
    destruct HH as [HH|]; [exfalso|done].
    assert (W y) as WY.
    { cdes COMMON0. by apply TCCOH0. }
    assert (~ is_init y) as NIN.
    { intros DD. apply NISS. eapply w_covered_issued; eauto.
      split; auto. apply TCCOH.
      split; auto. }
    assert (sb y b) as SBYB.
    { edestruct HH as [z [RFI RMW]].
      eapply (@sb_trans G); [by apply WF.(rfi_in_sbloc'); eauto|].
        by apply WF.(rmw_in_sb). }
    edestruct (sb_tid_init SBYB); desf. }
  right. exists p; splits; auto.
  assert (issued T' p) as ISSP'.
  { apply ISSIN. apply ISSP. }
  assert (loc lab p = Some l) as LOCP.
  { simpls. erewrite wf_rfrmwl; eauto. }
  assert (exists p_v', val lab p = Some p_v') as [p_v' VALP].
  { apply WF.(wf_rfrmwD) in INRMW.
    unfold val, is_w in *. desf.
    all: eexists; eauto. }
  eapply MSG_PRES in P_INMEM. desc.
  edestruct (SIM_MEM0 l) as [p_rel''].
  { cdes COMMON0. apply TCCOH0. apply ISSP'. }
  all: eauto; simpls.
  desc.
  rewrite P_INMEM in INMEM1. inv INMEM1.
  eexists; eexists; splits; eauto.
Qed.

Lemma max_event_cur PC T f_to f_from l e thread foo local smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (NEXT : next G (covered T) e)
      (TID_E : tid e = thread)
      (LOC : loc lab e = Some l)
      (TID: IdentMap.find thread PC.(Configuration.threads) = Some (foo, local)):
  exists p_max,
    ⟪ NEQ : p_max <> e ⟫ /\
    ⟪ CCUR : urr G sc l p_max e ⟫ /\
    ⟪ LB : Time.le
      (View.rlx (TView.cur (Local.tview local)) l)
      (f_to p_max) ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  red in SIM_TVIEW; desf.
  red in CUR; desf.
  specialize (CUR l); red in CUR; desc.
  
  assert (E e) as EE.
  { apply NEXT. }
  assert (~ is_init e) as NINE.
  { intros HH. apply NEXT. by apply TCCOH. }

  destruct MAX as [[MAX MAX'] | MAX].
  { unfold LocFun.find in MAX'.
    rewrite MAX'; ins.
    exists (InitEvent l); splits; [ | | by apply Time.bot_spec].
    { intros H; subst; simpls. }
    apply hb_in_urr.
    apply seq_eqv_l; split; red; [|right].
    { by unfold is_w, loc; rewrite WF.(wf_init_lab). }
    apply sb_in_hb.
    apply init_ninit_sb; auto.
    apply WF.(wf_init). eexists; eauto. }
  desf.
  exists a_max. apply and_assoc; split; auto.
  red in INam; red in INam.
  destruct INam as [y CCUR].
  red in CCUR; hahn_rewrite <- seqA in CCUR.
  apply seq_eqv_r in CCUR; destruct CCUR as [CCUR Y'].
  apply seq_eqv_r in CCUR; destruct CCUR as [CCUR Y].
  assert (hb y e) as HBYE.
  { apply sb_in_hb.
    assert (E y) as EY.
    { eapply (@coveredE G) in Y'; eauto. }
    destruct Y as [Y | Y].
    2: by apply init_ninit_sb.
    destruct (same_thread G e y) as [[ZZ|ZZ]|ZZ]; subst; auto.
    { by apply NEXT in Y'. }
    exfalso.
    assert (covered T e) as Z.
    { apply TCCOH in Y'.
      apply Y'. eexists; apply seq_eqv_r; split; eauto. }
      by apply NEXT in Z. }
  assert ((urr G sc l ⨾ hb) a_max e) as UH.
  { exists y; split; auto. }
  splits.
  { intros H; subst; eapply urr_hb_irr; eauto.
    all: apply CON. }
  apply urr_hb.
  destruct UH as [z [UH HH]].
  eexists; split; eauto.
Qed.

End PlainStepBasic.
