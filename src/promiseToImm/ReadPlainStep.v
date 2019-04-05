From hahn Require Import Hahn.
From promising Require Import Basic DenseOrder
     TView View Time Event Cell Thread Language Memory Configuration.
Require Import AuxRel.
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
Require Import Prog.
Require Import ProgToExecution.
Require Import SimulationPlainStepAux.
Require Import SimulationRelAux.

Require Import PlainStepBasic.
Require Import ReadPlainStepHelper.

Require Import SimStateHelper.
Require Import Promise ProgToExecution.
Require Import Arith.

Set Implicit Arguments.

Section ReadPlainStep.

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

Lemma read_step PC T f_to f_from thread r smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid r = thread)
      (NEXT : next G (covered T) r) (COV : coverable G sc T r)
      (TYPE : R r)
      (NRMW : ~ dom_rel rmw r):
  let T' := (mkTC (covered T ∪₁ eq r) (issued T)) in
  exists PC',
    ⟪ PCSTEP : plain_step None thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to f_from smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to f_from ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  
  assert (sc_per_loc G) as SC_PER_LOC.
  { by apply coherence_sc_per_loc; cdes CON. }

  assert (~ covered T r) as RNCOV.
  { apply NEXT. }
  
  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E r) as RACT.
  { apply NEXT. }
  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  assert (Rlx r) as RRLX.
  { apply ALLRLX. by split. }

  assert (exists locr, loc lab r = Some locr) as [locr RLOC].
  { unfold loc. desf; eauto. type_solver. }
  assert (exists valr, val lab r = Some valr) as [valr RVAL].
  { unfold val. desf; eauto. type_solver. }
  assert (exists xrmw, rmwmod lab r = Some xrmw) as [xrmw RXRMW].
  { unfold rmwmod. desf; eauto. all: type_solver. }
  
  assert (lab r = Aload xrmw (Events.mod lab r) locr valr) as PARAMS.
  { unfold loc, val, Events.mod, rmwmod in *. desf. }

  assert (exists w, rf w r) as [w RF].
  { by cdes CON; eapply Comp; split. }

  assert (issued T w) as WISS.
  { destruct COV as [_ [[COV|[_ COV]]|COV]].
    1,3: type_solver.
    apply COV.
    eexists; apply seq_eqv_r; split; eauto. }

  assert (loc lab w = Some locr) as WPLOC.
  { assert (loc lab w = loc lab r) as HH.
    { by apply (wf_rfl WF). }
      by rewrite HH. }
  assert (val lab w = Some valr) as WPVAL.
  { assert (val lab w = val lab r) as HH.
    { by apply wf_rfv. }
      by rewrite HH. }

  assert (W w) as WPWRITE.
  { apply (wf_rfD WF) in RF. apply seq_eqv_l in RF; desf. }
  assert (E w) as WPACT.
  { apply (wf_rfE WF) in RF. apply seq_eqv_l in RF; desf. }

  cdes SIM_MEM.
  edestruct SIM_MEM0 as [rel DOM'].
  2: by apply WISS.
  all: eauto.
  desc.

  assert (Event_imm_promise.same_g_events lab (r :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.read locr valr (Event_imm_promise.rmod (Events.mod lab r))) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *.
    destruct ev; desf; vauto. }

  set (pe := ThreadEvent.read locr (f_to w) valr rel (Event_imm_promise.rmod (Events.mod lab r))).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.rmod (Events.mod lab r))) as RLX_ORDR.
  { unfold is_rlx, mode_le in *.
    destruct (Events.mod lab r); simpls. }
  
  assert (forall y : actid, covered T y /\ tid y = tid r -> sb y r) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G r y) as [[ST|ST]|ST]; subst; auto.
    { apply TCCOH in COVY. apply COVY. }
    { done. }
    assert (covered T r) as CC.
    2: by apply NEXT in CC.
    apply TCCOH in COVY. apply COVY.
    eexists; apply seq_eqv_r; eauto. }
  
  eexists.
  apply and_assoc. apply pair_app.
  { split.
    { set (pe' := None).
      assert (pe' = ThreadEvent.get_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_read.
      econstructor; eauto.
      assert
        (Time.le (View.rlx (TView.cur (Local.tview local)) locr) (f_to w))
        as PP.
      2: constructor; auto.
      2: by cdes PLN_RLX_EQ; rewrite EQ_CUR.
      edestruct (max_event_cur) as [a_max]; eauto; desc.
      assert (E a_max) as EA.
      { apply (wf_urrE WF) in CCUR.
        revert CCUR; unfold seq; unfolder; ins; desf.
        apply CON. }
      assert (issued T a_max) as AISS.
      { assert (A: (urr G sc locr ⨾ ⦗coverable G sc T⦘) a_max r).
        by basic_solver.
        apply (urr_coverable) in A; try done.
        revert A; unfold seq; unfolder; ins; desf. }
      
      destruct (classic (a_max = w)) as [AWEQ|AWNEQ]; [by desf|].
      edestruct (@wf_co_total G WF (Some locr) a_max) as [AWCO|AWCO].
      3: apply AWNEQ.
      2: basic_solver.
      apply set_interA; split; auto.
      hahn_rewrite (@wf_urrD G sc locr) in CCUR.
      revert CCUR; clear; basic_solver 12.
      { etransitivity; eauto.
        cdes FCOH.
        apply Time.le_lteq; left. eapply f_to_co_mon; eauto. }
      exfalso.
      eapply transp_rf_co_urr_irr; eauto.
      1-3: by apply CON.
      exists w; split.
      { right; red; apply RF. }
      exists a_max; split; eauto. }
    edestruct (@read_step_helper G WF sc CON); eauto.
    { done. }
    desc. unnw.
    red; splits; red; splits; simpls; eauto.
    { intros. apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH]; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { subst. exfalso. apply NRMW. eexists; eauto. }
      { erewrite RMWCOV; eauto. }
      type_solver. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { eapply tau_steps_rmw_is_xacq; eauto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      eapply PROM_DISJOINT; eauto. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply full_simrel_step.
  13: by apply SIMREL.
  11: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  all: simpls; eauto.
  6: by apply msg_preserved_refl.
  rewrite coveredE; eauto.
  2: by eapply issuedE; eauto.
  all: basic_solver.
Qed.

End ReadPlainStep.