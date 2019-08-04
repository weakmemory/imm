From hahn Require Import Hahn.
From promising Require Import Configuration Basic DenseOrder
     TView View Time Event Cell Thread Language Memory.
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
Require Import PlainStepBasic.

Require Import SimStateHelper.
Require Import Promise ProgToExecution.
Require Import Arith.
Require Import MemoryAux.

Set Implicit Arguments.

Section WritePlainStep.

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

Lemma rlx_write_cover_step PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid w = thread)
      (NEXT : next G (covered T) w) (COV : coverable G sc T w)
      (TYPE : W w)
      (NREL : ~ Rel w)
      (NRMW : ~ codom_rel rmw w):
  let T' := (mkTC (covered T ∪₁ eq w) (issued T)) in
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

  assert (~ covered T w) as WNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E w) as WACT.
  { apply NEXT. }

  assert (exists ex ordw locw valw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }

  assert (~ is_init w) as NINIT.
  { intros IIN. apply WNCOV. apply TCCOH. by split. }
  assert (issued T w) as WISS.
  { cdes COV; desf; type_solver. }
  assert (val lab w = Some valw) as WPVAL.
  { by unfold val; rewrite PARAMS. }

  cdes SIM_MEM.
  edestruct SIM_MEM0 as [rel DOM']; eauto.
  desc.

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x RMW]. apply (dom_l WF.(wf_rmwD)) in RMW.
    apply seq_eqv_l in RMW. type_solver. }

  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }

  set (pe := ThreadEvent.write locw (f_from w) (f_to w)
                               valw rel (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }
  
  assert (forall y : actid, covered T y /\ tid y = tid w -> sb y w) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G w y) as [[ST|ST]|ST]; subst; auto.
    { apply TCCOH in COVY; apply COVY. }
    { done. }
    assert (covered T w) as CC.
    { apply TCCOH in COVY. apply COVY.
      eexists; apply seq_eqv_r; eauto. }
      by apply NEXT in CC. }
  
  assert (Rlx w) as WRLX.
  { apply ALLRLX. by split. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.wmod ordw)) as NRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }

  assert (~ Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as NSRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  assert (~ Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as NREL_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  
  destruct DOM'1 as [INPROM REL_REP]; auto.

  assert (Time.lt (f_from w) (f_to w)) as LT_F_T.
  { by apply FCOH. }

  assert (View.opt_wf rel) as WFREL.
  { apply opt_wf_unwrap. constructor.
    rewrite REL_PLN_RLX. reflexivity. }

  (* TODO: check!!! *)
  assert (Time.le (View.rlx (View.unwrap rel) locw) (f_to w)) as WVREL.
  { subst. simpls.
    destruct REL_REP as [p_rel]; desc.
    rewrite REL in *.
    unfold View.join; simpls.
    unfold TimeMap.join, TimeMap.singleton, LocFun.add.
    rewrite Loc.eq_dec_eq.
    apply Time.join_spec.
    2: reflexivity.
    apply Time.join_spec.
    2: { destruct H0 as [H0|H0]; desc; subst; simpls.
         { unfold TimeMap.bot. apply Time.bot_spec. }
         exfalso. apply NRMW.
         destruct INRMW; desc. by eexists; eauto. }

    clear REL.
    cdes SIM_TVIEW.
    specialize (REL locw locw).
    rewrite Loc.eq_dec_eq in REL.
    unfold LocFun.find in REL.
    cdes REL.
    destruct MAX as [[_ MAX]|[a_max MAX]].
    { rewrite MAX. apply Time.bot_spec. }
    desc.
    destruct (classic (a_max = w)) as [AWEQ|AWNEQ].
    { desf. }

    assert (issued T a_max) as ISSA.
    { destruct INam as [IN|IN].
      { apply t_rel_covered in IN; auto. }
      destruct IN as [[[WA LOCA] TIDA] COVA].
      eapply w_covered_issued; eauto.
        by split. }
    assert ((E ∩₁ W ∩₁ (fun x => loc lab a_max = Some locw)) a_max) as BB.
    { destruct INam as [IN|IN].
      { apply set_interA; split.
        { by apply TCCOH. }
        eapply t_rel_urr_doma; eauto. }
      destruct IN as [[[WA LOCA] TIDA] COVA].
      split; [split|]; auto.
      apply TCCOH in COVA. apply COVA. }
    edestruct (@wf_co_total G WF (Some locw) a_max) as [AWCO|AWCO]; eauto.
      by split; [|done]; split.
      { etransitivity; eauto.
        apply Time.le_lteq; left.
        eapply f_to_co_mon; eauto. }
      exfalso.
      assert (exists y, urr G sc locw a_max y /\ sb y w) as [y [URR SBY]].
      { destruct INam as [INam|INam].
        { destruct INam as [y IN].
          exists y.
          red in IN.
          repeat (hahn_rewrite <- seqA in IN).
          apply seq_eqv_r in IN; destruct IN as [IN COVY].
          apply seq_eqv_r in IN; destruct IN as [IN TID].
          repeat (apply seq_eqv_r in IN; destruct IN as [IN _]).
          split; auto.
          assert (E y) as EY.
          { eapply coveredE in COVY; eauto. }
          destruct TID.
          { destruct (same_thread G w y); auto. }
          apply init_ninit_sb; auto. }
        exists a_max.
        destruct INam as [[[WA LOCA] TIDA] COVA].
        split. 
        { apply urr_refl; basic_solver. }
        destruct (same_thread G w a_max); auto.
        apply BB. }
      eapply sb_transp_rf_co_urr_irr; eauto.
      1-3: by apply CON.
      eexists; split; eauto.
      eexists; split.
        by left.
        eexists; split; eauto. }

  edestruct (Memory.remove_exists (Local.promises local)  locw)
    as [new_prom NPCH].
  { edestruct (SIM_MEM locw w) as [rel' HH]; eauto. }
  
  destruct REL_REP as [p_rel]; desf.
  2: { exfalso. apply NRMW. destruct INRMW as [z H].
       eexists. apply H; done. }

  cdes CON.
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
      unfold pe; eapply Local.step_write.
      econstructor.
      { unfold TView.write_released.
        rewrite NRLX_PROM_W; simpls.
        rewrite View.join_bot_l.
        destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) eqn: HH.
        { subst; desf. }
        simpls; rewrite view_join_bot_r in *.
          by unfold LocFun.add; rewrite Loc.eq_dec_eq. }
      { constructor.
        edestruct (max_event_cur) as [a_max]; eauto; desc.
        assert (E a_max) as EA.
        { apply (wf_urrE WF) in CCUR; auto.
          revert CCUR; unfold seq; unfolder; ins; desf. }
        assert (issued T a_max) as AISS.
      { assert (A: (urr G sc locw ⨾ ⦗coverable G sc T⦘) a_max w).
        by basic_solver.
        apply (urr_coverable) in A; try done.
        revert A; unfold seq; unfolder; ins; desf. }
        edestruct (@wf_co_total G WF (Some locw) a_max) as [AWCO|AWCO].
        3: apply NEQ.
        2: basic_solver.
        1: apply set_interA; split; auto.
        hahn_rewrite (@wf_urrD G sc locw) in CCUR.
        revert CCUR; clear; basic_solver 12.
        { eapply TimeFacts.le_lt_lt; eauto; cdes FCOH.
          assert (DenseOrder.le (f_to a_max) (f_from w)) as LE.
          { apply TCO; auto. }
          eapply TimeFacts.le_lt_lt; eauto. }
        exfalso.
        eapply transp_rf_co_urr_irr; eauto.
        exists w; split.
        { by left. }
        eexists; eauto. }
      { econstructor.
        2: by apply NPCH.
        apply Memory.promise_lower; auto.
        all: by apply Memory.lower_exists_same. }
      intros. exfalso.
      unfold Event_imm_promise.wmod, is_rel, mode_le, Events.mod in *.
      rewrite PARAMS in *.
      destruct ordw; simpls. }
    unnw.
    red; splits; red; splits; simpls.
    { eapply trav_step_coherence; eauto.
      eexists; left. splits; eauto. }
    { etransitivity; eauto. basic_solver. }
    { intros. apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH]; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { type_solver. }
      { erewrite RMWCOV; eauto. }
      subst. exfalso. apply NRMW. eexists; eauto. }
    { intros e' EE. 
      destruct (Ident.eq_dec (tid e') (tid w)) as [EQ|NEQ].
      { rewrite EQ. eexists.
        rewrite IdentMap.gss; eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        etransitivity.
        2: by eapply PROM_IN_MEM; eauto.
        inv TID; simpls. clear TID.
        red; ins.
        erewrite Memory.remove_o in LHS; eauto.
        destruct (loc_ts_eq_dec (loc, to) (locw, f_to w)) as [|NEQ]; [by desf|].
          by erewrite loc_ts_eq_dec_neq in LHS. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      eapply PROM_IN_MEM; eauto. }
    { ins. etransitivity; [apply SC_COV|]; auto.
      basic_solver. }
    { intros NFSC l.
      eapply max_value_same_set.
      { by apply SC_REQ. }
      rewrite s_tm_union.
      unfold CombRelations.S_tm.
      split; unionL; try basic_solver 3.
      rewrite (wf_S_tmrD); type_solver 21. }
    rewrite IdentMap.gss.
    assert (Memory.inhabited (Configuration.memory PC)) as INHAB.
    { by apply inhabited_future_init. }
 
    eexists; eexists; eexists; splits; eauto; simpls.
    { eapply tau_steps_rmw_is_xacq; eauto. }
    { ins. rewrite IdentMap.gso in TID'; auto.
      edestruct (PROM_DISJOINT thread') as [H|]; eauto.
      left. erewrite Memory.remove_o; eauto. desf. }
    { red; splits; simpls.
      erewrite Memory.remove_o in PROM; eauto. 
      destruct (loc_ts_eq_dec (l, to) (locw, f_to w)) as [[EQ1 EQ2]|NEQ]; simpls; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to w)) in PROM.
        inv PROM. }
      rewrite (loc_ts_eq_dec_neq NEQ) in PROM.
      edestruct SIM_PROM as [b H]; eauto; desc.
      exists b; splits; auto.
      intros [H|H]; [done|subst].
      unfold loc in *; rewrite PARAMS in *; desf. }
    { red; ins.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)); vauto.
      destruct (classic (b = w)) as [|NEQ].
      { subst.
        unfold loc in LOC; unfold val in VAL; rewrite PARAMS in *; inv LOC.
        eexists; splits; eauto.
        intros _ H.
          by exfalso; apply H; right. }
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      exists rel; splits; auto.
      intros TT COVWB.
      destruct H1 as [PROM REL]; auto; unnw.
      { by intros H; apply COVWB; left. }
      erewrite Memory.remove_o; eauto.

      (* TODO: generalize! *)
      assert (l = locw -> Time.lt (f_to w) (f_to b)) as FGT.
      { ins; subst. eapply f_to_co_mon; eauto.
        assert (co w b \/ co b w) as H; [|destruct H as [|H]; [done|exfalso]].
        { assert (W b) as WB.
          { by apply TCCOH. }
          edestruct (@wf_co_total G WF (Some locw)).
          3: by eauto.
          1,2: by red; split; [red; split|]; auto.
            by right.
              by left. }
        cdes CON.
        eapply Cint.
        eexists; split.
        2: { apply r_step. red. left; right.
             eexists; split; eauto. }
        apply sb_in_hb.
        edestruct (same_thread G b w) as [[HH|HH]|]; vauto.
        { intros IB. apply COVWB; left. by apply TCCOH. }
        exfalso.
        apply COVWB; left.
        apply NEXT. eexists; apply seq_eqv_r; eauto. }

      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to w)) as [[A B]|LNEQ].
      { exfalso. simpls; subst; rewrite B in *.
          by apply DenseOrder.lt_strorder in FGT. }
      simpls. rewrite (loc_ts_eq_dec_neq LNEQ).
      splits; auto.
      unfold LocFun.add.
      destruct (classic (l = locw)) as [LL|LL].
      2: by rewrite Loc.eq_dec_neq.
      subst; rewrite Loc.eq_dec_eq.
      destruct REL as [p_rel [REL HH]]; exists p_rel; splits.
      2: by apply HH.
      rewrite View.join_assoc.
      rewrite (View.join_comm (View.unwrap p_rel)).
      rewrite <- View.join_assoc.
      rewrite (View.join_comm _ (View.singleton_ur locw (f_to b))).
      rewrite (View.join_comm _ (View.singleton_ur locw (f_to w))).
      rewrite <- View.join_assoc.
      rewrite (@View.le_join_l (View.singleton_ur locw (f_to b))); auto.
      { rewrite View.join_assoc. by rewrite View.join_comm. }
      unfold View.singleton_ur, TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
      constructor; simpls; intros l.
      all: destruct (Loc.eq_dec l locw).
      2,4: by apply Time.bot_spec.
      all: by apply Time.le_lteq; left; apply FGT. }
    { eapply sim_tview_write_step; eauto.
      { etransitivity; [by apply TCCOH|].
        intros x H; apply H. }
      { intros x y H. apply seq_eqv_r in H; destruct H as [H1 H2].
        apply TCCOH in H2. apply H2. eexists; apply seq_eqv_r; eauto. }
      intros x y H. apply seq_eqv_r in H; destruct H as [H]; subst.
      apply COV. eexists; apply seq_eqv_r; eauto. }
    { cdes PLN_RLX_EQ. 
      unfold TView.write_tview.
      red; splits; simpls.
      all: desf; simpls.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      1-2: reflexivity.
      all: unfold LocFun.add, LocFun.find, View.join; intros l.
      all: desf; simpls.
      all: rewrite EQ_REL; reflexivity. }
    { unfold TView.write_tview; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: try by eapply Memory.singleton_closed_timemap; eauto.
      all: unfold LocFun.add, LocFun.find; desf.
      all: try by apply MEM_CLOSE.
      all: apply Memory.join_closed_timemap.
      all: try apply MEM_CLOSE.
      all: by eapply Memory.singleton_closed_timemap; eauto. }
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

Lemma rlx_write_promise_step PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid w = thread)
      (WNISS : ~ issued T w)
      (ISS : issuable G T w)
      (NREL : ~ is_rel lab w):
  let T' := (mkTC (covered T) (issued T ∪₁ eq w)) in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step None thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to' f_from' smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (W w /\ E w) as [TYPE WACT].
  { split; apply ISS. }

  assert (~ covered T w) as WNCOV.
  { intros H. apply WNISS.
      by eapply w_covered_issued; eauto; split. }

  assert (~ is_init w) as WNINIT.
  { intros H; apply WNCOV. by apply TCCOH. }
  
  assert (tc_coherent G sc (mkTC (covered T) (issued T ∪₁ eq w))) as TCCOH_NEW.
  { eapply trav_step_coherence; eauto.
    exists w; right; splits; simpls. }
 
  assert (exists ex ordw locw valw,
             lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }
  assert (val lab w = Some valw) as WVAL.
  { by unfold val; rewrite PARAMS. }

  assert (W ∩₁ Rel ∩₁ (issued T ∪₁ eq w) ⊆₁ covered T) as RELCOV_NEW.
  { simpls. rewrite !set_inter_union_r.
    rewrite (set_interA W Rel (eq w)).
    arewrite (Rel ∩₁ eq w ⊆₁ ∅).
    { intros x [H]; desf. }
    generalize RELCOV; basic_solver. }
  
  cdes SIM_MEM. 
  edestruct write_promise_step_helper as [p_rel H].
  13: by apply FCOH.
  all: eauto.
  desc. destruct H1 as [H|H].
  { cdes H; clear H.
    set (pe :=
           ThreadEvent.promise
             locw (f_from' w) (f_to' w) valw
             (Some
                (View.join
                   (View.join
                      (if is_rel lab w
                       then TView.cur (Local.tview local)
                       else TView.rel (Local.tview local) locw) (View.unwrap p_rel))
                   (View.singleton_ur locw (f_to' w))))
             Memory.op_kind_add).

    eexists; exists f_to'; exists f_from'.
    apply and_assoc. apply pair_app; unnw.
    { split.
      { set (pe' := None).
        assert (pe' = ThreadEvent.get_event pe) as H.
        { unfold pe. simpls. }
        rewrite H. clear H.
        econstructor; eauto.
        apply Thread.step_promise.
        constructor.
        2: by simpls.
        constructor; eauto. }
      destruct (is_rel lab w); simpls; subst.
      red; splits; red; splits; eauto.
      simpls.
      exists state; eexists.
      rewrite IdentMap.gss.
      splits; eauto.
      eapply sim_tview_f_issued; eauto. }
    intros [PCSTEP SIMREL_THREAD']; split; auto.
    intros SMODE SIMREL.
    eapply simrel_f_issued in SIMREL; eauto.
    eapply full_simrel_step.
    13: by apply SIMREL.
    11: { ins. rewrite IdentMap.Facts.add_in_iff.
          split; auto. intros [|]; auto; subst.
          apply IdentMap.Facts.in_find_iff.
            by rewrite LLH. }
    all: simpls; eauto.
    7: by eapply msg_preserved_add; eauto.
    6: by eapply closedness_preserved_add; eauto.
    { eapply coveredE; eauto. }
    rewrite issuedE; eauto.
    all: basic_solver. }
  cdes H. clear H.
  set (pe :=
         ThreadEvent.promise
           locw (f_from' w) (f_to' w) valw rel 
           (Memory.op_kind_split (f_to' ws) valws relws)).
  eexists; exists f_to'; exists f_from'.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := None).
      assert (pe' = ThreadEvent.get_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_promise.
      constructor.
      2: by simpls.
      constructor; eauto. }
    subst.
    red; splits; red; splits; eauto.
    { intros. desf. }
    simpls.
    exists state; eexists.
    rewrite IdentMap.gss.
    destruct (is_rel lab w); simpls.
    splits; eauto.
    { eapply sim_tview_f_issued; eauto. }
    eapply tview_closedness_preserved_split; eauto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE'. desf.
Qed.

Lemma rel_write_step PC T f_to f_from thread w smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid w = thread)
      (NEXT : next G (covered T) w)
      (TYPE : W w)
      (REL : Rel w)
      (NRMW : ~ codom_rel rmw w)
      (TS1 : itrav_step G sc w T (mkTC (covered T) (issued T ∪₁ eq w)))
      (TS2 : itrav_step G sc w
                        (mkTC (covered T) (issued T ∪₁ eq w))
                        (mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w))) :
  let T' := (mkTC (covered T ∪₁ eq w) (issued T ∪₁ eq w)) in
  exists PC' f_to' f_from',
    ⟪ PCSTEP : plain_step None thread PC PC' ⟫ /\
    ⟪ SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to' f_from' smode ⟫ /\
    ⟪ SIMREL :
        smode = sim_normal -> simrel G sc PC T f_to f_from ->
        simrel G sc PC' T' f_to' f_from' ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.

  assert (~ covered T w) as WNCOV.
  { apply NEXT. }
  
  assert (issuable G T w) as WISS.
  { eapply issuable_next_w; eauto. split; auto. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E w) as WACT by apply NEXT.
  assert (Rlx w) as WRLX by mode_solver.

  assert (exists ex ordw locw valw, lab w = Astore ex ordw locw valw) as PARAMS; desf.
  { unfold is_w in TYPE.
    destruct (lab w); desf; eexists; eauto. }
  assert (loc lab w = Some locw) as WLOC.
  { by unfold loc; rewrite PARAMS. }
  assert (val lab w = Some valw) as WPVAL.
  { by unfold val; rewrite PARAMS. }
  assert (Events.mod lab w = ordw) as WMOD.
  { by unfold Events.mod; rewrite PARAMS. }

  assert (~ is_init w) as NINIT.
  { intros IIN. apply WNCOV. apply TCCOH. by split. }
  assert (~ issued T w) as WNISS.
  { intros ISS. apply WNCOV. apply RELCOV.
    split; [split|]; auto. }

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.wmod ordw)) as NRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }

  assert (Ordering.le Ordering.strong_relaxed (Event_imm_promise.wmod ordw)) as NSRLX_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }
  assert (Ordering.le Ordering.acqrel (Event_imm_promise.wmod ordw)) as NREL_PROM_W.
  { unfold Event_imm_promise.wmod, is_rel, is_rlx, mode_le, Events.mod in *.
    rewrite PARAMS in *.
    destruct ordw; simpls. }

  edestruct write_promise_step_helper as [p_rel H].
  13: by apply FCOH.
  all: eauto.
  desc. destruct H1 as [H|H].
  2: by cdes H; desf.
  cdes H; clear H. destruct (is_rel lab w) eqn:RELVV; [|by red in REL; desf].
  simpls.

  assert (~ dom_rel rmw w) as NNRMW.
  { intros [x HH].
    apply (dom_l WF.(wf_rmwD)) in HH. apply seq_eqv_l in HH.
    type_solver. }
  
  assert (Event_imm_promise.same_g_events lab (w :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (ev = ProgramEvent.write locw valw (Event_imm_promise.wmod ordw)) as EV.
  { red in SAME; red in SAME; simpls.
    rewrite PARAMS in *; simpls.
    destruct ev; desf; vauto. }
  set (pe := ThreadEvent.write locw (f_from' w) (f_to' w) valw
                               (Some (View.join
                                        (View.join
                                           (TView.cur (Local.tview local))
                                           (View.unwrap p_rel))
                                        (View.singleton_ur locw (f_to' w))))
                               (Event_imm_promise.wmod ordw)).
  assert (ev = ThreadEvent.get_program_event pe) as EV' by done; subst.

  assert (p_rel = None); subst.
  { destruct P_REL_CH as [H|H]; desc; auto.
    exfalso. destruct INRMW as [z [_ RMW]].
    eapply NRMW. eexists; eauto. }

  eexists; exists f_to'; exists f_from'.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := None).
      assert (pe' = ThreadEvent.get_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite <- EV'; eauto. }
      eapply Local.step_write.
      constructor.
      { unfold TView.write_released, TView.write_tview; simpls.
        unfold LocFun.add. rewrite Loc.eq_dec_eq.
        destruct (Ordering.le Ordering.relaxed
                              (Event_imm_promise.wmod (Events.mod lab w))); simpls.
        destruct (Ordering.le Ordering.acqrel
                              (Event_imm_promise.wmod (Events.mod lab w))); simpls.
        rewrite View.join_bot_l. by rewrite view_join_bot_r. }
      { by constructor. }
      { econstructor; eauto. }
      ins; split; auto. }
    red; splits; red; splits; eauto; ins.
    { eapply trav_step_coherence. exists w. apply TS2.
      eapply trav_step_coherence; eauto. by exists w. }
    { generalize RELCOV. basic_solver 10. }
    { apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [HH|HH]; left; auto.
      { erewrite <- RMWCOV; eauto. }
      { type_solver. }
      { erewrite RMWCOV; eauto. }
      subst. exfalso. apply NRMW. eexists; eauto. }
    { destruct (classic (tid e = tid w)) as [EQ|NEQ].
      { rewrite EQ. rewrite IdentMap.gss. eauto. }
      rewrite IdentMap.gso; auto. }
    { destruct (classic (thread' = tid w)) as [EQ|NEQ].
      { rewrite EQ in *. rewrite IdentMap.gss in *.
        inv TID. eapply PROM_IN_MEM0.
          by rewrite IdentMap.gss. }
      rewrite IdentMap.gso in *; auto.
      etransitivity.
      { eapply PROM_IN_MEM; eauto. }
      eapply memory_add_le; eauto. }
    { etransitivity; [by apply SC_COV|].
      basic_solver. }
    { eapply max_value_same_set.
      { apply SC_REQ0; auto. }
      apply s_tm_n_f_steps.
      { apply TCCOH. }
      { basic_solver. }
      intros a [BB|BB] OO; [by desf|intros CC; subst].
      type_solver. }
    exists state'''; eexists. splits; simpls.
    { eapply tau_steps_rmw_is_xacq; eauto. }
    { rewrite IdentMap.gss. simpls. }
    { ins. eapply PROM_DISJOINT0; eauto.
      rewrite IdentMap.gso in *; eauto. }
    { red; ins. }
    { ins. }
    { eapply sim_tview_write_step; eauto.
      1,2: by apply CON.
      { intros a H. apply TCCOH in H. apply H. }
      { arewrite (covered T ⊆₁ coverable G sc T) by apply TCCOH.
        intros x y H. apply seq_eqv_r in H; destruct H as [H1 H2].
        apply H2. exists y; apply seq_eqv_r. desf. }
      { eapply sim_tview_f_issued; eauto. }
      { intros y [COVY TIDY].
        destruct (same_thread G w y) as [[EQ|SB]|SB]; auto.
        { apply TCCOH in COVY. apply COVY. }
        { desf. }
        exfalso. apply WNCOV. apply TCCOH in COVY. apply COVY.
        exists y. apply seq_eqv_r; split; auto. }
      { intros x y H. apply seq_eqv_r in H; desc; subst.
        apply NEXT. eexists. apply seq_eqv_r; split; eauto. }
      { erewrite Memory.add_o.
        { rewrite loc_ts_eq_dec_eq; eauto. }
        apply PADD. }
      simpls. }
    { cdes PLN_RLX_EQ.
      simpls. red. unfold TView.write_tview. simpls; splits.
      { by rewrite EQ_CUR. }
      { by rewrite EQ_ACQ. }
      ins. unfold LocFun.add, LocFun.find.
      destruct (Loc.eq_dec l locw).
      2: by rewrite EQ_REL.
      destruct (Ordering.le Ordering.acqrel (Event_imm_promise.wmod (Events.mod lab w))).
      all: unfold View.join; simpls.
        by rewrite EQ_CUR. }
    { desf. }
    red. splits; eauto.
    ins. rewrite INDEX_NRMW; auto.
    apply sim_state_cover_event; auto. }
  intros [PCSTEP SIMREL_THREAD']; split; auto.
  intros SMODE SIMREL.
  eapply simrel_f_issued in SIMREL; eauto.
  eapply full_simrel_step.
  13: by apply SIMREL.
  11: { ins. rewrite IdentMap.Facts.add_in_iff.
        split; auto. intros [|]; auto; subst.
        apply IdentMap.Facts.in_find_iff.
          by rewrite LLH. }
  all: eauto; simpls.
  8: by eapply msg_preserved_add; eauto.
  7: by eapply closedness_preserved_add; eauto.      
  rewrite coveredE; eauto.
  2: rewrite issuedE; eauto.
  all: basic_solver.
Qed.

End WritePlainStep.