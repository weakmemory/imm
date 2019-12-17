From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Configuration TView View Time Event Cell Thread Memory.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s.
Require Import imm_s_hb.
Require Import imm_bob imm_s_ppo.

Require Import PArith.
Require Import CombRelations CombRelationsMore.

Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.

Require Import MaxValue.
Require Import ViewRel.
Require Import ViewRelHelpers.
Require Import SimulationRel.
Require Import SimulationPlainStepAux.
Require Import SimulationRelAux MemoryAux.
Require Import PlainStepBasic.

Require Import SimState.
Require Import SimStateHelper.
Require Import PromiseLTS.
Require Import ProgToExecution.
Require Import Arith.

Set Implicit Arguments.

Section FenceStep.

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

Lemma fence_step PC T f_to f_from thread f smode
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode)
      (TID : tid f = thread)
      (NEXT : next G (covered T) f) (COV : coverable G sc T f)
      (TYPE : F f):
  let T' := (mkTC (covered T ∪₁ eq f) (issued T)) in
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

  assert (~ covered T f) as FNCOV.
  { apply NEXT. }

  cdes STATE. rewrite <- TID in *.
  edestruct sim_state_to_events as [ev HH]; eauto.
  desc.

  apply clos_rt_rt1n in ESTEPS.
  eapply (rtc_lang_tau_step_rtc_thread_tau_step
            _ _ _ local PC.(Configuration.sc) PC.(Configuration.memory)) in ESTEPS.

  assert (E f) as FACT.
  { apply NEXT. }

  assert (exists ordf, lab f = Afence ordf) as FPARAMS; desc.
  { unfold is_f in TYPE.
    destruct (lab f); desf; eexists; eauto. }

  assert (~ is_init f) as FNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  
  assert (~ dom_rel rmw f) as NRMW.
  { intros [x HH].
    apply (dom_l WF.(wf_rmwD)) in HH. apply seq_eqv_l in HH.
    type_solver. }
  
  assert (Event_imm_promise.same_g_events lab (f :: nil) ev) as SAME.
  { by apply SAME_NRMW. }
  
  assert (exists ordr ordw, ev = ProgramEvent.fence ordr ordw)
    as [ordr [ordw EV]].
  { red in SAME; red in SAME; simpls.
    rewrite FPARAMS in *; simpls.
    destruct ev; vauto. }
  set (pe := ThreadEvent.fence ordr ordw).
  assert (ev = ThreadEvent.get_program_event pe) as EV'.
  { done. }
  
  assert (Ordering.le Ordering.acqrel ordw ->
          forall l to, Memory.get l to (Local.promises local) = None) as REL_NO_PROM.
  { intros ORD l to.
    destruct (Memory.get l to (Local.promises local)) as [[from [val rel]]|] eqn: HH; auto.
    exfalso.
    edestruct SIM_PROM as [w]; eauto; desc.
    apply TCCOH in ISS. apply FNCOV.
    destruct ISS as [[[EE WW] ISS] _].
    eapply ISS. exists w.
    apply seq_eqv_r; split; auto.
    right; apply seq_eqv_l; split.
    { split; auto; subst.
      clear -ORD SAME FPARAMS.
      unfold is_ra, is_acq, is_rel, mode_le, Events.mod.
      red in SAME; red in SAME; simpls;
        rewrite FPARAMS in *; simpls.
      unnw; red in SAME.
      desf.
      all: desf. }
    edestruct (same_thread G w f) as [SB|SB]; eauto.
    { intros H. apply NCOV. by apply TCCOH. }
    destruct SB as [|SB]; [subst; type_solver|].
    exfalso. apply NCOV.
    eapply NEXT. eexists; apply seq_eqv_r; split; eauto. }

  assert (Ordering.le Ordering.acqrel ordw <-> Ordering.le Ordering.strong_relaxed ordw)
    as REL_SRLX.
  { subst. clear -SAME FPARAMS.
    unfold mode_le, Events.mod.
    red in SAME; red in SAME; simpls;
      rewrite FPARAMS in *; simpls; desf.
    unnw; red in SAME.
    desf; desf. }
  clear TID.
  eexists.
  apply and_assoc. apply pair_app; unnw.
  { split.
    { set (pe' := None).
      assert (pe' = ThreadEvent.get_event pe) as H.
      { unfold pe. simpls. }
      rewrite H. clear H.
      econstructor; eauto.
      apply Thread.step_program.
      constructor.
      { rewrite EV' in STEP; eauto. }
      unfold pe; eapply Local.step_fence.
      constructor; eauto.
      intros ORD_SRLX l; red.
      intros from to [val rel] MSG.
      exfalso. (* There should be no promised message. *)
      apply REL_SRLX in ORD_SRLX.
      specialize (REL_NO_PROM ORD_SRLX l to).
      desf. }
    red; splits; red; splits; simpls.
    { eapply trav_step_coherence; eauto.
      exists f; left. splits; eauto. }
    { etransitivity; eauto. basic_solver. }
    { intros. apply WF.(wf_rmwD) in RMW.
      apply seq_eqv_l in RMW; destruct RMW as [RR RMW].
      apply seq_eqv_r in RMW; destruct RMW as [RMW WW].
      split; intros [H|H]; left; auto.
      2,4: type_solver.
      { erewrite <- RMWCOV; eauto. }
      erewrite RMWCOV; eauto. }
    { intros e' EE. 
      destruct (Ident.eq_dec (tid e') (tid f)) as [EQ|NEQ].
      { rewrite EQ. eexists.
        rewrite IdentMap.gss; eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      destruct (Ident.eq_dec thread' (tid f)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID.
        assert (Local.promises local0 = Local.promises local) as H.
        { inv TID. }
        rewrite H.
        eapply PROM_IN_MEM; eauto. }
      red; ins. rewrite IdentMap.gso in TID; auto.
      eapply PROM_IN_MEM; eauto. }
    { intros H. apply SC_COV in H. etransitivity; [apply H|].
      basic_solver. }
    { ins; subst.
      eapply sim_sc_fence_step; eauto.
      red in SAME; red in SAME; simpls.
      rewrite FPARAMS in *; simpls. }
    { unfold TView.read_fence_tview, TView.write_fence_sc; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: by apply CLOSED_SC. }
    rewrite IdentMap.gss.
    eexists; eexists; eexists; splits; eauto; simpls.
    { eapply tau_steps_rmw_is_xacq; eauto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      eapply PROM_DISJOINT; eauto. }
    { red. ins.
      (* TODO: generalize the proof! It's used a couple of times. *)
      edestruct SIM_PROM as [w]; eauto.
      exists w; splits; desc; auto.
      assert (W w) as WW.
      { by apply TCCOH. }
      assert (~ (covered T ∪₁ eq f) w <-> ~ covered T w) as HH.
      2: by apply HH.
      split; intros HA HB; apply HA; [by left|].
      destruct HB as [HB|HB]; [done| subst; type_solver]. }
    { red; splits; simpls.
      edestruct SIM_MEM as [rel]; eauto.
      simpls; desc.
      exists rel; splits; auto.
      intros TIDBF COVBF.
      assert (~ covered T b) as COVB.
      { by intros B; apply COVBF; left. }
      destruct H1 as [PROM REL]; auto; unnw; splits; auto.
      subst.
      destruct (Ordering.le Ordering.acqrel ordw) eqn: LL; auto.
      exfalso.
      rewrite REL_NO_PROM in PROM; desf. }
    { eapply sim_tview_fence_step; eauto.
      { red in SAME; red in SAME; simpls.
        rewrite FPARAMS in *; desf. }
      intros H. apply SC_REQ.
      destruct smode; auto.
      exfalso. apply H. by apply SC_COV. }
    { cdes PLN_RLX_EQ. 
      unfold TView.read_fence_tview, TView.write_fence_tview.
      red; splits; simpls.
       all: desf; simpls.
      all: try rewrite EQ_CUR.
      all: try rewrite EQ_ACQ.
      all: reflexivity. }
    { assert (Memory.inhabited PC.(Configuration.memory)) as INHAB.
      { by apply inhabited_future_init. }
      unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc; simpls.
      red; splits; simpls.
      all: desf; ins.
      all: repeat (apply Memory.join_closed_timemap).
      all: try apply MEM_CLOSE.
      all: try apply CLOSED_SC.
      all: by apply Memory.closed_timemap_bot. }
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
  rewrite coveredE; eauto.
  2: by eapply issuedE; eauto.
  5: by apply msg_preserved_refl.
  all: basic_solver.
Qed.

End FenceStep.
