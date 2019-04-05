Require Import Classical Peano_dec.
Require Import Setoid.
From hahn Require Import Hahn.
From promising Require Import Basic DenseOrder
     TView View Time Event Cell Thread Language Memory Configuration.
Require Import AuxRel.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s.
Require Import imm_s_hb.
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
Require Import SimulationRelAux MemoryAux.

Require Import Promise.

Set Implicit Arguments.

Section ReadPlainStepHelper.

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

Lemma read_step_helper PC T f_to f_from r w locr valr rel smode
      state local state' 
      (SIMREL_THREAD : simrel_thread G sc PC (tid r) T f_to f_from smode)
      (NEXT : next G (covered T) r) (COV : coverable G sc T r)
      (RR : R r)
      (LOC : loc lab r = Some locr) (VAL : val lab r = Some valr)
      (WW : W w) (RF : rf w r)
      (INMEM : Memory.get locr (f_to w) PC.(Configuration.memory) =
               Some (f_from w, Message.mk valr rel))
      (TIDMAP : IdentMap.find (tid r) PC.(Configuration.threads) =
                Some (existT _ (thread_lts (tid r)) state, local)) :
  let T' := (mkTC (covered T ∪₁ eq r) (issued T)) in
  let tview' := TView.read_tview (Local.tview local) locr
                                 (f_to w) rel (Event_imm_promise.rmod (mod lab r)) in
  let langst' := existT _ (thread_lts (tid r)) state' in
  let local' := Local.mk tview' (Local.promises local) in
  let threads' :=
      IdentMap.add (tid r) (langst', local')
                   (Configuration.threads PC) in
  let PC' := Configuration.mk threads' PC.(Configuration.sc) PC.(Configuration.memory) in
  ⟪ TCCOH : tc_coherent G sc T' ⟫ /\
  ⟪ RELCOV : W ∩₁ Rel ∩₁ issued T' ⊆₁ covered T' ⟫ /\

  ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
      exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\

  ⟪ PROM_IN_MEM :
      forall thread' langst local
             (TID : IdentMap.find thread' threads' = Some (langst, local)),
        Memory.le local.(Local.promises) PC.(Configuration.memory) ⟫ /\

  ⟪ FCOH: f_to_coherent G (issued T') f_to f_from ⟫ /\

  ⟪ SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T' ⟫ /\ 
  ⟪ SC_REQ : smode = sim_normal -> 
         forall (l : Loc.t),
           max_value f_to (S_tm G l (covered T')) (LocFun.find l PC.(Configuration.sc)) ⟫ /\

  ⟪ SIM_PROM : sim_prom G sc (tid r) T' f_to f_from local.(Local.promises) ⟫ /\
  ⟪ RESERVED_TIME :
      reserved_time G f_to f_from (issued T') PC.(Configuration.memory) smode ⟫ /\
  
  ⟪ SIM_MEM : sim_mem G sc T' f_to f_from (tid r) local' PC.(Configuration.memory) ⟫ /\
  ⟪ SIM_TVIEW : sim_tview G sc (covered T') f_to tview' (tid r) ⟫ /\
  ⟪ PLN_RLX_EQ : pln_rlx_eq tview' ⟫ /\
  ⟪ MEM_CLOSE : memory_close tview' PC.(Configuration.memory) ⟫.
Proof.
  simpls.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (X := STATE).
  
  assert (~ covered T r) as RNCOV.
  { apply NEXT. }

  assert (E r) as RACT.
  { apply NEXT. }
  assert (~ is_init r) as RNINIT.
  { intros H; apply (init_w WF) in H. type_solver. }
  assert (Rlx r) as RRLX.
  { apply ALLRLX. by split. }

  assert (issued T w) as WISS.
  { destruct COV as [_ [[COV|[_ COV]]|COV]].
    1,3: type_solver.
    apply COV.
    eexists; apply seq_eqv_r; split; eauto. }

   assert (exists xrmw, rmwmod lab r = Some xrmw) as RXRMW.
   { unfold rmwmod. unfold is_r in *. desf. eauto. }

  assert (loc lab w = Some locr) as WPLOC.
  { assert (loc lab w = loc lab r) as HH.
    { by apply (wf_rfl WF). }
      by rewrite HH. }
  assert (val lab w = Some valr) as WPVAL.
  { assert (val lab w = val lab r) as HH.
    { by apply wf_rfv. }
      by rewrite HH. }

  assert (E w) as WPACT.
  { apply (wf_rfE WF) in RF. apply seq_eqv_l in RF; desf. }

  edestruct SIM_MEM as [rel' DOM].
  2: by apply WISS.
  all: eauto.
  simpls. desc.
  rewrite INMEM in INMEM0. inv INMEM0. clear INMEM0.
  rename rel' into rel.

  assert (Ordering.le Ordering.relaxed (Event_imm_promise.rmod (mod lab r))) as RLX_ORDR.
  { unfold is_rlx, mode_le, mod, is_r in *.
    destruct (lab r); desf. }
  
  assert (forall y : actid, covered T y /\ tid y = tid r -> sb y r) as COVSB.
  { intros y [COVY TIDY].
    destruct (same_thread G r y) as [[ST|ST]|ST]; subst; auto.
    { apply TCCOH in COVY. apply COVY. }
    { done. }
    assert (covered T r) as CC.
    2: by apply NEXT in CC.
    apply TCCOH in COVY. apply COVY.
    eexists; apply seq_eqv_r; eauto. }
  
  splits; simpls.
  { eapply trav_step_coherence; eauto.
    eexists; left. splits; eauto. }
  { etransitivity; eauto. basic_solver. }
  { intros e' EE. 
    destruct (Ident.eq_dec (tid e') (tid r)) as [EQ|NEQ].
    { rewrite EQ. eexists.
      rewrite IdentMap.gss; eauto. }
    rewrite IdentMap.gso; auto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid r)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID.
      assert (Local.promises local0 = Local.promises local) as H.
      { inv TID. }
      rewrite H.
      eapply PROM_IN_MEM; eauto. }
    red; ins. rewrite IdentMap.gso in TID; auto.
    eapply PROM_IN_MEM; eauto. }
  { intros H. apply SC_COV in H. etransitivity; [apply H|].
    basic_solver. }
  { intros NFSC l; subst.
    eapply max_value_same_set.
    { apply SC_REQ; auto. }
    rewrite s_tm_union.
    unfold CombRelations.S_tm.
    split; unionL; try basic_solver 3.
    rewrite (wf_S_tmrD); type_solver 21. }
  { red. ins.
    (* TODO: generalize the proof! It's used a couple of times. *)
    edestruct SIM_PROM as [w']; eauto.
    exists w'; splits; desc; auto.
    assert (W w') as WW'.
    { by apply TCCOH. }
    assert (~ (covered T ∪₁ eq r) w' <-> ~ covered T w') as HH.
    2: by apply HH.
    split; intros HA HB; apply HA; [by left|].
    destruct HB as [HB|HB]; [done| subst; type_solver]. }
  { red; splits; simpls.
    edestruct SIM_MEM as [rel']; eauto.
    simpls; desc.
    exists rel'; splits; auto.
    intros TIDBF COVBF.
    assert (~ covered T b) as COVB.
    { by intros B; apply COVBF; left. }
    destruct H1 as [PROM REL]; auto; unnw; splits; auto. }
  { eapply sim_tview_read_step; eauto.
    1,2: by apply CON.
    { red; intros x y H. apply NEXT.
        by exists y. }
    unfold is_r, loc, val, mod, rmwmod in *. desf. }
  { cdes PLN_RLX_EQ. 
    unfold View.singleton_ur_if.
    red; splits; simpls.
    all: desf; simpls.
    all: try rewrite REL_PLN_RLX.
    all: try rewrite EQ_SIN.
    all: try rewrite EQ_CUR.
    all: try rewrite EQ_ACQ.
    all: reflexivity. }
  assert (Memory.inhabited PC.(Configuration.memory)) as INHAB.
  { by apply inhabited_future_init. }
  unfold TView.read_tview; simpls.
  red; splits; simpls.
  all: desf; ins.
  all: repeat (apply Memory.join_closed_timemap).
  all: try apply MEM_CLOSE.
  all: auto.
  all: try by apply Memory.closed_timemap_bot.
  all: by eapply Memory.singleton_closed_timemap; eauto.
Qed.

End ReadPlainStepHelper.