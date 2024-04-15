Require Import RelationClasses List Lia.
From PromisingLib Require Import Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Events.
Require Import Execution.
Require Import Prog.
Require Import ProgToExecution.

Set Implicit Arguments.

Section Props.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Record thread_restricted_execution (G : execution) t (G' : execution) :=
  { tr_acts_set : (acts_set G') ≡₁ (acts_set G) ∩₁ Tid_ t;
    tr_threads_set : (threads_set G') ⊆₁ eq t;
    tr_lab  : forall x (EE : (acts_set G') x), (lab G') x = (lab G) x;
    tr_rmw  : (rmw G')  ≡ ⦗ Tid_ t ⦘ ⨾ (rmw G) ⨾ ⦗ Tid_ t ⦘;
    tr_data : (data G') ≡ ⦗ Tid_ t ⦘ ⨾ (data G) ⨾ ⦗ Tid_ t ⦘;
    tr_addr : (addr G') ≡ ⦗ Tid_ t ⦘ ⨾ (addr G) ⨾ ⦗ Tid_ t ⦘;
    tr_ctrl : (ctrl G') ≡ ⦗ Tid_ t ⦘ ⨾ (ctrl G) ⨾ ⦗ Tid_ t ⦘;
    tr_rmw_dep :
      (rmw_dep G') ≡
      ⦗ Tid_ t ⦘ ⨾ (rmw_dep G) ⨾ ⦗ Tid_ t ⦘;
  }.

Lemma depf_preserves_set_expr s (depfs : DepsFile.t) (AA : forall r, depfs r ⊆₁ s) :
  forall expr, DepsFile.expr_deps depfs expr ⊆₁ s.
Proof using.
  ins. induction expr.
  1,2: unfold DepsFile.expr_deps, DepsFile.val_deps; desf; apply AA.
  unfold DepsFile.expr_deps.
  unfold DepsFile.val_deps, RegFun.find. desf.
  { basic_solver. }
  all: rewrite AA.
  3: rewrite AA.
  all: basic_solver.
Qed.

Lemma depf_preserves_set_lexpr s (depfs : DepsFile.t) (AA : forall r, depfs r ⊆₁ s) :
  forall expr, DepsFile.lexpr_deps depfs expr ⊆₁ s.
Proof using.
  ins. induction expr.
  all: unfold DepsFile.lexpr_deps, DepsFile.val_deps; desf; apply AA.
Qed.

Section StateWF.
Variable thread : thread_id.
Variable s : state.

Notation "'E'" := (acts_set (G s)).
Notation "'lab'" := (lab (G s)).
Notation "'rf'" := (rf (G s)).
Notation "'co'" := (co (G s)).
Notation "'sb'" := (sb (G s)).
Notation "'rmw'" := (rmw (G s)).
Notation "'data'" := (data (G s)).
Notation "'addr'" := (addr (G s)).
Notation "'ctrl'" := (ctrl (G s)).
Notation "'rmw_dep'" := (rmw_dep (G s)).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Record wf_thread_state := {
  acts_rep :
    forall e (EE : E e),
      exists index,
        ⟪ REP : e = ThreadEvent thread index ⟫ /\
        ⟪ LE : index < (eindex s) ⟫ ;
  acts_clos :
    forall n (LT : n < (eindex s)),
      E (ThreadEvent thread n) ;
  wft_rmwE : rmw ≡ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘ ;
  wft_rmwIndex :
    forall r w (RMW : rmw r w),
      exists index,
        ⟪ RI : r = ThreadEvent thread index ⟫ /\
        ⟪ WI : w = ThreadEvent thread (S index) ⟫ ;
  wft_dataE : data ≡ ⦗E⦘ ⨾ data ⨾ ⦗E⦘ ;
  wft_addrE : addr ≡ ⦗E⦘ ⨾ addr ⨾ ⦗E⦘ ;
  wft_ctrlE : ctrl ≡ ⦗E⦘ ⨾ ctrl ⨾ ⦗E⦘ ;
  wft_rmw_depE : rmw_dep ≡ ⦗E⦘ ⨾ rmw_dep ⨾ ⦗E⦘ ;
  wft_ectrlE : ectrl s ⊆₁ acts_set (G s) ;
  wft_depfE : forall r, depf s r ⊆₁ acts_set (G s);
}.

Lemma wft_sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘.
Proof using. 
split; [|basic_solver].
unfold Execution.sb; basic_solver 42. 
Qed.

End StateWF.

Lemma wf_thread_state_init l thread:
      wf_thread_state thread (init l).
Proof using.
  unfold init. constructor; simpls.
  { ins. inv LT. }
  { basic_solver. }
  1-4: basic_solver.
  ins. unfold DepsFile.init. simpls.
Qed.

Lemma add_preserves_lab thread s s' e hl s1 s2 s3 s4
      (WF : wf_thread_state thread s)
      (UG : G s' = add (G s) thread (eindex s) hl s1 s2 s3 s4)
      (ACT : acts_set (G s) e) :
  lab (G s') e = lab (G s) e.
Proof using.
  unfold add in UG. rewrite UG. simpls.
  rewrite updo; auto.
  intros HH; subst. red in ACT. apply WF in ACT.
  desc. inv REP. lia.
Qed.

Lemma add_rmw_preserves_lab thread s s' e hl s1 s2 s3 s4 s5
      (WF : wf_thread_state thread s)
      (UG : G s' = add_rmw (G s) thread (eindex s) hl s1 s2 s3 s4 s5)
      (ACT : acts_set (G s) e) :
  lab (G s') e = lab (G s) e.
Proof using.
  unfold add in UG. rewrite UG. simpls.
  rewrite !updo; auto.
  all: intros HH; subst.
  all: red in ACT; apply WF in ACT.
  all: desc; inv REP; lia.
Qed.

Lemma add_preserves_acts_clos thread ll s s' hl s1 s2 s3 s4
      (WF : wf_thread_state thread s)
      (STEP : istep thread ll s s')
      (LABELS : ll = hl :: nil)
      (UG : G s' = add (G s) thread (eindex s) hl s1 s2 s3 s4)
      (UINDEX : eindex s' = eindex s + 1) :
  forall n : nat,
    n < eindex s + 1 ->
    acts_set (add (G s) thread (eindex s) hl s1 s2 s3 s4)
             (ThreadEvent thread n).
Proof using.
  unfold add. simpls. ins.
  assert (n <= eindex s) as NS by lia.
  apply Const.le_lteq in NS.
  destruct NS as [LT|LT]; [right|left].
  { apply (acts_clos WF). lia. }
  desf.
Qed.

Lemma add_rmw_preserves_acts_clos thread ll s s' rl wl s1 s2 s3 s4
      (WF : wf_thread_state thread s)
      (STEP : istep thread ll s s')
      (LABELS : ll = wl :: rl :: nil)
      (UG : G s' = add_rmw (G s) thread (eindex s) rl wl s1 s2 s3 s4)
      (UINDEX : eindex s' = eindex s + 2) :
  forall n : nat,
    n < eindex s + 2 ->
    acts_set (add_rmw (G s) thread (eindex s) rl wl s1 s2 s3 s4)
             (ThreadEvent thread n).
Proof using.
  unfold add_rmw. simpls. ins.
  assert (n <= eindex s + 1) as NS by lia.
  apply Const.le_lteq in NS.
  destruct NS as [LT|LT].
  { apply Const.le_lteq in LT.
    destruct LT as [LT|LT].
    { right. apply (acts_clos WF). lia. }
    rewrite Const.add_comm in LT. inv LT.
    left. by right. }
  rewrite Const.add_comm in LT. inv LT.
  rewrite Const.add_comm. do 2 left. eauto.
Qed.

Lemma step_preserves_E thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : step thread state state') :
  acts_set (ProgToExecution.G state) ⊆₁
  acts_set (ProgToExecution.G state').
Proof using.
  red in STEP. desc. cdes STEP.
  destruct ISTEP0.
  all: rewrite UG; auto.
  1-4: by unfold add, acts_set; simpls; right.
  all: by unfold add_rmw, acts_set; simpls; repeat right.
Qed.

Lemma step_preserves_instrs thread state state'
      (STEP : step thread state state') :
  instrs state' = instrs state.
Proof using. inv STEP. inv H. Qed.

Lemma steps_preserve_instrs thread state state'
      (STEPS : (step thread)＊ state state') :
  instrs state' = instrs state.
Proof using.
  apply clos_rt_rtn1 in STEPS. induction STEPS; auto.
  rewrite <- IHSTEPS.
  eapply step_preserves_instrs; eauto.
Qed.

Lemma ectrl_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  (ectrl s) ⊆₁ (ectrl s').
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0; rewrite UECTRL; try done. 
basic_solver.
Qed.

Lemma ectrl_increasing_steps (tid : thread_id) s s' (STEP : (step tid)＊ s s'):
  (ectrl s) ⊆₁ (ectrl s').
Proof using.
  induction STEP.
  { eby eapply ectrl_increasing. }
  { done. }
  unfolder in *; basic_solver.
Qed.

Lemma ctrl_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  (ctrl (G s)) ⊆ (ctrl (G s')).
Proof using.
  destruct STEP; desc.
  red in H; desc.
  destruct ISTEP0.
  all: rewrite UG; try done.
  all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma rmw_dep_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  (rmw_dep (G s)) ⊆ (rmw_dep (G s')).
Proof using.
  destruct STEP; desc.
  red in H; desc.
  destruct ISTEP0.
  all: rewrite UG; try done.
  all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma addr_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  (addr (G s)) ⊆ (addr (G s')).
Proof using.
  destruct STEP; desc.
  red in H; desc.
  destruct ISTEP0.
  all: rewrite UG; try done.
  all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma data_increasing (tid : thread_id) s s' (STEP : step tid s s'):
  (data (G s)) ⊆ (data (G s')).
Proof using.
  destruct STEP; desc.
  red in H; desc.
  destruct ISTEP0.
  all: rewrite UG; try done.
  all: unfold add, add_rmw; ins; basic_solver.
Qed.

Lemma wf_thread_state_step thread s s'
      (WF : wf_thread_state thread s)
      (STEP : step thread s s') :
  wf_thread_state thread s'.
Proof using.
  destruct STEP as [ll STEP]. cdes STEP.
  constructor.
  { destruct ISTEP0.
    all: rewrite UG.
    all: try rewrite UINDEX.
    all: try apply WF.
    all: try (intros e [HH|IN]; [eexists; splits; eauto; lia|];
        edestruct (acts_rep WF); eauto; desc;
        eexists; splits; eauto; lia).
    all: intros e [[HH|IN]|IN].
    all: try (eexists; splits; eauto; lia).
    all: edestruct (acts_rep WF); eauto; desc.
    all: eexists; splits; eauto; lia. }
  { destruct ISTEP0.
    all: rewrite UG.
    all: try rewrite UINDEX.
    1,2: by apply WF.
    1-4: by eapply add_preserves_acts_clos; eauto.
    all: eapply add_rmw_preserves_acts_clos; eauto. }
  { split; [|basic_solver].
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.
    1-4: unfold add; simpls; rewrite (wft_rmwE WF) at 1;
      basic_solver.
    all: unfold add_rmw; simpls; rewrite (wft_rmwE WF) at 1;
      basic_solver. }
  { assert (RMW_HELPER: forall ldlab stlab dps ldps edps r w,
               rmw (add_rmw (G s) thread (eindex s) ldlab stlab
                            dps ldps (ectrl s) edps) r w
               -> exists index : nat,
                 r = ThreadEvent thread index
                 /\ w = ThreadEvent thread (S index)).
    { unfold add_rmw. simpls. intros lblab stlab dps ldps edps r w RMW. 
      destruct RMW as [RMW|RMW].
      2: by apply WF.
      red in RMW. desf.
      rewrite Const.add_comm.
      eexists. splits; eauto. }
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.
    1-4: by unfold add; simpls; apply WF.
    all: apply RMW_HELPER. }
  { split; [|basic_solver].
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.

    all: unfold add, add_rmw; simpls; rewrite (wft_dataE WF) at 1.
    1,3,4: basic_solver 10.
    1: seq_rewrite <- (set_inter_absorb_r
                        (depf_preserves_set_expr _ (wft_depfE WF) expr)).
    3: seq_rewrite <- (set_inter_absorb_r
                        (depf_preserves_set_expr _ (wft_depfE WF) expr_add)).
    2,4: seq_rewrite <- (set_inter_absorb_r
                           (depf_preserves_set_expr _ (wft_depfE WF) expr_new)).
    all: basic_solver 12. }
  { split; [|basic_solver].
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.
    1,2,4: unfold add; simpls; rewrite (wft_addrE WF) at 1;
      seq_rewrite <- (set_inter_absorb_r
                        (depf_preserves_set_lexpr _ (wft_depfE WF) lexpr));
      basic_solver.

    all: unfold add, add_rmw; simpls; rewrite (wft_addrE WF) at 1.
    { basic_solver. }
    all: seq_rewrite <- (set_inter_absorb_r
                           (depf_preserves_set_lexpr _ (wft_depfE WF) lexpr));
      basic_solver 10. }
  { split; [|basic_solver].
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.
    all: unfold add, add_rmw; simpls; rewrite (wft_ctrlE WF) at 1;
      seq_rewrite <- (set_inter_absorb_r (wft_ectrlE WF));
      basic_solver 10. }
  { split; [|basic_solver].
    destruct ISTEP0.
    all: rewrite UG.
    1,2: by apply WF.
    all: unfold add; simpls; rewrite (wft_rmw_depE WF) at 1.
    4-5: seq_rewrite <- (set_inter_absorb_r
                          (depf_preserves_set_expr _ (wft_depfE WF) expr_old)).
    all: basic_solver. }
  { destruct ISTEP0.
    all: rewrite UG, UECTRL.
    { by apply WF. }
    { rewrite (wft_ectrlE WF).
      erewrite depf_preserves_set_expr.
      2: by apply WF.
      basic_solver. }
    1-4: etransitivity; [by apply (wft_ectrlE WF)|];
      unfold add, acts_set; basic_solver.
    all: etransitivity; [by apply (wft_ectrlE WF)|];
      unfold add_rmw, acts_set; basic_solver. }
  assert (acts_set (G s) ⊆₁ acts_set (G s')) as EE.
  { eapply step_preserves_E; eauto. red. eauto. }
  destruct ISTEP0.
  all: rewrite UDEPS; ins.
  all: try unfold RegFun.add, RegFun.find.
  all: try by rewrite (wft_depfE WF).
  all: destruct (Reg.eq_dec r reg).
  all: try by rewrite (wft_depfE WF).
  { by rewrite depf_preserves_set_expr; [|by apply WF]. }
  all: rewrite UG; unfold add, add_rmw, acts_set; simpls; basic_solver.
Qed.

Lemma wf_thread_state_steps thread s s'
      (WF : wf_thread_state thread s)
      (STEP : (step thread)＊ s s') :
  wf_thread_state thread s'.
Proof using.
  induction STEP.
  2: done.
  { eapply wf_thread_state_step; eauto. }
  apply IHSTEP2. by apply IHSTEP1.
Qed.

Lemma steps_preserve_E thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread)＊ state state') :
  acts_set (ProgToExecution.G state) ⊆₁
  acts_set (ProgToExecution.G state').
Proof using.
  intros e EE.
  induction STEP.
  2: done.
  { eapply step_preserves_E; eauto. }
  eapply IHSTEP2.
  { eapply wf_thread_state_steps; eauto. }
  eapply IHSTEP1; eauto.
Qed.

Section StepProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.

Notation "'E'" := (acts_set G).
Notation "'co'" := (co G).
Notation "'coi'" := (coi G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'rfe'" := (rfe G).

Notation "'E'" := (acts_set G).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
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

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

(* Lemma E_thread_in_thread_restricted_E thread pe *)
(*       (TEH : thread_restricted_execution G thread pe) : *)
(*   E ∩₁ Tid_ thread ⊆₁ acts_set pe. *)
(* Proof using. by rewrite (tr_acts TEH). Qed. *)

(* Lemma thread_restricted_E_in_E thread : *)
(*   acts_set (thread_restricted_execution G thread) ⊆₁ E. *)
(* Proof using. *)
(*   unfold thread_restricted_execution. unfold acts_set. simpls. *)
(*   intros x EE. apply in_filter_iff in EE. desf. *)
(* Qed. *)

Lemma rmw_in_thread_restricted_rmw thread G'
      (TEH : thread_restricted_execution G thread G') :
  rmw G' ⊆ rmw G.
Proof using. rewrite (tr_rmw TEH). basic_solver. Qed.

Lemma step_preserves_rmw thread state state'
      (STEP : step thread state state') :
  rmw (ProgToExecution.G state) ⊆
  rmw (ProgToExecution.G state').
Proof using.
  red in STEP. desc. cdes STEP.
  destruct ISTEP0.
  all: rewrite UG; auto.
  1,2: done.
  1-4: unfold add; simpls.
  all: unfold add_rmw; simpls.
Qed.

Lemma steps_preserve_rmw thread state state'
      (STEP : (step thread)＊ state state') :
  rmw (ProgToExecution.G state) ⊆
  rmw (ProgToExecution.G state').
Proof using.
  induction STEP.
  2: done.
  { eapply step_preserves_rmw; eauto. }
  etransitivity; eauto.
Qed.

Lemma step_dont_add_rmw thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : step thread state state') :
  ⦗ acts_set (ProgToExecution.G state) ⦘ ⨾ rmw (ProgToExecution.G state') ⊆
  rmw (ProgToExecution.G state).
Proof using.
  red in STEP. desc. cdes STEP.
  destruct ISTEP0.
  all: rewrite UG; auto.
  1,2: basic_solver.
  1-4: unfold add; simpls; basic_solver.
  { unfold add_rmw. simpls.
    rewrite seq_union_r.
    apply inclusion_union_l; [|basic_solver].
    intros x y HH.
    apply seq_eqv_l in HH. destruct HH as [EE HH].
    red in HH. desf.
    exfalso.
    edestruct (acts_rep GPC); eauto.
    desf. lia. }
  { unfold add_rmw. simpls.
    rewrite seq_union_r.
    apply inclusion_union_l; [|basic_solver].
    intros x y HH.
    apply seq_eqv_l in HH. destruct HH as [EE HH].
    red in HH. desf.
    exfalso.
    edestruct (acts_rep GPC); eauto.
    desf. lia. }
  unfold add_rmw. simpls.
  rewrite seq_union_r.
  apply inclusion_union_l; [|basic_solver].
  intros x y HH.
  apply seq_eqv_l in HH. destruct HH as [EE HH].
  red in HH. desf.
  exfalso.
  edestruct (acts_rep GPC); eauto.
  desf. lia.
Qed.

Lemma steps_dont_add_rmw thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread)＊ state state') :
  ⦗ acts_set (ProgToExecution.G state) ⦘ ⨾ rmw (ProgToExecution.G state') ⊆
  rmw (ProgToExecution.G state).
Proof using.
  induction STEP.
  2: basic_solver.
  { eapply step_dont_add_rmw; eauto. }
  etransitivity.
  2: by apply IHSTEP1.
  intros a b HH.
  apply seq_eqv_l in HH. destruct HH as [EEA HH].
  apply seq_eqv_l. split; auto.
  apply IHSTEP2.
  { eapply wf_thread_state_steps; eauto. }
  apply seq_eqv_l. split; auto.
  eapply steps_preserve_E; eauto.
Qed.

Lemma lab_thread_eq_thread_restricted_lab thread e G'
      (EE : (acts_set G') e)
      (TEH : thread_restricted_execution G thread G') :
  lab G e = lab G' e.
Proof using. rewrite (tr_lab TEH); auto. Qed.

Lemma same_lab_u2v_dom_restricted thread G'
  (TEH : thread_restricted_execution G thread G') :
  same_lab_u2v_dom (acts_set G') (lab G) (lab G').
Proof using. red. ins. red. rewrite (tr_lab TEH); auto. desf. Qed.

Lemma step_preserves_lab e state state'
      (GPC : wf_thread_state (tid e) state)
      (STEP : step (tid e) state state')
      (EE : acts_set (ProgToExecution.G state) e) :
  lab (ProgToExecution.G state') e =
  lab (ProgToExecution.G state) e.
Proof using.
  red in STEP. desc. cdes STEP.
  edestruct (acts_rep GPC) as [ii]; eauto. desc.
  destruct ISTEP0.
  all: rewrite UG; auto.
  1-4: unfold add; simpls; rewrite updo; auto.
  5-7: unfold add_rmw; simpls; rewrite updo; auto;
    [unfold add_rmw; simpls; rewrite updo; auto|].
  all: intros HH; rewrite REP in HH; inv HH; lia.
Qed.

Lemma steps_preserve_lab e state state'
      (GPC : wf_thread_state (tid e) state)
      (STEP : (step (tid e))＊ state state')
      (EE : acts_set (ProgToExecution.G state) e) :
  lab (ProgToExecution.G state') e =
  lab (ProgToExecution.G state) e.
Proof using.
  induction STEP.
  2: done.
  { apply step_preserves_lab; auto. }
  rewrite IHSTEP2.
  { rewrite IHSTEP1; auto. }
  { eapply wf_thread_state_steps; eauto. }
  eapply steps_preserve_E; eauto.
Qed.

Lemma step_empty_same_E thread state state'
      (STEP : istep thread nil state state') :
  acts_set (ProgToExecution.G state') ≡₁
  acts_set (ProgToExecution.G state).
Proof using.
  cdes STEP. inv ISTEP0.
  all: by rewrite UG.
Qed.

Lemma steps_empty_same_E thread state state'
      (STEPS : (istep thread nil)＊ state state') :
  acts_set (ProgToExecution.G state') ≡₁
  acts_set (ProgToExecution.G state).
Proof using.
  induction STEPS.
  2: done.
  { eapply step_empty_same_E; eauto. }
  etransitivity; eauto.
Qed.

Lemma step_same_E_empty_in thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : step thread state state') :
  acts_set (ProgToExecution.G state') ⊆₁
    acts_set (ProgToExecution.G state)
  <->
  istep thread nil state state'.
Proof using.
  assert (~ Execution.acts_set (ProgToExecution.G state)
            (ThreadEvent thread (eindex state))) as XX.
  { intros HH. apply (acts_rep GPC) in HH.
    desc. inv REP. lia. }
  red in STEP. desc.
  red in STEP. desc.
  split; intros IN.
  2: { cdes IN. inv ISTEP2; by rewrite UG. }
  destruct ISTEP0.
  { red. splits; auto. eexists. splits; eauto.
    eapply assign; eauto. }
  { red. splits; auto. eexists. splits; eauto.
    eapply if_; eauto. }
  all: exfalso; apply XX; apply IN.
  1-4: by rewrite UG; unfold acts_set, add; simpls; left.
  all: by rewrite UG; unfold acts_set, add_rmw; simpls;
    left; right.
Qed.

Lemma step_same_E_empty thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : step thread state state') :
  acts_set (ProgToExecution.G state') ≡₁
    acts_set (ProgToExecution.G state)
  <->
  istep thread nil state state'.
Proof using.
  etransitivity.
  2: eapply step_same_E_empty_in; eauto.
  split; [basic_solver|].
  intros HH.
  split; auto.
  eapply step_preserves_E; eauto.
Qed.

Lemma steps_same_E_empty_in thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread)＊ state state') :
  acts_set (ProgToExecution.G state') ⊆₁
    acts_set (ProgToExecution.G state)
  <->
  (istep thread nil)＊ state state'.
Proof using.
  assert (istep thread [] ⊆ step thread) as AA.
  { unfold step. basic_solver. }
  split.
  2: { intros ST.
       induction ST as [x y ST| |].
       2: done.
       { apply step_same_E_empty_in in ST; auto. }
       assert (wf_thread_state thread y) as YY.
       { eapply wf_thread_state_steps; eauto.
         eapply clos_refl_trans_mori; eauto. }
       etransitivity.
       { apply IHST2; auto.
         eapply clos_refl_trans_mori; eauto. }
       apply IHST1; auto.
       eapply clos_refl_trans_mori; eauto. }
  induction STEP; intros.
  2: by apply rt_refl.
  { apply rt_step. by apply step_same_E_empty_in. }
  assert (wf_thread_state thread y) as YY.
  { eapply wf_thread_state_steps; eauto. }
  assert (acts_set (ProgToExecution.G y) ⊆₁
          acts_set (ProgToExecution.G z)) as XX.
  { eapply steps_preserve_E; eauto. }
  eapply rt_trans.
  { apply IHSTEP1; auto. by rewrite XX. }
  apply IHSTEP2; auto.
  etransitivity; eauto.
  eapply steps_preserve_E; eauto.
Qed.

Lemma steps_same_E_empty thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread)＊ state state') :
  acts_set (ProgToExecution.G state') ≡₁
    acts_set (ProgToExecution.G state)
  <->
  (istep thread nil)＊ state state'.
Proof using.
  etransitivity.
  2: by eapply steps_same_E_empty_in; eauto.
  split; [basic_solver|].
  intros IN. split; auto.
  eapply steps_preserve_E; eauto.
Qed.

Lemma steps_same_eindex thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (istep thread nil)＊ state state') :
  (eindex state') = (eindex state).
Proof using.
  induction STEP.
  2: done.
  { cdes H. destruct ISTEP0; desf. }
  rewrite IHSTEP2.
  { by rewrite IHSTEP1. }
  eapply wf_thread_state_steps; eauto.
  eapply clos_refl_trans_mori; eauto.
  unfold step. basic_solver.
Qed.

Lemma step_old_restrict thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread) state state') :
  let GO := (ProgToExecution.G state) in
  let GN := (ProgToExecution.G state') in
  ⟪ ORMW  : (rmw GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (rmw GN) ⨾ ⦗ (acts_set GO) ⦘ ⟫ /\
  ⟪ ODATA : (data GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (data GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OADDR : (addr GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (addr GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OCTRL : (ctrl GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (ctrl GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OFAILDEP : (rmw_dep GO) ≡
                ⦗ (acts_set GO) ⦘ ⨾ (rmw_dep GN) ⨾ ⦗ (acts_set GO)⦘ ⟫.
Proof using.
  red in STEP. desc. red in STEP. desc.
  assert (~ acts_set (ProgToExecution.G state) (ThreadEvent thread (eindex state))) as XX.
  { intros HH. apply (acts_rep GPC) in HH. desc. inv REP. lia. }
  assert (~ acts_set (ProgToExecution.G state) (ThreadEvent thread (eindex state + 1))) as YY.
  { intros HH. apply (acts_rep GPC) in HH. desc. inv REP. lia. }
  destruct ISTEP0; simpls.
  all: rewrite UG.
  1,2: by splits; apply GPC.
  all: unfold add, add_rmw; simpls; splits.
  all: try apply GPC.
  all: try by (rewrite (wft_rmwE GPC) at 1; basic_solver).
  all: try by (rewrite (wft_dataE GPC) at 1; basic_solver).
  all: try by (rewrite (wft_addrE GPC) at 1; basic_solver).
  all: try by (rewrite (wft_ctrlE GPC) at 1; basic_solver).
  all: try by (rewrite (wft_rmw_depE GPC) at 1; basic_solver).
  all: rewrite (wft_ctrlE GPC) at 1; basic_solver 10.
Qed.

Lemma steps_old_restrict thread state state'
      (GPC : wf_thread_state thread state)
      (STEP : (step thread)＊ state state') :
  let GO := (ProgToExecution.G state) in
  let GN := (ProgToExecution.G state') in
  ⟪ ORMW  : (rmw GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (rmw GN) ⨾ ⦗ (acts_set GO) ⦘ ⟫ /\
  ⟪ ODATA : (data GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (data GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OADDR : (addr GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (addr GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OCTRL : (ctrl GO) ≡
             ⦗ (acts_set GO) ⦘ ⨾ (ctrl GN) ⨾ ⦗ (acts_set GO)⦘ ⟫ /\
  ⟪ OFAILDEP : (rmw_dep GO) ≡
                ⦗ (acts_set GO) ⦘ ⨾ (rmw_dep GN) ⨾ ⦗ (acts_set GO)⦘ ⟫.
Proof using.
  induction STEP.
  2: { simpls. splits; apply GPC. }
  { eapply step_old_restrict; eauto. }
  assert (wf_thread_state thread y) as GPC'.
  { eapply wf_thread_state_steps; eauto. }
  simpls. desc.
  assert (acts_set (ProgToExecution.G x) ⊆₁ acts_set (ProgToExecution.G y)) as XX.
  { eapply steps_preserve_E; eauto. }
  specialize (IHSTEP1 GPC).
  specialize (IHSTEP2 GPC').
  desc.
  splits.
  { rewrite ORMW0, ORMW. generalize XX. basic_solver 10. }
  { rewrite ODATA0, ODATA. generalize XX. basic_solver 10. }
  { rewrite OADDR0, OADDR. generalize XX. basic_solver 10. }
  { rewrite OCTRL0, OCTRL. generalize XX. basic_solver 10. }
  rewrite OFAILDEP0, OFAILDEP. generalize XX. basic_solver 10. 
Qed.

End StepProperties.

Lemma step_middle_set thread state state' C
      (OIN : (acts_set (G state)) ⊆₁ C)
      (INN : C ⊆₁ (acts_set (G state')))
      (STEP : (step thread) state state')
      (RMWC : forall r w (RMW : (rmw (G state')) r w),
                       C r <-> C w) :
        C ≡₁ (acts_set (G state)) \/
        C ≡₁ (acts_set (G state')).
Proof using.
  destruct (classic (C ⊆₁ (acts_set (G state)))) as [INO|NINO].
  { left. by split. }
  right. split; auto.
  red in STEP. desc.
  red in STEP. desc.
  unfold set_subset in NINO. apply not_all_ex_not in NINO.
  desc.
  assert (G'1: (exists new_lbl add_dep1 add_ldep add_ctrl add_dep2,
                   G state' = add (G state) thread (eindex state)
                                  new_lbl add_dep1 add_ldep add_ctrl add_dep2)
               -> acts_set (G state') ⊆₁ C).
  { ins. desf.
    rewrite H in *; auto.
    unfold add, acts_set in *; simpls.
    intros y [AA|BB]; [|by apply OIN].
    destruct (classic (C y)) as [|NC]; auto.
    exfalso; apply NINO; ins.
    set (YY := H0). apply INN in YY.
    red in YY. desf. }
  assert (G'2: (exists new_lbl1 new_lbl2 add_dep1 add_ldep add_ctrl add_dep2,
                   G state' = add_rmw (G state) thread (eindex state)
                                      new_lbl1 new_lbl2
                                      add_dep1 add_ldep add_ctrl add_dep2)
               -> acts_set (G state') ⊆₁ C).
  { ins. desf.
    rewrite H in *; auto.
    unfold add_rmw, acts_set in *; simpls.
    destruct (classic (C (ThreadEvent thread (eindex state)))) as [ZZ|NC].
    2: { exfalso. apply NINO. ins.
         set (YY := H0); apply INN in YY.
         unfolder in YY; desf.
         exfalso. apply NC. eapply RMWC; [|by apply H0]. by left. }
    intros x [[AA|BB]|CC]; [ | | by apply OIN]; desf.
    eapply RMWC with (r:=ThreadEvent thread (eindex state)); auto. by left. }
  destruct ISTEP0.
  all: rewrite UG in *; auto.
  1-4: eapply G'1; repeat eexists.
  all: eapply G'2; repeat eexists.
Qed. 
  
Lemma steps_middle_set thread state state' C cindex
      (GPC : wf_thread_state thread state)
      (OIN : (acts_set (G state)) ⊆₁ C)
      (INN : C ⊆₁ (acts_set (G state')))
      (STEP : (step thread)＊ state state')
      (CCLOS : forall index (LT : index < cindex), 
          C (ThreadEvent thread index))
      (CREP :
         forall e (INC : C e),
           exists index,
             ⟪ EREP : e = ThreadEvent thread index ⟫ /\
             ⟪ IIND : index < cindex ⟫)
      (RMWC : forall r w (RMW : (rmw (G state')) r w),
                       C r <-> C w) :
  exists state'',
    ⟪ STEP1 : (step thread)＊ state state'' ⟫ /\
    ⟪ STEP2 : (step thread)＊ state'' state' ⟫ /\
    ⟪ CACTS : (acts_set (G state'')) ≡₁ C ⟫.
Proof using.
  apply clos_rt_rt1n in STEP.
  induction STEP.
  { exists x. splits.
    1,2: apply rt_refl.
      by split. }
  assert (wf_thread_state thread y) as GPC'.
  { eapply wf_thread_state_step; eauto. }
  destruct (Compare_dec.le_ge_dec cindex (eindex y)) as [LL|LL].
  { assert (C ⊆₁ acts_set (G y)) as UU.
    { intros a HH. apply CREP in HH. desc. subst.
      apply (acts_clos GPC'). lia. }
    edestruct step_middle_set with (state:=x) (state':=y) as [YY|YY]; eauto.
    { ins. apply RMWC. eapply steps_preserve_rmw; eauto. }
    { exists x. splits.
      { apply rt_refl. }
      { apply rt_begin. right. eexists; eauto. }
        by rewrite YY. }
    exists y. splits.
    { by apply rt_step. }
    { by apply clos_rt1n_rt. }
      by rewrite YY. }
  assert (acts_set (G y) ⊆₁ C) as UU.
  { intros a HH. apply (acts_rep GPC') in HH. desc. subst.
    apply CCLOS. lia. }
  specialize (IHSTEP GPC' UU INN RMWC). desc.
  exists state''. splits; auto.
  apply rt_begin. right. eexists; eauto.
Qed.

Definition program_execution (prog : Prog.t) (G : execution) :=
  (forall e (IN: (acts_set G) e),
      is_init e \/ IdentMap.In (tid e) prog) /\
  forall thread linstr (INTHREAD: Some linstr = IdentMap.find thread prog),
  exists pe, 
    thread_execution thread linstr pe /\
    thread_restricted_execution G thread pe.

Lemma tid_initi G prog 
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog)) : 
  (acts_set G) ∩₁ Tid_ tid_init ⊆₁ is_init.
Proof using. 
  red. unfolder. 
  intros e [EE TIDe].
  unfold tid, is_init in *.
  destruct e eqn:Heq; auto.
  destruct GPROG as [HH _].
  rewrite <- Heq in EE.
  specialize (HH e EE).
  desf. 
Qed.

Lemma istep_eindex_shift thread st st' lbl
      (STEP : ProgToExecution.istep thread lbl st st') :
  eindex st' = eindex st + length lbl.
Proof using.
  cdes STEP. inv ISTEP0. 
  all: simpls; lia.
Qed.

Lemma eindex_step_mon thread st st'
      (STEP : ProgToExecution.step thread st st') :
  eindex st <= eindex st'.
Proof using.
  cdes STEP.
  rewrite (istep_eindex_shift STEP0). lia.
Qed.

Lemma eindex_steps_mon thread st st'
      (STEPS : (ProgToExecution.step thread)＊ st st') :
  eindex st <= eindex st'.
Proof using.
  apply clos_rt_rt1n in STEPS.
  induction STEPS; auto.
  apply eindex_step_mon in H.
  lia.
Qed.

Lemma eindex_not_in_rmw thread st st'
      (TNIL : thread <> tid_init)
      (WTS : wf_thread_state thread st)
      (STEPS : (ProgToExecution.step thread)＊ st st') :
  ~ (codom_rel (Execution.rmw (ProgToExecution.G st'))
               (ThreadEvent thread (eindex st))).
Proof using.
  intros [y RMW].
  apply clos_rt_rtn1 in STEPS.
  induction STEPS.
  { eapply wft_rmwE in RMW; eauto.
    destruct_seq RMW as [AA BB].
    eapply acts_rep in BB; eauto.
    desf. lia. }
  apply IHSTEPS.
  destruct H as [ll HH].
  cdes HH.
  inv ISTEP0; simpls.
  1,2: by rewrite <- UG.
  all: rewrite UG in RMW; unfold add in RMW; simpls.
  all: destruct RMW as [RMW|RMW]; simpls.
  all: red in RMW; desf.
  all: apply clos_rtn1_rt in STEPS.
  all: apply eindex_steps_mon in STEPS.
  all: lia.
Qed.

Lemma step_threads_set s1 s2 t
      (STEP: step t s1 s2):
  threads_set (ProgToExecution.G s2) ⊆₁ threads_set (ProgToExecution.G s1) ∪₁ eq t /\ 
  threads_set (ProgToExecution.G s1) ⊆₁ threads_set (ProgToExecution.G s2). 
Proof using. 
  inv STEP. inv H. red in H0, H1. desc. inv H2.
  all: rewrite UG; try by vauto.
  all: simpl; basic_solver.
Qed.

Lemma steps_threads_set s1 s2 t
      (STEP: (step t)^* s1 s2):
  threads_set (ProgToExecution.G s2) ⊆₁ threads_set (ProgToExecution.G s1) ∪₁ eq t /\
  threads_set (ProgToExecution.G s1) ⊆₁ threads_set (ProgToExecution.G s2). 
Proof using.
  induction STEP.
  { by apply step_threads_set in H. }
  { basic_solver. }
  desc. split.
  { rewrite IHSTEP2, IHSTEP1. basic_solver. }
  rewrite IHSTEP3, IHSTEP0. basic_solver.
Qed.

End Props.
