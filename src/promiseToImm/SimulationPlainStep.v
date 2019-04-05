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
Require Import Prog ProgToExecution.
Require Import SimulationPlainStepAux.
Require Import SimulationRelAux.

Require Import PlainStepBasic.
Require Import FencePlainStep.
Require Import WritePlainStep.
Require Import ReadPlainStep.
Require Import RMWPlainStep.

Set Implicit Arguments.

Section PlainStep.

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

Lemma plain_sim_step thread PC T f_to f_from T' smode
      (TCSTEP : isim_trav_step G sc thread T T')
      (SIMREL_THREAD : simrel_thread G sc PC thread T f_to f_from smode) :
    exists PC' f_to' f_from',
      ⟪ PSTEP : plain_step None thread PC PC' ⟫ /\
      ⟪ SIMREL_THREAD : simrel_thread G sc PC' thread T' f_to' f_from' smode ⟫ /\
      ⟪ SIMREL :
          smode = sim_normal -> simrel G sc PC T f_to f_from ->
          simrel G sc PC' T' f_to' f_from' ⟫.
Proof.
  cdes SIMREL_THREAD. cdes COMMON. cdes LOCAL.
  set (TCSTEP' := TCSTEP).
  destruct TCSTEP'.
  { (* Fence covering *)
    cdes TS. desf.
    2: { red in ISS. type_solver. }
    edestruct fence_step; eauto.
    red. split; [split|]; auto. all: apply COV. }
  { (* Read covering *)
    cdes TS. desf.
    2: { red in ISS. type_solver. }
    edestruct read_step; eauto.
    red. split; [split|]; auto. all: apply COV. }
  { (* Relaxed write issuing *)
    cdes TS. desf.
    { exfalso. apply NISS. red in COV. 
      destruct COV as [_ [[COV|COV]|COV]].
      { apply COV. }
      all: type_solver. }
    edestruct rlx_write_promise_step; eauto. }
  { (* Relaxed write covering *)
    cdes TS. desf.
    edestruct rlx_write_cover_step; eauto.
    red. split; [split|]; auto. all: apply COV. }
  { (* Release write covering *)
    cdes TS1. desf.
    { exfalso. apply NISS. red in COV. 
      destruct COV as [_ [[COV|COV]|COV]].
      { apply COV. }
      all: type_solver. }
    edestruct rel_write_step; eauto.
    red. split; [split|]; auto.
    { apply ISS. }
    2: { intros COV. apply NISS. eapply w_covered_issued; eauto. by split. }
    red in ISS.
    destruct ISS as [[[_ ISS] _] _]. red in ISS.
    red. etransitivity.
    2: by apply ISS.
    unfold fwbob.
    arewrite (eq w ⊆₁ W ∩₁ Rel ∩₁ eq w).
    basic_solver.
    basic_solver 10. }
  { (* Relaxed RMW covering *)
    assert (R r) as RR.
    { apply (dom_l WF.(wf_rmwD)) in RMW. hahn_rewrite (R_ex_in_R) in RMW. apply seq_eqv_l in RMW. desf. }
    cdes TS1. desf.
    2: { red in ISS0. type_solver. }
    edestruct rlx_rmw_cover_step; eauto.
    red. split; [split|]; auto. all: apply COV. }
  (* Release RMW covering *)
  assert (R r) as RR.
  { apply (dom_l WF.(wf_rmwD)) in RMW. hahn_rewrite (R_ex_in_R) in RMW. apply seq_eqv_l in RMW. desf. }
  cdes TS1. desf.
  2: { red in ISS. type_solver. }
  edestruct rel_rmw_cover_step; eauto.
  red. split; [split|]; auto.
  all: apply COV.
Qed.

End PlainStep.