Require Import RelationClasses List Lia.
From PromisingLib Require Import Basic.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.

Set Implicit Arguments.

Section XACQ.

Definition rmw_is_xacq_instr (i : Instr.t) :=
  match i with
  | Instr.update _ _ Xpln _ _  _ _ => False
  | _ => True
  end.

Definition rmw_is_xacq_instrs (il : list Instr.t) :=
  forall (i : Instr.t) (IN : In i il), rmw_is_xacq_instr i.

Definition w_ex_is_xacq s :=
  W_ex (ProgToExecution.G s) ⊆₁
  W_ex (ProgToExecution.G s) ∩₁ is_xacq (lab (ProgToExecution.G s)).

Lemma w_ex_is_xacq_add_preserves thread s s'
      (WF : wf_thread_state thread s) lbl vl lc cl ff
      (UG : G s' =
            add (G s) thread (eindex s) lbl vl lc cl ff) 
      (SS : w_ex_is_xacq s) :
    w_ex_is_xacq s'.
Proof using.
  unfold w_ex_is_xacq in *.
  apply set_subset_inter_r. split; [done|].
  unfold W_ex in *.
  unfold add in UG. rewrite UG at 1. simpls.
  rewrite SS. rewrite (dom_r (wft_rmwE WF)).
  rewrite codom_eqv1. rewrite set_interA.
  unfolder. ins. desc.
  unfold is_xacq, xmod. erewrite add_preserves_lab; eauto.
Qed.

Lemma w_ex_is_xacq_add_rmw_preserves thread s s'
      (WF : wf_thread_state thread s) lbl1 ordw vl lc vl' lc' cl ff
      (UG : G s' =
            add_rmw (G s) thread (eindex s) lbl1
                    (Astore Xacq ordw vl lc) vl' lc' cl ff) 
      (SS : w_ex_is_xacq s) :
    w_ex_is_xacq s'.
Proof using.
  unfold w_ex_is_xacq in *.
  apply set_subset_inter_r. split; [done|].
  unfold W_ex in *.
  unfold add_rmw in UG. rewrite UG at 1. simpls.
  rewrite codom_union. unionL.
  2: { rewrite SS. rewrite (dom_r (wft_rmwE WF)).
       rewrite codom_eqv1. rewrite set_interA.
       unfolder. ins. desc.
       unfold is_xacq, xmod. erewrite add_rmw_preserves_lab; eauto. }
  subst. unfolder. ins. desf.
  rewrite UG. simpls. unfold is_xacq, xmod. by rewrite upds.
Qed.

Lemma rmw_is_xacq_instr_xmod rmw rexmod xmod ordr ordw reg lexpr s
      (XACQIN : rmw_is_xacq_instrs (instrs s))
      (ISTEP :
         Some
           (Instr.update rmw rexmod xmod ordr ordw reg
                         lexpr) = nth_error (instrs s) (pc s)) :
  xmod = Xacq.
Proof using.
  symmetry in ISTEP; apply nth_error_In in ISTEP.
  apply XACQIN in ISTEP; simpls; desf.
Qed.

Lemma w_ex_is_xacq_thread_step thread s s'
      (XACQIN : rmw_is_xacq_instrs (instrs s))
      (WF : wf_thread_state thread s)
      (STEP : step thread s s')
      (SS : w_ex_is_xacq s) :
  w_ex_is_xacq s'.
Proof using.
  unfold w_ex_is_xacq in *.
  destruct STEP as [ll STEP]. cdes STEP.
  destruct ISTEP0.
  1,2: by rewrite UG.
  1-4: by eapply w_ex_is_xacq_add_preserves; eauto.
  all: assert (xmod = Xacq); subst;
    [ |eapply w_ex_is_xacq_add_rmw_preserves; eauto].
  all: eapply rmw_is_xacq_instr_xmod; eauto.
Qed.

End XACQ.

Section REX.

Definition rmw_is_rex_instr (i : Instr.t) : Prop :=
  match i with
  | Instr.update _ false _ _ _ _ _ => False
  | _ => True
  end.

Definition rmw_is_rex_instrs (il : list Instr.t) :=
  forall (i : Instr.t) (IN : In i il), rmw_is_rex_instr i.

Definition dom_rmw_in_rex s :=
  dom_rel (rmw (ProgToExecution.G s)) ⊆₁ R_ex (lab (ProgToExecution.G s)).

Lemma dom_rmw_in_rex_add_preserves thread s s'
      (WF : wf_thread_state thread s) lbl vl lc cl ff
      (UG : G s' =
            add (G s) thread (eindex s) lbl vl lc cl ff) 
      (SS : dom_rmw_in_rex s) :
    dom_rmw_in_rex s'.
Proof using.
  unfold dom_rmw_in_rex in *.
  unfold add in UG. rewrite UG. simpls.
  rewrite (dom_l (wft_rmwE WF)). rewrite dom_eqv1.
  rewrite SS.
  unfold R_ex. unfolder. ins. desc.
  rewrite updo; auto.
  intros HH; subst. apply (acts_rep WF) in H. desf. lia.
Qed.

Lemma dom_rmw_in_rex_add_rmw_preserves thread s s'
      (WF : wf_thread_state thread s) lbl1 rexmod ordw vl lc vl' lc' cl ff
      (UG : G s' =
            add_rmw (G s) thread (eindex s) (Aload rexmod ordw vl lc)
                    lbl1 vl' lc' cl ff) 
      (REX : rexmod = true)
      (SS : dom_rmw_in_rex s) :
    dom_rmw_in_rex s'.
Proof using.
  unfold dom_rmw_in_rex, R_ex in *.
  unfold add_rmw in UG. rewrite UG. simpls.
  rewrite dom_union. unionL.
  2: { rewrite (dom_l (wft_rmwE WF)). rewrite dom_eqv1.
       unfolder. ins. desc.
       rewrite !updo; auto.
       { apply SS. red. eauto. }
       all: intros HH; subst.
       all: apply (acts_rep WF) in H; desf; lia. }
  unfolder. ins. desc; subst.
  rewrite updo.
  { by rewrite upds. }
  intros HH. inv HH. lia.
Qed.

Lemma rmw_is_rex_instr_rexmod rmw rexmod xmod ordr ordw reg lexpr s
      (RMWREX : rmw_is_rex_instrs (instrs s))
      (ISTEP :
         Some
           (Instr.update rmw rexmod xmod ordr ordw reg
                         lexpr) = nth_error (instrs s) (pc s)) :
  rexmod = true.
Proof using.
  symmetry in ISTEP; apply nth_error_In in ISTEP.
  apply RMWREX in ISTEP; simpls; desf.
Qed.

Lemma dom_rmw_in_rex_thread_step thread s s'
      (RMWREX : rmw_is_rex_instrs (instrs s))
      (WF : wf_thread_state thread s)
      (STEP : step thread s s')
      (SS : dom_rmw_in_rex s) :
  dom_rmw_in_rex s'.
Proof using.
  unfold dom_rmw_in_rex in *.
  destruct STEP as [ll STEP]. cdes STEP.
  destruct ISTEP0.
  1,2: by rewrite UG.
  1-4: by eapply dom_rmw_in_rex_add_preserves; eauto.
  all: eapply dom_rmw_in_rex_add_rmw_preserves; eauto.
  all: rewrite II in ISTEP.
  all: eapply rmw_is_rex_instr_rexmod; eauto.
Qed.

End REX.

Section CASREX.

Definition cas_produces_R_ex_instr (i : Instr.t) : Prop :=
  match i with
  | Instr.update (Instr.cas _ _) false _ _ _ _ _ => False
  | _ => True
  end.

Definition cas_produces_R_ex_instrs (il : list Instr.t) :=
  forall (i : Instr.t) (IN : In i il), cas_produces_R_ex_instr i.

Lemma cas_produces_R_ex_instr_rexmod old new rexmod xmod ordr ordw reg lexpr s
      (RMWREX : cas_produces_R_ex_instrs (instrs s))
      (ISTEP :
         Some
           (Instr.update (Instr.cas old new) rexmod xmod ordr ordw reg
                         lexpr) = nth_error (instrs s) (pc s)) :
  rexmod = true.
Proof using.
  symmetry in ISTEP; apply nth_error_In in ISTEP.
  apply RMWREX in ISTEP; simpls; desf.
Qed.

End CASREX.
