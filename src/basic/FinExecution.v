Require Import Lia.
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import FairExecution.

Section FinExecution.
  Variable G: execution.

  Hypothesis FINDOM: set_finite (acts_set G).

  Lemma exists_nE thread :
    exists n, ~ acts_set G (ThreadEvent thread n).
  Proof using FINDOM.
    set (AA:=FINDOM).
    apply set_finite_exists_bigger with (f:=ThreadEvent thread) in AA.
    3: { ins. desf. }
    2: { apply eq_dec_actid. }
    desf.
    exists (1 + n). apply AA. lia.
  Qed.

  Lemma fin_exec_fair (WF: Wf G):
    mem_fair G.
  Proof using FINDOM.
    red. rewrite wf_coE, wf_frE; eauto.
    destruct FINDOM as [findom FIN]. 
    split; red; intros; exists findom; basic_solver.
  Qed. 
End FinExecution. 
