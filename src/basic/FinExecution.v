Require Import Lia.
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import AuxRel2. 
Require Import Events.
Require Import Execution.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Definition fin_exec (G: execution) :=
  set_finite (acts_set G \₁ is_init).

(* TODO: currently seems that the notion of full finiteness is needed 
   to support traversal as is *)
Definition fin_exec_full (G: execution) :=
  (* fin_exec G /\ set_finite (acts_set G ∩₁ Tid_ tid_init).  *)
  set_finite (acts_set G).

Lemma fin_exec_full_equiv (G: execution):
  fin_exec_full G <-> fin_exec G /\ set_finite (acts_set G ∩₁ is_init).
Proof using.
  unfold fin_exec, fin_exec_full.
  rewrite <- set_finite_union. apply set_finite_more. 
  rewrite set_minusE, set_unionC, <- set_inter_union_r, <- set_full_split.
  basic_solver.
Qed. 


Section FinExecution.
  Variable G: execution.

  Hypothesis FINDOM: fin_exec_full G.

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
  
End FinExecution. 

Lemma fin_exec_same_events G G'
      (SAME: acts_set G ≡₁ acts_set G') (FIN: fin_exec G):
  fin_exec G'.
Proof using. unfold fin_exec in *. by rewrite <- SAME. Qed.
