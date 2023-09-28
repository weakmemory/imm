Require Import Lia.
Require Import Classical Peano_dec ClassicalEpsilon.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt. 
Require Import Events.
Require Import Execution.

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Definition fin_exec (G: execution) :=
  set_finite (acts_set G \₁ is_init).

Definition fin_exec_full (G: execution) :=
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

  Definition acts_list: list actid :=
    filterP (acts_set G \₁ is_init)
            (proj1_sig (@constructive_indefinite_description _ _ FINDOM)).
  Lemma acts_set_findom: acts_set G \₁ is_init ≡₁ (fun e => In e acts_list).
  Proof using.
    unfold acts_list. destruct constructive_indefinite_description. simpl.
    split; intros e.
    all: rewrite in_filterP_iff; intuition. 
    apply i. apply H.
  Qed.
  Opaque acts_list.
End FinExecution. 

Lemma fin_exec_same_events G G'
      (SAME: acts_set G ≡₁ acts_set G') (FIN: fin_exec G):
  fin_exec G'.
Proof using. unfold fin_exec in *. by rewrite <- SAME. Qed.

Lemma tid_is_init_fin_helper (S: actid -> Prop) thread
      (NT: thread <> tid_init)
      (FIN: set_finite (S \₁ is_init)):
  set_finite (S ∩₁ Tid_ thread).
Proof using. 
  rewrite set_split_complete with (s := is_init).
  apply set_finite_union. split.
  { eapply set_finite_mori; [| by apply set_finite_empty].
    red. unfolder. ins. desc. vauto. by destruct x. }
  eapply set_finite_mori; [| by apply FIN].
  red. basic_solver.
Qed. 