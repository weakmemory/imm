From hahn Require Import Hahn.

Require Import ReserveClos.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import TlsEventSets.
Require Import TraversalOrder.
Require Import TLSCoherency.
Require Import IordCoherency.
Require Import SimClosure.

Section ReserveInitClos.

Variable (G : execution).
Variable (sc : relation actid).

Definition reserve_init_clos tc := 
  (tc \₁ action ↓₁ (eq ta_reserve)) ∪₁ eq ta_reserve <*> (acts_set G ∩₁ is_init).

Add Parametric Morphism : reserve_init_clos with signature
  set_subset ==> set_subset as reserve_init_clos_mori.
Proof using.
  clear. intros a b IN.
  unfold reserve_init_clos. now rewrite IN.
Qed.

Add Parametric Morphism : reserve_init_clos with signature
  set_equiv ==> set_equiv as reserve_init_clos_more.
Proof using.
  clear. intros a b [AA BB].
  now split; [rewrite AA|rewrite BB].
Qed.

Lemma reserve_init_clos_union a b :
  reserve_init_clos (a ∪₁ b) ≡₁ reserve_init_clos a ∪₁ reserve_init_clos b.
Proof using. clear. unfold reserve_init_clos. basic_solver 10. Qed.

Lemma reserve_init_clos_init_tls : reserve_init_clos (init_tls G) ≡₁ init_tls G.
Proof using.
  clear.
  unfold reserve_init_clos, init_tls.
  rewrite !set_pair_union_l, !set_minus_union_l.
  split; unionL.
  all: try basic_solver.
  { do 4 unionR left. unfold set_pair. unfolder. ins. do 2 desf. }
  { do 3 unionR left. unfold set_pair. unfolder. ins. do 2 desf.
    right. splits; eauto. intros HH; inv HH. }
  unionR left -> right.
  unfold set_pair, is_ta_propagate_to_G. unfolder. ins. do 2 desf.
  splits; eauto. intros HH; inv HH.
Qed.
  
Lemma reserve_init_clos_tls_coherent
  tc (TCOH : tls_coherent G tc) :
  tls_coherent G (reserve_init_clos tc).
Proof using.
  destruct TCOH as [AA BB].
  unfold reserve_init_clos. constructor.
  { rewrite <- AA. unfold init_tls. clear.
    rewrite !set_pair_union_l. unfold set_pair, is_ta_propagate_to_G.
    unfolder. ins. desf; desf; ins; eauto 10.
    all: now left; split; [|intros HH; inv HH]; eauto 20. }
  unionL.
  { transitivity tc; eauto with hahn. basic_solver. }
  unionR left. unfold init_tls.
  rewrite !set_pair_union_l. eauto with hahn.
Qed.

Lemma reserve_init_clos_sim_coherent
  tc (SCOH : sim_coherent G tc) :
  sim_coherent G (reserve_init_clos tc).
Proof using.
  unfold reserve_init_clos. red.
  split.
  { unfold sim_clos. eauto with hahn. }
  unfold sim_clos.
  apply set_subset_union_l; split.
  apply set_subset_union_l; split; eauto with hahn.
  all: unionR left.
  all: rewrite set_minusE at 2.
  all: apply set_subset_inter_r; split.
  all: try now (unfold rmw_clos, rel_clos, set_pair; unfolder; ins; do 2 desf).
  all: transitivity (sim_clos G tc); try now apply SCOH.
  all: unfold sim_clos.
  1: transitivity (rmw_clos G tc); eauto with hahn.
  2: transitivity (rel_clos G tc); eauto with hahn.
  all: unfold rmw_clos, rel_clos.
  all: apply set_pair_mori; eauto with hahn.
  all: autorewrite with cir_simplify.
  all: clear; basic_solver.
Qed.

Lemma reserve_init_clos_sim_clos_step_rt :
  sim_clos_step G sc ⊆ reserve_init_clos ↓ (sim_clos_step G sc)^?.
Proof using.
  clear.
  intros tc tc' STEP. red.
  clear -STEP.
  destruct STEP as [[tll STEP] [SCOH SCOH']].
  unfold reserve_init_clos.
  eapply isim_clos_step_fixed_reserve in STEP.
  { destruct STEP as [EQ|STEP]; [now left; apply EQ|right].
    split.
    2: now split; apply reserve_init_clos_sim_coherent.
    exists tll; auto. }
  unfold set_pair. unfolder. ins. do 2 desf.
Qed.

Lemma reserve_init_clos_sim_clos_steps_rt :
  (sim_clos_step G sc)^* ⊆ reserve_init_clos ↓ (sim_clos_step G sc)^*.
Proof using.
  clear.
  rewrite reserve_init_clos_sim_clos_step_rt at 1.
  rewrite map_rel_crt.
  now rewrite rt_of_cr.
Qed.

End ReserveInitClos.