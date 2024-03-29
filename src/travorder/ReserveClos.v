Require Import Lia.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Events.
Require Import Execution.
Require Import imm_s.
Require Import TlsEventSets.
Require Import TraversalOrder.
Require Import TLSCoherency.
Require Import IordCoherency.

Set Implicit Arguments.

Section ReserveClos.
Definition reserve_clos tc := tc ∪₁ eq ta_reserve <*> (issued tc).

Global Add Parametric Morphism : reserve_clos with signature
    set_subset ==> set_subset as reserve_clos_mori.
Proof using.
  intros x y HH. unfold reserve_clos. rewrite HH.
  clear. basic_solver.
Qed. 

Global Add Parametric Morphism : reserve_clos with signature
    set_equiv ==> set_equiv as reserve_clos_more.
Proof using.
  intros x y [HH AA]. split.
  { now rewrite HH. }
  now rewrite AA.
Qed. 

Lemma reserve_clos_union s s' :
  reserve_clos (s ∪₁ s') ≡₁ reserve_clos s ∪₁ reserve_clos s'.
Proof using.
  unfold reserve_clos.
  rewrite !issued_union.
  rewrite set_pair_union_r.
  clear. basic_solver 10.
Qed.

Variable G : execution.
Variable sc : relation actid.
Hypothesis WF : Wf G.
Hypothesis WFSC : wf_sc G sc.
Notation "'E'" := (acts_set G).
Notation "'W'" := (fun x => is_true (is_w (lab G) x)).

Lemma reserve_clos_iord_coherent tc
  (ICOH : iord_coherent G sc tc) :
  iord_coherent G sc (reserve_clos tc).
Proof using.
  unfold reserve_clos.
  red. rewrite id_union, seq_union_r, dom_union.
  unionL.
  { now unionR left. }
  transitivity (@set_empty trav_label).
  2: clear; basic_solver.
  rewrite iord_no_reserve.
  unfold set_pair.
  unfolder. ins. do 2 desf.
Qed.

Lemma reserve_clos_tls_coherent tc
  (COH : tls_coherent G tc) :
  tls_coherent G (reserve_clos tc).
Proof using WF.
  unfold reserve_clos.
  apply tls_coherent_ext_union; auto.
  unfold exec_tls.
  arewrite (issued tc ≡₁ issued tc ∩₁ (is_init ∪₁ set_compl is_init)).
  { now rewrite <- set_full_split, set_inter_full_r. }
  rewrite issued_EW; eauto.
  rewrite !set_inter_union_r, set_pair_union_r.
  unionL.
  { transitivity (init_tls G); eauto with hahn.
    unfold init_tls. apply set_pair_mori; eauto with hahn.
    clear. basic_solver. }
  unionR right -> right.
  apply set_pair_mori; eauto with hahn.
  clear. basic_solver.
Qed.

Lemma covered_reserve_clos tc : covered (reserve_clos tc) ≡₁ covered tc.
Proof using.
  ins. unfold reserve_clos. rewrite covered_union, covered_ta_reserve.
  now rewrite set_union_empty_r.
Qed.

Lemma issued_reserve_clos tc : issued (reserve_clos tc) ≡₁ issued tc.
Proof using.
  ins. unfold reserve_clos. rewrite issued_union, issued_ta_reserve.
  now rewrite set_union_empty_r.
Qed.

Lemma reserved_reserve_clos tc : reserved (reserve_clos tc) ≡₁ reserved tc ∪₁ issued tc.
Proof using.
  ins. unfold reserve_clos.
  now rewrite reserved_union, reserved_ta_reserve.
Qed.

Lemma reserve_clos_eq_ta_cover w : reserve_clos (eq (ta_cover, w)) ≡₁ eq (ta_cover, w).
Proof using.
  ins. unfold reserve_clos. rewrite issued_eq_ta_cover.
  unfold set_pair. unfolder. split; ins; do 2 desf; eauto.
Qed.

Lemma reserve_clos_eq_ta_issue w : reserve_clos (eq (ta_issue, w)) ≡₁ eq (ta_issue, w) ∪₁ eq (ta_reserve, w).
Proof using.
  ins. unfold reserve_clos. rewrite issued_singleton.
  apply set_union_more; eauto with hahn.
  now rewrite set_pair_exact.
Qed.

Lemma reserve_clos_eq_ta_reserve w : reserve_clos (eq (ta_reserve, w)) ≡₁ eq (ta_reserve, w).
Proof using.
  ins. unfold reserve_clos. rewrite issued_eq_ta_reserve.
  unfold set_pair. unfolder. split; ins; do 2 desf; eauto.
Qed.

Lemma reserve_clos_mon tc : tc ⊆₁ reserve_clos tc.
Proof using. unfold reserve_clos. eauto with hahn. Qed.

Lemma reserve_clos_init_tls : reserve_clos (init_tls G) ≡₁ init_tls G.
Proof using.
  split; auto using reserve_clos_mon.
  unfold reserve_clos. unionL; eauto with hahn.
  unfold init_tls at 1. 
  rewrite !set_pair_union_l, !issued_union.
  rewrite !issued_ta_reserve, !issued_ta_issue, !issued_ta_cover,
          !issued_is_ta_propagate_to_G.
  rewrite !set_union_empty_l, !set_union_empty_r.
  unfold init_tls. rewrite !set_pair_union_l. eauto with hahn.
Qed.

Lemma reserve_clos_ta_reserve s :
  reserve_clos (eq ta_reserve <*> s) ≡₁ eq ta_reserve <*> s.
Proof using.
  unfold reserve_clos. now autorewrite with cir_simplify.
Qed.

End ReserveClos.

#[export]
Hint Rewrite reserve_clos_eq_ta_cover reserve_clos_eq_ta_issue
             reserve_clos_eq_ta_reserve
             reserve_clos_union
             reserved_reserve_clos
             issued_reserve_clos 
             covered_reserve_clos 
             reserve_clos_init_tls
             reserve_clos_ta_reserve
             : cir_simplify.