Require Import Lia.
From hahn Require Import Hahn.
Require Import Setoid.

Set Implicit Arguments.

Lemma dom_eqv_seq {A} a (r r' : relation A) (NE : exists b, r' a b) :
  dom_rel (r ⨾ ⦗eq a⦘ ) ≡₁ dom_rel (r ⨾ ⦗eq a⦘ ⨾ r').
Proof using.
  split.
  2: { rewrite <- !seqA. apply dom_seq. }
  unfolder. ins. desf. eauto.
Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_union_more.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_union A) with signature 
  set_subset ==> set_subset ==> set_subset as set_union_mori.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Lemma codom_rel_helper {A} (r : relation A) (d : A -> Prop) (HH : codom_rel r ⊆₁ d) :
  r ≡ r ⨾ ⦗d⦘.
Proof using.
  split; [|basic_solver].
  unfolder. ins. split; auto. apply HH. red. eauto.
Qed.

Lemma inter_inclusion {A : Type} (r r' : relation A) (IN : r ⊆ r') :
  r ⊆ r ∩ r'.
Proof using. basic_solver. Qed.

Lemma inter_eq {A : Type} (r r' : relation A) (EQ : r ≡ r') : r ≡ r ∩ r'.
Proof using. generalize EQ. basic_solver. Qed.

Lemma forall_not_or_exists {A} (s P : A -> Prop):
  (exists e, s e /\ P e) \/ (forall e, s e -> ~ P e).
Proof using. apply NNPP. intros X. firstorder. Qed.

Lemma tot_ext_nat_extends2 (r : relation nat) : r⁺ ⊆ tot_ext_nat r.
Proof using.
  apply inclusion_t_ind; try apply tot_ext_nat_trans.
  red; ins.
    by apply tot_ext_nat_extends.
Qed.

Lemma pair_app :
  forall (A B : Prop), A -> (A -> A /\ B) -> A /\ B.
Proof using. ins. intuition. Qed.

Theorem nat_ind_lt (P : nat -> Prop)
        (HPi : forall n, (forall m, m < n -> P m) -> P n) :
  forall n, P n.
Proof using.
  set (Q n := forall m, m <= n -> P m).
  assert (forall n, Q n) as HH.
  2: { ins. apply (HH n). lia. }
  ins. induction n.
  { unfold Q. ins. inv H. apply HPi. ins. inv H0. }
  unfold Q in *. ins.
  apply Compare_dec.le_lt_eq_dec in H.
  destruct H as [Hl | Heq].
  { unfold lt in Hl. apply le_S_n in Hl. by apply IHn. }
  rewrite Heq. apply HPi. ins.
  apply le_S_n in H. by apply IHn.
Qed.

Lemma immediate_inter_mori {A} (x y : relation A) (IN : y ⊆ x) :
  y ∩ (immediate x) ⊆ immediate y.
Proof using.
  intros e e' [HH BB].
  split; auto.
  ins. eapply BB; apply IN; eauto.
Qed.

Lemma seq_codom_dom_inter  {A} (r r' : relation A) :
  codom_rel r ∩₁ dom_rel r' ≡₁ ∅ -> r ⨾ r' ≡ ∅₂.
Proof using.
  unfold set_equiv, set_subset; ins; desf. 
  unfold same_relation; splits; [|basic_solver].
  unfold seq, inclusion. 
  intros x y [z HH]. 
  specialize (H z).
  apply H. 
  basic_solver.
Qed.

Lemma seq_codom_dom_inter_iff {A} (r r' : relation A) :
  codom_rel r ∩₁ dom_rel r' ≡₁ ∅ <-> r ⨾ r' ≡ ∅₂.
Proof using.
  ins. split.
  { by apply seq_codom_dom_inter. }
  intros AA.
  split; [|basic_solver].
  unfolder. ins. desf.
  eapply AA. eexists. eauto.
Qed.

Lemma length_nzero_in A (l : list A) n : length l = S n -> exists x, In x l.
Proof using.
  destruct l; ins; desf; eauto.
Qed.

Lemma r_to_dom_rel_r_r {A} (r: relation A) : r ≡ ⦗dom_rel r⦘ ⨾ r.
Proof using. basic_solver. Qed.

Lemma r_to_r_codom_rel_r {A} (r: relation A) : r ≡ r ⨾ ⦗codom_rel r⦘.
Proof using. basic_solver. Qed.

Lemma set_full_split {A: Type} (S: A -> Prop):
  set_full ≡₁ S ∪₁ set_compl S.
Proof using.
  split; [| basic_solver]. red. ins. destruct (classic (S x)); basic_solver.
Qed.

Lemma set_bunion_separation {A B: Type} (S: A -> Prop) (fab: A -> B):
  S ≡₁ ⋃₁ b, S ∩₁ (fun a => fab a = b).
Proof using. basic_solver. Qed.

(* TODO: move to hahn *)
Lemma clos_trans_domb_l {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb r s):
  ⦗s⦘ ⨾ r^+ ⊆ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+.
Proof using.
  erewrite (@domb_rewrite _ r) at 1; eauto.
  rewrite <- seq_eqvK at 2. rewrite <- seqA. rewrite ct_rotl.
  do 2 rewrite <- seqA. rewrite <- ct_begin. basic_solver. 
Qed.
