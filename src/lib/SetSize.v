(* Require Import AuxProp. *)
Require Import IndefiniteDescription.
Require Import PropExtensionality.
From hahn Require Import Hahn.
Require Import ClassicalDescription.
Require Import Lia.
Require Import Arith.

Definition set_size {A: Type} (S: A -> Prop): nat_omega :=
  match (excluded_middle_informative (set_finite S)) with
  | left FIN => (NOnum (length (undup (filterP S (proj1_sig (constructive_indefinite_description _ FIN))))))
  | right _ => NOinfinity
  end. 

Lemma lt_size_of_finite A (s : A -> Prop) d
      (SUB: forall x, s x -> In x d) n :
  lt_size n s <-> n < length (undup (filterP s d)).
Proof using.
  unfold lt_size; split; ins; desf.
    eapply lt_le_trans, NoDup_incl_length; unfold incl; eauto.
    ins; rewrite in_undup_iff, in_filterP_iff; desf; eauto.
    exists (undup (filterP s d)); splits; ins.
    rewrite in_undup_iff, in_filterP_iff in *; desf; eauto.
Qed.

Lemma set_lt_size {A: Type} (S: A -> Prop) i:
  NOmega.lt_nat_l i (set_size S) <-> lt_size i S.
Proof using.
  unfold set_size. destruct (excluded_middle_informative _).
  2: { simpl. split; auto. ins. by apply lt_size_infinite. }
  destruct (constructive_indefinite_description _).
  simpl. symmetry. by apply lt_size_of_finite.
Qed. 

Lemma enumeratesE' {A : Type} (f : nat -> A) (s : A -> Prop):
  enumerates f s <->
  let dom := fun i => NOmega.lt_nat_l i (set_size s) in
  ⟪INSET: forall i : nat, dom i -> s (f i)⟫ /\
  ⟪INJ: forall i : nat, dom i -> forall j : nat, dom j -> f i = f j -> i = j⟫ /\
  ⟪IND: forall a : A, s a -> exists i : nat, dom i /\ f i = a⟫.
Proof using.
  etransitivity.
  { apply enumeratesE. }
  pose proof (set_lt_size s) as EQUIV. 
  split.
  { ins. desc. splits; ins.
    { by apply RNG, EQUIV. }
    { by apply INJ; [apply EQUIV | apply EQUIV| apply H1]. }
    { apply SUR in H. desc. exists i. split; auto. by apply EQUIV. }
  }
  { ins. desc. splits; ins. 
    { by apply INSET, EQUIV. }
    { by apply INJ; [apply EQUIV | apply EQUIV| ]. }
    { apply IND in IN. desc. exists i. split; auto. by apply EQUIV. }
  }
Qed.

Lemma set_size_equiv {A: Type} (S1 S2: A -> Prop) (EQ: S1 ≡₁ S2):
  set_size S1 = set_size S2.
Proof using.
  cut (S1 = S2); [congruence| ].  
  extensionality a. apply propositional_extensionality.
  by apply set_equiv_exp. 
Qed. 

Lemma set_size_empty {A: Type} (s: A -> Prop):
  set_size s = NOnum 0 <-> s ≡₁ ∅.
Proof.
  split; intros. 
  { unfold set_size in H. destruct excluded_middle_informative; try by vauto.
    destruct constructive_indefinite_description. simpl in *.
    inversion H. apply length_zero_iff_nil in H1.
    destruct (classic (s ≡₁ ∅)) as [? | NEMPTY]; auto. 
    apply set_nonemptyE in NEMPTY. desc.
    specialize (i _ NEMPTY).
    assert (In x0 nil); [| by vauto].
    rewrite <- H1. apply in_undup_iff. apply in_filterP_iff. auto. }
  erewrite set_size_equiv; eauto.
  unfold set_size. destruct excluded_middle_informative.
  2: { destruct n. by exists nil. }
  f_equal. destruct constructive_indefinite_description. simpl in *.
  rewrite (proj2 (filterP_eq_nil ∅ x)); vauto.
Qed. 

