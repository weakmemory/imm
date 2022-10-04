From hahn Require Import Hahn.
Require Import AuxRel2.
Require Import AuxDef. 
Require Import Basics. 
Require Import SetSize. 
Section EnumProperties.
  Context {A: Type} (r: relation A) (f: nat -> A). 

Lemma enum_exact_steps
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  forall i d, r ^^ d (f i) (f (i + d)). 
Proof using. 
  intros. induction d. 
  { simpl. rewrite PeanoNat.Nat.add_0_r. vauto. }
  eexists. split; eauto.
  rewrite NPeano.Nat.add_succ_r, <- NPeano.Nat.add_1_r.
  apply STEPS. 
Qed.   
  
Lemma enum_steps
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  ⟪STEPS: forall i j (LT: i < j), r^+ (f i) (f j) ⟫. 
Proof using.
  red. ins. apply PeanoNat.Nat.le_exists_sub in LT. desc. subst j.
  apply ctEE. exists p. split; auto.
  rewrite NPeano.Nat.add_comm, PeanoNat.Nat.add_succ_comm.
  apply enum_exact_steps. auto. 
Qed.

Lemma enum_inj
      (STEPS: forall i, r (f i) (f (i + 1)))
      (AC: acyclic r):
  forall x y, f x = f y -> x = y. 
Proof using. 
  ins. forward eapply enum_steps as STEPS'; eauto.
  pose proof (NPeano.Nat.lt_trichotomy x y) as LT.
  des; auto;
    destruct (AC (f x)); [rewrite H at 2| rewrite H at 1]; 
    specialize (STEPS' _ _ LT); auto.
Qed. 

Lemma enumerates_set_bunion (steps: nat -> A) (S: A -> Prop)
  (ENUM: enumerates steps S):
  S ≡₁ ⋃₁ i ∈ flip NOmega.lt_nat_l (set_size S), eq (steps i).
Proof using. 
  apply enumeratesE' in ENUM. desc.
  split; unfolder; ins; desc; subst. 
  by apply INSET.
Qed.

End EnumProperties. 
