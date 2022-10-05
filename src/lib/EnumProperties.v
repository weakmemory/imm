From hahn Require Import Hahn.
Require Import Lia.
Require Import AuxRel2.
Require Import AuxDef. 
Require Import Basics. 
Require Import SetSize. 
Import ListNotations.

Section EnumProperties.
  Context {A: Type} (f: nat -> A). 

Lemma enum_exact_steps (r : relation A)
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  forall i d, r ^^ d (f i) (f (i + d)). 
Proof using. 
  intros. induction d. 
  { simpl. rewrite PeanoNat.Nat.add_0_r. vauto. }
  eexists. split; eauto.
  rewrite NPeano.Nat.add_succ_r, <- NPeano.Nat.add_1_r.
  apply STEPS. 
Qed.   
  
Lemma enum_steps (r : relation A)
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  ⟪STEPS: forall i j (LT: i < j), r^+ (f i) (f j) ⟫. 
Proof using.
  red. ins. apply PeanoNat.Nat.le_exists_sub in LT. desc. subst j.
  apply ctEE. exists p. split; auto.
  rewrite NPeano.Nat.add_comm, PeanoNat.Nat.add_succ_comm.
  apply enum_exact_steps. auto. 
Qed.

Lemma enum_steps_crt (r : relation A) b
  (STEPS : forall i (DOM : NOmega.lt_nat_l i b), r (f i) (f (i + 1))) :
  forall i j (LE : i <= j) (DOM : NOmega.le (NOnum j) b), r^* (f i) (f j).
Proof using.
  destruct b; ins.
  { apply Lt.le_lt_or_eq in LE as [LT | ]; subst.
    2: now apply rt_refl.
    apply inclusion_t_rt. eapply enum_steps; auto. }
  generalize dependent j.
  induction n; ins.
  { assert (i = 0) by lia; subst.
    assert (j = 0) by lia; subst.
    apply rt_refl. }
  apply Lt.le_lt_or_eq in DOM as [LT | ]; subst.
  { apply IHn; auto. lia. }
  apply Lt.le_lt_or_eq in LE as [LT | ]; subst; vauto.
  eapply rt_unit. exists (f n). split.
  { eapply IHn; auto. lia. }
  specialize (STEPS n).
  rewrite NPeano.Nat.add_comm in STEPS.
  apply STEPS. lia.
Qed.

Lemma enum_inj (r : relation A)
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

Lemma enum_steps_inv (r : relation A)
  (STEPS: forall i : nat, r (f (i + 1)) (f i)) :
  forall i j (LT : i < j), r^+ (f j) (f i).
Proof using.
  ins. fold (transp r⁺ (f i) (f j)). apply transp_ct.
  apply enum_steps; auto. 
Qed.

Lemma orders_contradiction r1 r2 (S : A -> Prop)
      (ORD1 : is_total S r1)
      (ORD2 : is_total S r2) :
  restr_rel S (r1 \ eq) ≡ restr_rel S (r2 \ eq) \/
  exists x y, S x /\ S y /\ r1 x y /\ r2 y x. 
Proof using.
  destruct (classic (restr_rel S (r1 \ eq) ≡ restr_rel S (r2 \ eq)))
    as [| NEQ]; [tauto| right]. 
  contra AGREE. destruct NEQ.
  apply same_relation_exp_iff. ins.
  destruct (classic (S x /\ S y)) as [[Sx Sy] |].
  2: { unfold restr_rel. split; ins; desc; by destruct H. }
  destruct (classic (x = y)) as [| NEQ].
  { subst. vauto. unfolder. tauto. }
  specialize (ORD1 x Sx y Sy NEQ). specialize (ORD2 x Sx y Sy NEQ).
  apply excluded_middle_or in ORD1, ORD2. 
  des; try by vauto.
  all: try by (edestruct AGREE; do 2 eexists; eauto). 
  pose proof not_ex_all_not. specialize (H _ _ AGREE).
  unfolder. tauto. 
Qed.

Lemma fsupp_dom_enum_general (r: relation A) (S: A -> Prop)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (FSUPP: fsupp (restr_rel (S ∩₁ f ↑₁ set_full) r^+))
      (INF_S': ~ set_finite (f ↓₁ S)):
  False.
Proof using.
  pose proof (proj2 (fin_dom_rel_fsupp _) FSUPP) as FSUPP'.

  forward eapply (@set_infinite_has_element _ _ INF_S')  as [ie1 Ie1].
  specialize (FSUPP' (eq (f ie1))). specialize_full FSUPP'; [by exists [f ie1]; vauto| ].

  eapply set_finite_mori in FSUPP'.
  2: { red. apply set_collect_map with (f := f). }
  apply set_finite_set_collect_inv_inj in FSUPP'.
  2: { ins. eapply enum_inj with (r := transp r); eauto.
       by apply acyclic_transp. }

  destruct INF_S'.
  rewrite <- set_inter_full_r with (s := _ ↓₁ _). 
  rewrite set_full_split with (S := ge ie1), set_inter_union_r.
  apply set_finite_union. split.
  { exists (List.seq 0 (ie1 + 1)). ins. unfolder in IN. desc. 
    apply in_seq. lia. }

  eapply set_finite_mori; [| by apply FSUPP'].
  red. red. ins. unfolder in H. desc.
  red. eexists. apply seq_eqv_r. split; eauto.
  red. splits; try by vauto.
  eapply enum_steps_inv; eauto. lia.
Qed. 

Lemma fsupp_dom_enum (r: relation A)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (FSUPP: fsupp r^+):
  False.
Proof using. 
  eapply fsupp_dom_enum_general with (S := set_full); eauto.
  { eapply fsupp_mori; eauto. red. basic_solver. }
  intros FIN. eapply set_infinite_nat.
  eapply set_finite_mori; eauto. basic_solver. 
Qed. 

Lemma fsupp_inv_inj {B: Type} (g: A -> B) (r: relation A)
      (FSUPP: fsupp (g ↑ r))
      (INJ_S: forall (x y: A) (Rx: dom_rel r x) (Ry: dom_rel r y),
          g x = g y -> x = y):
  fsupp r.
Proof using. 
  apply fin_dom_rel_fsupp. ins. 
  pose proof (proj2 (fin_dom_rel_fsupp (g ↑ r)) FSUPP).
  eapply set_finite_set_collect_inv_inj.
  2: { ins. eapply INJ_S; eauto; generalize Sx, Sy; basic_solver. }
  rewrite set_collect_dom. eapply set_finite_mori.
  { red. apply dom_rel_mori. apply collect_rel_seq. }
  rewrite collect_rel_eqv. apply H. by apply set_finite_set_collect. 
Qed.

(* TODO: rename? *)
Lemma enum_order_contradiction (r r': relation A) (S: A -> Prop)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (INF_S: ~ set_finite (f ↓₁ S))
      (TOTAL': is_total S r')
      (AC: acyclic r)
      (FS': fsupp r')
      (SEQ: r^+ ⨾ r' ⊆ r^+):
  False.
Proof using.
  forward eapply orders_contradiction with (r1 := r^+) (r2 := r') (S := S ∩₁ (f ↑₁ set_full)).  
  2: { eapply is_total_mori; eauto; [red| ]; basic_solver. }
  { red. ins. unfolder in IWa. unfolder in IWb. desc. subst. rename y0 into x.
    pose proof (NPeano.Nat.lt_trichotomy x y). 
    desf; [right | left].
    all: eapply enum_steps_inv; eauto. }

  intros [EQUIV | CYCLE].
  2: { desc. apply (AC x). apply SEQ. vauto. }

  eapply fsupp_mori in FS'.
  2: { red. etransitivity.
       { apply proj1 in EQUIV. apply EQUIV. }
       basic_solver. }

  eapply fsupp_dom_enum_general; eauto.
  eapply fsupp_mori; eauto. red.
  eapply restr_rel_mori; [reflexivity| ].
  red. ins. split; auto. intros ->. edestruct AC; eauto. 
Qed. 

End EnumProperties. 
