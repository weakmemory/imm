From hahn Require Import Hahn.
Require Import Events.
Require Import Classical.
Require Import Lia.
Require Import IndefiniteDescription.

Lemma false_acyclic {A} : acyclic (∅₂ : relation A).
Proof using.
  red. rewrite ct_of_trans; [|apply transitiveI].
  all: clear; basic_solver.
Qed.

Lemma fsupp_rt_ct {A} (r : relation A)
      (FSUPP : fsupp r＊) :
  fsupp r⁺.
Proof using.
  intros y. specialize (FSUPP y).
  desf. exists findom.
  ins. apply FSUPP.
  apply rtE. now right.
Qed.

Lemma fsupp_wf_implies_fsupp_ct {A} (r : relation A)
      (WF    : well_founded r)
      (FSUPP : fsupp r) : 
  fsupp r⁺.
Proof using.
  apply fsupp_rt_ct.
  red; intros y.
  induction y as [y HH] using (well_founded_ind WF).
  specialize (FSUPP y). desf.
  set (f :=
         fun (a : A) =>
           match
             excluded_middle_informative (r a y)
           with
           | left  PF =>
               proj1_sig (constructive_indefinite_description _ (HH a PF))
           | right _  => nil
           end
      ).
  exists (y :: flat_map f findom).
  ins. apply rtE in REL. red in REL. desf.
  { red in REL. desf. auto. }
  right.
  apply ct_end in REL.
  destruct REL as [z [AA BB]].
  apply in_flat_map.
  exists z. splits.
  { now apply FSUPP. }
  subst f. ins. unfold proj1_sig. desf.
  intuition.
Qed.

Lemma fsupp_map_rel {A B} (f : B -> A)
      (FININJ : forall y, set_finite (fun x => y = f x))
      r (FSUPP : fsupp r) :
  fsupp (f ↓ r).
Proof using.
  unfolder. ins. red in FSUPP.
  specialize (FSUPP (f y)). desf.
  set (g :=
         fun (a : A) =>
           proj1_sig
             (constructive_indefinite_description _ (FININJ a))
      ).
  exists (flat_map g findom).
  ins. apply in_flat_map.
  exists (f x). splits; auto.
  subst g. unfold proj1_sig. desf.
  intuition.
Qed.

Lemma fsupp_map_rel2 {A B} (f : B -> A)
      (FSURJ : forall y, exists x, y = f x)
      r (FSUPP : fsupp (f ↓ r)) :
  fsupp r.
Proof using.
  unfolder. ins. red in FSUPP.
  unfold map_rel in *.
  destruct (FSURJ y) as [x AA]; subst.
  destruct (FSUPP x) as [l BB].
  exists (map f l).
  ins. apply in_map_iff.
  destruct (FSURJ x0) as [z CC]; subst.
  eexists; eauto.
Qed.

Lemma map_rel_seq2 {A B} {f : A -> B} r r'
      (FSURJ : forall y, exists x, y = f x) :
  f ↓ r ⨾ f ↓ r' ≡ f ↓ (r ⨾ r').
Proof using.
  split.
  { apply map_rel_seq. }
  unfolder. ins. desf.
  specialize (FSURJ z). desf.
  eauto.
Qed.

(* TODO: move to Hahn. *)
Lemma set_finite_exists_bigger {A}
      (DEC : forall x y : A, {x = y} + {x <> y})
      (s : A -> Prop) (FINDOM : set_finite s)
      (f : nat -> A)
      (INJ : forall n m (EQ : f n = f m), n = m) :
  exists n, forall m (LT : n < m), ~ s (f m).
Proof using.
  red in FINDOM. desf.
  generalize dependent s.
  induction findom; ins; eauto.
  destruct (in_dec DEC a findom) as [|NIN].
  { edestruct IHfindom with (s:=s) as [n NN]; eauto.
    ins. apply FINDOM in IN. desf. }
  edestruct IHfindom with (s:=s \₁ eq a) as [n NN].
  { unfolder. ins. desf. apply FINDOM in IN. desf. }
  destruct (classic (exists ma, f ma = a)) as [|CC]; desf.
  2: { exists n. ins. intros AA.
       apply NN in LT. apply LT. split; eauto. }
  exists (1 + max ma n). ins. intros AA.
  set (BB:=AA).
  apply FINDOM in BB. desf.
  { apply INJ in BB; subst. clear -LT. lia. }
  apply NN with (m:=m).
  { lia. }
  split; auto.
  intros HH. apply INJ in HH. desf.
Unshelve. apply 0.
Qed.

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
  apply Lt.le_lt_or_eq in H.
  destruct H as [Hl | Heq].
  { unfold lt in Hl. apply le_S_n in Hl. by apply IHn. }
  rewrite Heq. apply HPi. ins.
  apply le_S_n in H. by apply IHn.
Qed.


Tactic Notation "destruct_seq" constr(x)
       "as" "[" ident(y) ident(z) "]" :=
  apply seq_eqv_l in x; destruct x as [y x];
  apply seq_eqv_r in x; destruct x as [x z].

Tactic Notation "destruct_seq_l" constr(x)
       "as" ident(y) :=
  apply seq_eqv_l in x; destruct x as [y x].

Tactic Notation "destruct_seq_r" constr(x)
       "as" ident(y) :=
  apply seq_eqv_r in x; destruct x as [x y].

Section Props.
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Lemma ntid_tid_set_inter s thread :
  s ⊆₁ s ∩₁ NTid_ thread ∪₁ s ∩₁ Tid_ thread.
Proof using.
  ins.
  rewrite <- set_inter_union_r.
  unfolder. ins. splits; auto.
  destruct (classic (tid x = thread)); eauto.
Qed.
End Props.

Lemma dom_rel_to_cond {A} r (s t : A -> Prop) :
  dom_rel (r ⨾ ⦗t⦘) ⊆₁ s -> t ⊆₁ dom_cond r s.
Proof using.
  unfold dom_cond; unfolder.
  intro H; ins; desf; eapply H; eauto.
Qed.

Lemma dom_cond_to_rel {A} r (s t : A -> Prop) :
  t ⊆₁ dom_cond r s -> dom_rel (r ⨾ ⦗t⦘) ⊆₁ s.
Proof using.
  unfold dom_cond; unfolder.
  intro H; ins; desf; eapply H; eauto.
Qed.
