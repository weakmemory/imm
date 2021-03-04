From hahn Require Import Hahn.
Require Import Events.
Require Import Classical.
Require Import Lia.

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
