From hahn Require Import Hahn.
Require Import Events.
Require Import Classical.

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
Proof.
  ins.
  rewrite <- set_inter_union_r.
  unfolder. ins. splits; auto.
  destruct (classic (tid x = thread)); eauto.
Qed.
End Props.

Lemma dom_rel_to_cond {A} r (s t : A -> Prop) :
  dom_rel (r ⨾ ⦗t⦘) ⊆₁ s -> t ⊆₁ dom_cond r s.
Proof.
  unfold dom_cond; unfolder.
  intro H; ins; desf; eapply H; eauto.
Qed.

Lemma dom_cond_to_rel {A} r (s t : A -> Prop) :
  t ⊆₁ dom_cond r s -> dom_rel (r ⨾ ⦗t⦘) ⊆₁ s.
Proof.
  unfold dom_cond; unfolder.
  intro H; ins; desf; eapply H; eauto.
Qed.
