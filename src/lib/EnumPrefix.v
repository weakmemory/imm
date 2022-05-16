From hahn Require Import Hahn.
Require Import AuxRel2.
Require Import AuxDef. 
Require Import SetSize. 
Require Import Lia. 

Section EnumPrefix.
Context {A: Type}. 
Variable (steps: nat -> A).
Variable (r: relation A).
Variable (dom: A -> Prop).
Hypothesis (R_DOM: r ⊆ dom × dom).
Hypothesis (ENUM: enumerates steps dom).
Hypothesis (RESP: respects_rel steps r⁺ dom).

Definition trav_prefix (i: nat) : A -> Prop :=
  ⋃₁ j < i, eq (steps j).

Lemma trav_prefix_rel_closed i (DOMi: NOmega.le (NOnum i) (set_size dom)):
  dom_rel (r⁺ ⨾ ⦗trav_prefix i⦘) ⊆₁ trav_prefix i.
Proof using ENUM RESP R_DOM.
  unfold trav_prefix. 
  red. intros e' [e DOMe']. apply seq_eqv_r in DOMe' as [REL ENUMe].
  red in ENUMe. destruct ENUMe as [j [LTji STEPje]].
  apply enumeratesE' in ENUM. cdes ENUM.
  specialize (IND e'). specialize_full IND.
  { eapply clos_trans_more in REL.
    2: { symmetry. apply dom_helper_3. eauto. }
    apply ct_begin in REL. generalize REL. clear. basic_solver. }
  
  destruct IND as [k [DOMk STEPke']].
  red. exists k. splits; eauto.      
  etransitivity; [| apply LTji].
  red in RESP. apply RESP with (j := j); eauto.
  2: congruence.
  liaW (set_size dom). 
Qed. 

Lemma prefix_border i (DOMi: NOmega.lt_nat_l i (set_size dom)):
  ~ trav_prefix i (steps i).
Proof using ENUM.
  unfold trav_prefix. intros [j [LT EQ]]. 
  apply enumeratesE' in ENUM. cdes ENUM.
  forward eapply INJ; [| | apply EQ| lia]; auto. 
  eapply NOmega.lt_lt_nat; eauto.
Qed.

Lemma step_event_dom i (DOMi: NOmega.lt_nat_l i (set_size dom)):
  dom (steps i). 
Proof using ENUM.
  apply enumeratesE' in ENUM. cdes ENUM.
  specialize_full INSET; eauto. 
Qed.       

Lemma trav_prefix_ext i
      (DOMi: NOmega.lt_nat_l i (set_size dom)):
  trav_prefix (S i) ≡₁ trav_prefix i ∪₁ eq (steps i).
Proof using. 
  unfold trav_prefix.
  arewrite ((fun x => x < S i) ≡₁ (fun x => x < i) ∪₁ eq i).
  { unfolder. split; ins; lia. }
  rewrite set_bunion_union_l. basic_solver.
Qed.

Lemma trav_prefix_init:
  trav_prefix 0 ≡₁ ∅. 
Proof using.
  unfold trav_prefix. apply set_subset_empty_r, set_subset_bunion_l.
  ins. lia. 
Qed.

Lemma trav_prefix_r_closed 
      (i : nat) (DOMi: NOmega.le (NOnum i) (set_size dom)):
  dom_rel (r ⨾ ⦗trav_prefix i⦘) ⊆₁ trav_prefix i.
Proof using RESP ENUM R_DOM.
  induction i.
  { rewrite trav_prefix_init. red. basic_solver. }
  rewrite trav_prefix_ext; eauto. 
  rewrite id_union, seq_union_r, dom_union.
  apply set_subset_union_l. split. 
  { rewrite IHi; [basic_solver| ]. liaW (set_size dom). }
  red. intros tlj. intros [tli R%seq_eqv_r]. desc.
  apply dom_helper_3 in R_DOM.
  apply R_DOM, seq_eqv_lr in R as (Dj & Rji & Di).  
  apply enumeratesE' in ENUM. cdes ENUM.
  apply IND in Dj, Di. desc. rename i1 into j.
  assert (i0 = i) as -> by (apply INJ; auto; congruence).
  subst. 
  pose proof (NPeano.Nat.lt_total i j) as LT. des; revgoals. 
  { left. red. vauto. }
  { subst. basic_solver. }
  (* TODO: is the last tactic needed? *)
  enough (j < i); [lia| ]. eapply RESP; eauto; try by apply ct_step.
Qed.

Lemma trav_prefix_in_dom i
      (DOMi: NOmega.le (NOnum i) (set_size dom)):
  trav_prefix i ⊆₁ dom. 
Proof using ENUM. 
  apply enumeratesE' in ENUM. cdes ENUM. 
  unfold trav_prefix. apply set_subset_bunion_l. intros.
  apply set_subset_single_l. apply INSET.
  liaW (set_size dom). 
Qed.

End EnumPrefix.
