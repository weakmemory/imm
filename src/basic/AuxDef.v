From hahn Require Import Hahn.
Require Import Classical.
Require Import Lia.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
From ZornsLemma Require Classical_Wf. 
Require Import Events.

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
  apply i. splits; auto.
Qed.

Lemma fsupp_dom_map_rel {A B} (f : B -> A)
      r (FSUPP : fsupp r) 
      (FININJ : forall y, set_finite (fun x => y = f x /\ dom_rel r y)) :
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
  apply i. splits; auto.
  red; eauto.
Qed.

Lemma fsupp_seq_l_map_rel {A B} (f : B -> A) (s : B -> Prop)
      r (FSUPP : fsupp r)
      (FININJ : forall y, set_finite (fun x => y = f x /\ s x)) :
  fsupp (<|s|> ;; (f ↓ r)).
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
  desf.
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


Lemma set_map_codom_ext {A B : Type} (f : A -> B) (rr : relation B)
      (SUR: forall b, exists a, f a = b):
  codom_rel (f ↓ rr) ≡₁ f ↓₁ codom_rel rr. 
Proof using. 
  split; [apply set_map_codom| ].
  unfolder. ins. desc. specialize (SUR x0). desc.
  exists a. congruence. 
Qed.  


Ltac contra name := 
  match goal with
  | |- ?goal => destruct (classic goal) as [? | name]; [done| exfalso]
  end. 

(* TODO: move to Hahn. *)
Lemma set_infinite_has_element {A: Type} (S: A -> Prop)
      (INF: ~ set_finite S):
  exists e, S e.
Proof using. contra NO. destruct INF. exists nil. ins. edestruct NO; vauto. Qed. 

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

Lemma set_extensionality {A} (s s' : A -> Prop)
      (IN : s ≡₁ s') :
  s = s'.
Proof using.
  ins; extensionality x.
  apply propositional_extensionality.
  split; apply IN.
Qed.

Lemma eqv_rel_alt {A: Type} (S: A -> Prop):
  ⦗S⦘ ≡ S × S ∩ eq.
Proof using. basic_solver. Qed.

Lemma doma_alt {A: Type} (r: relation A) (d: A -> Prop):
  doma r d <-> dom_rel r ⊆₁ d. 
Proof using. unfolder. split; ins; basic_solver. Qed. 

Lemma map_rel_seq_insert_exact {A B: Type} (r1 r2: relation B)
      (f: A -> B) (d: A -> Prop)
      (SUR_D: forall b, exists a, f a = b /\ d a):
  f ↓ (r1 ⨾ r2) ⊆ f ↓ r1 ⨾ ⦗d⦘ ⨾ f ↓ r2. 
Proof using.
  unfolder. ins. desc.
  specialize (SUR_D z). desc. eexists. splits; eauto; congruence. 
Qed. 


Lemma rel_map_bunionC {A B C: Type} (f: A -> B)
      (cdom: C -> Prop) (ss: C -> relation B):
  f ↓ (⋃ c ∈ cdom, ss c) ≡ (⋃ c ∈ cdom, f ↓ (ss c)).
Proof using. basic_solver. Qed. 

Lemma dom_rel_bunion {B C: Type}
      (cdom: C -> Prop) (ss: C -> relation B):
  dom_rel (⋃ c ∈ cdom, ss c) ≡₁ (⋃₁ c ∈ cdom, dom_rel (ss c)).
Proof using. basic_solver. Qed.

Lemma restr_rel_seq_same {A: Type} (r1 r2: relation A) (d: A -> Prop)
      (DOMB1: domb (⦗d⦘ ⨾ r1) d):
  restr_rel d (r1 ⨾ r2) ≡ restr_rel d r1 ⨾ restr_rel d r2. 
Proof using.
  split; [| apply restr_seq].
  unfolder. unfolder in DOMB1. ins. desc.
  eexists. splits; eauto.
Qed. 

Lemma set_subset_inter_exact {A: Type} (s s': A -> Prop):
  s ⊆₁ s' <-> s ⊆₁ s ∩₁ s'. 
Proof using.
  split; [basic_solver| ]. ins.
  red. ins. by apply H. 
Qed.  

Lemma set_collect_map_ext [A B : Type] [f : A -> B] [d : B -> Prop]
      (SUR: forall b, exists a, f a = b):
  f ↑₁ (f ↓₁ d) ≡₁ d. 
Proof using.
  ins. split; [apply set_collect_map| ]. 
  unfolder. ins.
  specialize (SUR x) as [a Fa]. exists a. split; congruence. 
Qed.
 
Lemma restr_rel_cross_inter {A: Type} (d1 d2 d: A -> Prop):
  (d1 ∩₁ d) × (d2 ∩₁ d) ≡ restr_rel d (d1 × d2).
Proof using. basic_solver. Qed. 

Global Add Parametric Morphism
       {A: Type} (r: relation (A -> Prop)):
  r with signature
       @set_equiv A ==> @set_equiv A ==> iff as set_equiv_rel_more. 
Proof using. ins. apply set_extensionality in H, H0. by subst. Qed.


Lemma functional_codom {A: Type} (r: relation A) (a: A)
      (FUN: functional r)
      (DOMa: dom_rel r a):
  exists a', codom_rel (⦗eq a⦘ ⨾ r) ≡₁ eq a'.
Proof using.
  destruct DOMa as [a' Raa']. exists a'. split; [| basic_solver].  
  intros x [a_ Ra_x%seq_eqv_l]. desc. subst.
  eapply FUN; eauto.
Qed.

Lemma set_eq_helper {A: Type} (s1 s2: A -> Prop) (EQ: s1 = s2):
  s1 ≡₁ s2.
Proof using. by rewrite EQ. Qed.

Lemma set_minus_disjoint {A: Type} (s1 s2: A -> Prop)
      (DISJ: set_disjoint s1 s2):
  s1 \₁ s2 ≡₁ s1.
Proof using. basic_solver. Qed.

Definition set_pair {A B} (s : A -> Prop) (t : B -> Prop) : A * B -> Prop := 
  fun ab =>
    match ab with
    | (a, b) => s a /\ t b
    end.
Global Notation "s <*> t" := (set_pair s t) (at level 40, left associativity).

Lemma set_pair_alt {A B: Type} (Sa: A -> Prop) (Sb: B -> Prop ):
  Sa <*> Sb ≡₁ (fst ↓₁ Sa) ∩₁ (snd ↓₁ Sb). 
Proof using. unfold set_pair. basic_solver. Qed.

Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_equiv A ==> @set_equiv B ==> @set_equiv (A * B) as set_pair_more.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_subset A ==> @set_subset B ==> @set_subset (A * B) as set_pair_mori.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

Lemma acyclic_transp {A: Type} (r: relation A)
      (AC: acyclic r):
  acyclic (transp r). 
Proof using. red. rewrite <- transp_ct. vauto. Qed.   

Lemma not_wf_inf_decr_enum {A: Type} (r: relation A)
      (NWF: ~ well_founded r):
  exists (f: nat -> A), forall i, r (f (i + 1)) (f i).
Proof using.
  contra DECR. destruct NWF.
  apply Classical_Wf.DSP_implies_WF. red. apply not_ex_not_all. 
  intros [f DECR']. destruct DECR. exists f.
  ins. contra Nri. destruct DECR'. exists i. by rewrite <- PeanoNat.Nat.add_1_r. 
Qed. 

Lemma In_gt_list_max (l: list nat) (n: nat)
      (GT_MAX: n > list_max l):
  ~ In n l. 
Proof using.
  intros IN.
  forward eapply (list_max_le l (list_max l)) as [IMPL _].
  specialize_full IMPL; [lia| ].
  eapply Forall_in in IMPL; eauto. lia.
Qed.  

Lemma excluded_middle_or (A B: Prop)
      (OR: A \/ B):
  A \/ (~ A) /\ B.
Proof using. tauto. Qed. 

Ltac liaW no := destruct no; [done| ins; lia]. 

Lemma dom_cond_alt {A : Type} (r : relation A) (d : A -> Prop):
  dom_cond r d ≡₁ (⋃₁ e ∈ (fun e_ => dom_rel (r ⨾ ⦗eq e_⦘) ⊆₁ d), eq e).
Proof using. unfold dom_cond. basic_solver 10. Qed. 

Lemma dom_rel_union_r1 {A: Type} (S1 S2: A -> Prop) (r: relation A)
      (NOR2: ⦗S2⦘ ⨾ r ⊆ ∅₂)
      (DOM: dom_rel r ⊆₁ S1 ∪₁ S2):
  dom_rel r ⊆₁ S1. 
Proof using. 
  red. intros x D.
  specialize (@DOM x D). destruct DOM; auto.
  red in D. desc. 
  edestruct NOR2; basic_solver 10.
Qed.   
