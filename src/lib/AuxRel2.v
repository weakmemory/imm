Require Import Lia.
From hahn Require Import Hahn.
Require Import Setoid.
Require Import SetSize.
Import ListNotations.
Require Import IndefiniteDescription.
Require Import AuxDef.

Set Implicit Arguments.

Lemma empty_ct {A} : (fun _ _ : A => False)⁺ ≡ (fun _ _ : A => False).
Proof using. rewrite ct_begin. basic_solver 10. Qed.

Lemma empty_rt {A} : (fun _ _ : A => False)＊ ≡ <|fun _ : A => True|>.
Proof using. rewrite rtE, empty_ct. rewrite union_false_r. basic_solver. Qed.

Lemma dom_eqv_seq {A} a (r r' : relation A) (NE : exists b, r' a b) :
  dom_rel (r ⨾ ⦗eq a⦘ ) ≡₁ dom_rel (r ⨾ ⦗eq a⦘ ⨾ r').
Proof using.
  split.
  2: { rewrite <- !seqA. apply dom_seq. }
  unfolder. ins. desf. eauto.
Qed.

Lemma codom_seq_eqv_r {A: Type} (r: relation A) (S: A -> Prop):
  codom_rel (r ⨾ ⦗S⦘) ⊆₁ S. 
Proof using. basic_solver. Qed.

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

Lemma clos_trans_domb_l {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb r s):
  ⦗s⦘ ⨾ r^+ ⊆ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+.
Proof using.
  erewrite (@domb_rewrite _ r) at 1; eauto.
  rewrite <- seq_eqvK at 2. rewrite <- seqA. rewrite ct_rotl.
  do 2 rewrite <- seqA. rewrite <- ct_begin. basic_solver. 
Qed.

Lemma clos_refl_trans_domb_l {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb r s):
  ⦗s⦘ ⨾ r^* ⊆ ⦗s⦘ ⨾ r^* ⨾ ⦗s⦘.
Proof using.
  rewrite <- seqA. apply domb_helper.
  rewrite rtE, seq_union_r. apply union_domb; [basic_solver| ].
  erewrite (@domb_rewrite _ r); eauto.
  rewrite ct_end. basic_solver.
Qed.

Lemma clos_trans_doma_r_strong {B: Type} (r: relation B) (s: B -> Prop)
      (DOMA_S: doma (r ⨾ ⦗s⦘) s):
   r^+ ⨾ ⦗s⦘ ≡ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+. 
Proof using.
  split.
  2: { rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r. basic_solver. }
  red. intros x y TT. apply seq_eqv_r in TT as [R'xy Sy].
  apply ctEE in R'xy as [n [_ Rnxy]].
  generalize dependent y. induction n.
  { ins. apply ct_step. apply seq_eqv_l in Rnxy as [_ Rnxy].
    apply seq_eqv_lr. splits; auto.
    eapply DOMA_S. basic_solver. }
  ins. destruct Rnxy as [z [Rnxz Rzy]]. specialize (IHn _ Rnxz).
  apply ct_unit. exists z. split; eauto.
  { apply IHn. eapply DOMA_S; eauto. basic_solver. } 
  apply seq_eqv_lr. splits; auto.
  eapply DOMA_S. basic_solver.
Qed.

Lemma clos_trans_domb_l_strong {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb (⦗s⦘ ⨾ r) s):
  ⦗s⦘ ⨾ r^+ ≡ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+. 
Proof using.
  split.
  2: { rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r. basic_solver. }
  red. intros x y TT. apply seq_eqv_l in TT as [Sx R'xy].
  apply ctEE in R'xy as [n [_ Rnxy]].
  generalize dependent y. induction n.
  { ins. apply ct_step. apply seq_eqv_l in Rnxy as [_ Rnxy].
    apply seq_eqv_lr. splits; auto.
    eapply DOMB_S. basic_solver. }
  ins. destruct Rnxy as [z [Rnxz Rzy]]. specialize (IHn _ Rnxz).
  apply ct_unit. eexists. split; eauto.
  eapply same_relation_exp in IHn.
  2: { rewrite <- restr_relE. reflexivity. }
  apply clos_trans_restrD in IHn. desc. 
  apply seq_eqv_lr. splits; auto.
  eapply DOMB_S. basic_solver.
Qed.

Lemma seq_eqv_compl {A: Type} (r: relation A) (s: A -> Prop):
  r ⨾ ⦗s⦘ ≡ ∅₂ <-> r ≡ r ⨾ ⦗set_compl s⦘.
Proof using.
  split; [basic_solver 10| ]; intros ->. basic_solver.
  Unshelve. all: eauto.
Qed.

Definition respects_rel {A: Type} (enum: nat -> A) (r: relation A) (S: A -> Prop) :=
  forall i j (DOMi: NOmega.lt_nat_l i (set_size S))
    (DOMj: NOmega.lt_nat_l j (set_size S))
    (Rij: r (enum i) (enum j)),
    i < j.

Lemma set_split_complete {A: Type} (s s': A -> Prop):
  s' ≡₁ s' ∩₁ s ∪₁ s' ∩₁ (set_compl s).
Proof using.
  rewrite <- set_inter_union_r. rewrite <- AuxRel2.set_full_split. basic_solver. 
Qed.

Lemma set_union_strict {A: Type}
      (s1 s2: A -> Prop):
  s1 ∪₁ s2 ≡₁ s1 ∪₁ s2 \₁ s1.
Proof using.
  split; [| basic_solver].
  intros x Sx. destruct (classic (s1 x)); [basic_solver| ].
  destruct Sx; [done| ]. basic_solver. 
Qed.

Lemma set_disjoint_not_eq_r {A: Type} (a : A) (s : A -> Prop):
  ~ set_disjoint s (eq a) <-> s a.
Proof using.
  pose proof (set_disjoint_eq_r a s) as EQ. apply not_iff_compat in EQ. tauto.
Qed.

Lemma set_finite_set_collect_inv_inj {A B: Type} (f: A -> B) (S: A -> Prop)
      (FIN_MAP: set_finite (f ↑₁ S))
      (INJ_S: forall (x y: A) (Sx: S x) (Sy: S y), f x = f y -> x = y):
  set_finite S.
Proof using.
  red in FIN_MAP. desc.
  rewrite AuxRel2.set_bunion_separation with (fab := f).
  rewrite AuxRel2.set_full_split with (S := (fun b => In b findom)).
  rewrite set_bunion_union_l. apply set_finite_union. split.
  2: { exists []. ins. red in IN. desc. red in IN0. desc.
       destruct IN. apply FIN_MAP. basic_solver. }
  apply set_finite_bunion.
  { by vauto. }
  intros b INb. 
  destruct (classic (exists a, S a /\ f a = b)).
  2: { exists []. ins. destruct H. exists x. apply IN. }
  desc. exists [a]. ins. unfolder in IN. desc.  left. apply INJ_S; congruence.
Qed.  

Lemma set_infinite_nat:
  ~ set_finite (@set_full nat).
Proof using.
  intros [findom FIN].
  specialize (FIN (list_max findom + 1)). specialize_full FIN; [done| ].
  forward eapply (list_max_le findom (list_max findom)) as [CONTRA _].
  specialize_full CONTRA; [lia| ].
  eapply Forall_in in CONTRA; eauto. lia.
Qed. 

Lemma set_infinite_minus_finite {A: Type} (S S': A -> Prop)
      (INF: ~ set_finite S) (FIN': set_finite S'):
  ~ set_finite (S \₁ S'). 
Proof using.
  intros [findom FIN]. destruct FIN' as [findom' FIN']. 
  destruct INF. exists (findom ++ findom'). ins. apply in_or_app.
  destruct (classic (S' x)); intuition (auto with *).
Qed.

Lemma set_infinite_bunion {A B: Type} (As: A -> Prop) (ABs: A -> B -> Prop)
      (FINa: set_finite As)
      (INF: ~ set_finite (⋃₁ a ∈ As, ABs a)):
  exists a, As a /\ ~ set_finite (ABs a).
Proof using. 
  contra FIN_ALL. destruct INF. apply set_finite_bunion; auto.
  ins. contra INF. destruct FIN_ALL. eauto.
Qed. 

Lemma fin_dom_rel_fsupp {A: Type} (r: relation A):
  (forall S (FINS: set_finite S), set_finite (dom_rel (r ⨾ ⦗S⦘))) <-> fsupp r.
Proof using.
  split. 
  2: { intros FSUPPr S FINS.  
  red in FSUPPr. apply functional_choice in FSUPPr as [supp_map FSUPPr].
  destruct FINS as [Sl DOMS]. 
  exists (concat (map supp_map Sl)).
  intros a [s DOM%seq_eqv_r]. desc.
  apply in_concat_iff. eexists. split.
  - eapply FSUPPr; eauto.
  - apply in_map. intuition. }
  ins. red. ins. 
  specialize (H (eq y)). specialize_full H; [by exists [y]; vauto|].
  destruct H as [findom FIN]. exists findom. ins. apply FIN.
  red. eexists. apply seq_eqv_r. eauto.  
Qed.

Lemma fin_dom_rel_cr_fsupp {A: Type} (r: relation A) (S: A -> Prop)
      (FIN: set_finite S) (FS: fsupp r):
  set_finite (dom_rel (r^? ⨾ ⦗S⦘)). 
Proof using. rewrite crE. relsf. split; auto. by apply fin_dom_rel_fsupp. Qed. 

Lemma set_finite_set_collect {A B: Type} (S: A -> Prop) (f: A -> B)
      (FIN: set_finite S):
  set_finite (f ↑₁ S). 
Proof using. 
  red in FIN. desc. exists (map f findom). 
  ins. apply in_map_iff. red in IN. desc. vauto.
  eexists. split; eauto. 
Qed. 

Lemma same_relation_exp_iff {A: Type} (r r': relation A):
  r ≡ r' <-> (forall x y, r x y <-> r' x y).
Proof using.
  red. split.
  { apply same_relation_exp. }
  ins. red. split.
  all: red; ins; apply H; auto.
Qed.  

Lemma pref_union_alt {A: Type} (r1 r2: relation A):
  pref_union r1 r2 ≡ r1 ∪ r2 \ (r1)⁻¹.
Proof. basic_solver. Qed.

Lemma bunion_mori_equiv {A B: Type} (As1 As2: A -> Prop) (ABB1 ABB2: A -> relation B)
  (EQA: As1 ⊆₁ As2) (EQB: forall a (AS: As1 a), ABB1 a ⊆ ABB2 a):
  (⋃ a ∈ As1, ABB1 a) ⊆ (⋃ a ∈ As2, ABB2 a). 
Proof using. 
  unfolder. ins; desc; exists a.
  splits; [apply EQA | apply EQB]; auto.
Qed.
