From hahn Require Import Hahn.
Require Import Program.Basics.
Require Import PropExtensionality.
From imm Require Import AuxDef.
Require Import IndefiniteDescription. 
Require Import Setoid.

Set Implicit Arguments.
Local Open Scope program_scope.

Section AuxRel.

  Definition eq_opt {A : Type} (a: option A) : A -> Prop := 
    fun b => 
      match a with
      | None => False
      | Some a => eq a b
      end.
  
  Definition compl_rel {A : Type} (r : relation A) : relation A := 
    fun a b => ~ r a b.

  Definition inj_dom {A B : Type} (s : A -> Prop) (f : A -> B) := 
    forall (x y : A) (SX : s x) (SY: s y) (EQ : f x = f y), 
      x = y.

  Definition restr_fun {A B : Type} (s : A -> Prop) (f g : A -> B) := 
    fun x => if excluded_middle_informative (s x) then f x else g x.

  Definition fixset {A : Type} (s : A -> Prop) (f : A -> A) := 
    forall (x : A) (SX : s x), f x = x.

  Definition downward_total {A : Type} (r : relation A) := 
    forall x y z (Rxz : r x z) (Ryz : r y z), clos_refl_sym r x y.

  Lemma bunion_alt {A B: Type} (R': B -> relation A):
    (fun (x y: A) => exists b, R' b x y) ≡ ⋃ b, R' b.
  Proof using. basic_solver. Qed.

End AuxRel.

Notation "⊤₁" := set_full.
Notation "⊤₂" := (fun _ _ => True).

Notation "a ⁼" := (clos_refl_sym a) (at level 1, format "a ⁼").
Notation "a ^=" := (clos_refl_sym a) (at level 1, only parsing).

Global
Hint Unfold 
     clos_sym clos_refl_sym 
     inj_dom restr_fun set_map
     eq_opt compl_rel fixset : unfolderDb. 

Lemma dom_rel_irr_seq_eq_no_eq {A} p s (e : A)
  (IRR : irreflexive p)
  (DOM : dom_rel (p ;; <|eq e|>) ⊆₁ s ∪₁ eq e) :
  dom_rel (p ;; <|eq e|>) ⊆₁ s.
Proof using.
  ins. intros b [c HH]. apply seq_eqv_r in HH. desf.
  specialize (DOM b). destruct DOM; auto.
  { basic_solver 10. }
  desf. now apply IRR in HH.
Qed.

Section Props.

Variables A B C : Type.
Variables s s' s'' : A -> Prop.
Variables p p' p'' : B -> Prop.
Variables r r' r'' : relation A.

(******************************************************************************)
(** ** clos_sym/clos_refl_sym properties *)
(******************************************************************************)

Lemma crs_cs : r⁼ ≡ ⦗⊤₁⦘ ∪ r^⋈.
Proof using. basic_solver. Qed. 

Lemma crs_restr1 : (restr_rel s r)⁼ ≡ ⦗⊤₁⦘ ∪ restr_rel s r^⋈.
Proof using. basic_solver 10. Qed.

Lemma crs_restr2 : restr_rel s r⁼ ≡ restr_rel s ⦗⊤₁⦘ ∪ restr_rel s r^⋈.
Proof using. basic_solver 10. Qed.

(******************************************************************************)
(** ** dom/codom properties *)
(******************************************************************************)

(* TODO : rename *)
Lemma seq_codom_dom_inter : codom_rel r ∩₁ dom_rel r' ≡₁ ∅ -> r ⨾ r' ≡ ∅₂.
Proof using.
  unfold set_equiv, set_subset; ins; desf. 
  unfold same_relation; splits; [|basic_solver].
  unfold seq, inclusion. 
  intros x y [z HH]. 
  specialize (H z).
  apply H. 
  basic_solver.
Qed.

(******************************************************************************)
(** ** cross_rel properties *)
(******************************************************************************)

Lemma seq_cross_eq x : s × eq x ⨾ eq x × s' ≡ s × s'.
Proof using. basic_solver 10. Qed.

(* Lemma seq_eqv_cross : ⦗q⦘ ⨾ s × s' ⨾ ⦗q'⦘ ≡ (q ∩₁ s) × (q' ∩₁ s'). *)
(* Proof using. basic_solver. Qed. *)

Lemma restr_cross : restr_rel s r ≡ r ∩ s × s.
Proof using. basic_solver. Qed.

Lemma seq_cross_singl_l x y : s' x -> s × s' ⨾ singl_rel x y ≡ s × eq y.
Proof using. 
  ins. 
  autounfold with unfolderDb.
  splits; ins; splits; desf; eauto. 
Qed.

Lemma seq_cross_singl_r x y : s y -> singl_rel x y ⨾ s × s' ≡ eq x × s'.
Proof using. 
  ins. 
  autounfold with unfolderDb.
  splits; ins; splits; desf; eauto. 
Qed.

(******************************************************************************)
(** ** transp properties *)
(******************************************************************************)

Lemma transp_singl_rel (x y : A) : (singl_rel x y)⁻¹ ≡ singl_rel y x.
Proof using. basic_solver. Qed.

Lemma transp_sym_equiv : symmetric r -> r⁻¹ ≡ r. 
Proof using. basic_solver. Qed.

Lemma sym_transp_equiv : symmetric r <-> r⁻¹ ≡ r. 
Proof using.
  split.
  { basic_solver. }
  intros HH.
  red. ins. by apply HH.
Qed.

(* TODO : rename *)
Lemma seq_transp_sym : symmetric r -> ⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘ ≡ (⦗ s' ⦘ ⨾ r ⨾ ⦗ s ⦘)⁻¹.
Proof using. 
  ins. 
  rewrite !transp_seq. 
  rewrite !seqA.
  rewrite !transp_sym_equiv; auto. 
  rewrite !transp_eqv_rel. 
  done.
Qed.

(******************************************************************************)
(** ** set_collect properties *)
(******************************************************************************)

Lemma set_collect_eq_dom (f g : A -> B) (EQ : eq_dom s f g) :
  f ↑₁ s ≡₁ g ↑₁ s.
Proof using. 
  unfolder in *. 
  split. 
  { ins. desf. 
    specialize (EQ y H).
    eauto. }
  ins. desf. eauto. 
Qed.

Lemma set_collect_eq_opt (f : A -> B) (a : option A) : 
  f ↑₁ eq_opt a ≡₁ eq_opt (option_map f a).
Proof using. unfold eq_opt, option_map. basic_solver. Qed.

Lemma set_collect_updo (f : A -> B) (a : A) (b : B) (NC : ~ s a) : 
  (upd f a b) ↑₁ s ≡₁ f ↑₁ s.
Proof using.
  assert (forall x: A, s x -> x <> a). 
  { ins. intros HH. by subst. }
  unfolder.
  splits; unfold set_subset; ins.
  all: desf; eexists; splits; eauto.
  all: rewrite updo; auto.
Qed.

Lemma set_collect_restr_fun (f g : A -> B) : 
  s' ⊆₁ s -> (restr_fun s f g) ↑₁ s' ≡₁ f ↑₁ s'.
Proof using. 
  clear.
  unfolder. ins. split. 
  all : 
    ins; desc; 
    eexists; split; eauto; 
    destruct (excluded_middle_informative (s y)); 
    eauto; exfalso; intuition. 
Qed.

Lemma set_collect_if_then (ft fe: A -> B) (HH : s ⊆₁ s') :
  (fun e : A =>
     if excluded_middle_informative (s' e)
     then ft e
     else fe e) ↑₁ s ≡₁ ft ↑₁ s.
Proof using.
  unfolder. split; ins; desf; eauto.
  2: eexists; splits; eauto; desf.
  all: by exfalso; match goal with H : ~ _ |- _ => apply H end; apply HH.
Qed.

Lemma set_collect_if_else (ft fe: A -> B) (HH : s ∩₁ s' ⊆₁ ∅) :
  (fun e : A =>
     if excluded_middle_informative (s' e)
     then ft e
     else fe e) ↑₁ s ≡₁ fe ↑₁ s.
Proof using.
  unfolder. split; ins; desf; eauto.
  2: eexists; splits; eauto; desf.
  all: exfalso; eapply HH; split; eauto.
Qed.

(******************************************************************************)
(** ** collect_rel properties *)
(******************************************************************************)

(* Lemma collect_rel_eq_dom : *)
(*   forall (s s': A -> Prop) (EQs: eq_dom s f g) (EQs': eq_dom s' f g), *)
(*   f ↑ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘) ≡ g ↑ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘). *)
(* Proof using. *)
(*   ins. *)
(*   unfolder. *)
(*   splits; ins; desf; repeat eexists; eauto; symmetry. *)
(*   { by apply EQs. } *)
(*   by apply EQs'. *)
(* Qed. *)

Lemma collect_rel_restr_eq_dom (f g : A -> B) (EQ : eq_dom s f g) :
  f ↑ (restr_rel s r) ≡ g ↑ (restr_rel s r).
Proof using. 
  unfolder. split.
  { ins; desf; repeat eexists; eauto; 
      symmetry; eapply EQ; auto. }
  ins; desf; repeat eexists; eauto; 
    symmetry; eapply EQ; auto.
Qed.

Lemma collect_rel_interi (f : A -> B) : 
  f ↑ (r ∩ r') ⊆ (f ↑ r) ∩ (f ↑ r').
Proof using. basic_solver 10. Qed.

Lemma collect_rel_seqi (f : A -> B) : 
  f ↑ (r ⨾ r') ⊆ (f ↑ r) ⨾ (f ↑ r').
Proof using. basic_solver 30. Qed.

Lemma collect_rel_fixset (f : A -> A) (FIX : fixset s f) :
  f ↑ restr_rel s r ≡ restr_rel s r.
Proof using.
  unfolder in *.
  split; ins; desf.
  2: { do 2 eexists. splits; eauto. }
  assert (f x' = x') as HX. 
  { specialize (FIX x'). auto. }
  assert (f y' = y') as HY. 
  { specialize (FIX y'). auto. }
  splits; congruence.
Qed.

Lemma collect_rel_if_then
      (ft fe: A -> B) (DOM : dom_rel r ⊆₁ s) (CODOM : codom_rel r ⊆₁ s) :
  (fun e : A =>
     if excluded_middle_informative (s e)
     then ft e
     else fe e) ↑ r ≡ ft ↑ r.
Proof using.
  unfolder. split; ins; desf; eauto.
  4: do 2 eexists; splits; eauto; desf.
  1,3,5: by exfalso; match goal with H : ~ _ |- _ => apply H end;
    eapply CODOM; eexists; eauto.
  all: by exfalso; match goal with H : ~ _ |- _ => apply H end;
    eapply DOM; eexists; eauto.
Qed.

Lemma collect_rel_if_else
      (ft fe: A -> B) (DOM : dom_rel r ∩₁ s ⊆₁ ∅) (CODOM : codom_rel r ∩₁ s ⊆₁ ∅) :
  (fun e : A =>
     if excluded_middle_informative (s e)
     then ft e
     else fe e) ↑ r ≡ fe ↑ r.
Proof using.
  unfolder. split; ins; desf; eauto.
  4: do 2 eexists; splits; eauto; desf.
  1,2,4: by exfalso; eapply DOM; split; [eexists|]; eauto.
  all: exfalso; eapply CODOM; split; [eexists|]; eauto.
Qed.

(******************************************************************************)
(** ** set_map/set_collect properties *)
(******************************************************************************)

Lemma collect_map_in_set (f : A -> B) : 
  f ↑₁ (f ↓₁ p) ⊆₁ p.
Proof using. basic_solver. Qed.

Lemma set_in_map_collect (f : A -> B) : 
  s ⊆₁ f ↓₁ (f ↑₁ s).
Proof using. basic_solver. Qed.

(******************************************************************************)
(** ** inj_dom properties *)
(******************************************************************************)

Lemma inj_dom_union 
      (f : A -> B)
      (INJ : inj_dom s f) 
      (INJ' : inj_dom s' f) 
      (DISJ : set_disjoint (f ↑₁ s) (f ↑₁ s')) :
  inj_dom (s ∪₁ s') f. 
Proof using. 
  unfolder in *. 
  ins; desf; 
    try (by exfalso; eapply DISJ; eauto).
  { by apply INJ. }
    by apply INJ'. 
Qed.

Lemma inj_dom_eq (f : A -> B) (a : A) :
  inj_dom (eq a) f. 
Proof using. basic_solver. Qed.

Lemma inj_dom_eq_opt (f : A -> B) (a : option A) :
  inj_dom (eq_opt a) f. 
Proof using. basic_solver. Qed.

(******************************************************************************)
(** ** fixset properties *)
(******************************************************************************)

Lemma fixset_union (f : A -> A) : 
  fixset (s ∪₁ s') f <-> fixset s f /\ fixset s' f.
Proof using. clear; unfolder; split; ins; intuition. Qed.

Lemma fixset_eq_dom (f g : A -> A) (EQD : eq_dom s f g) : 
  fixset s f <-> fixset s g.
Proof using. 
  unfolder in *. 
  split; ins; 
    specialize (EQD x SX);
    specialize (H x SX);
    congruence.
Qed.

Lemma fixset_set_fixpoint (f : A -> A) : 
  fixset s f -> s ≡₁ f ↑₁ s.
Proof using. 
  autounfold with unfolderDb; unfold set_subset.
  intros FIX.
  splits. 
  { ins. eexists. 
    specialize (FIX x). 
    splits; eauto. } 
  ins; desf. 
  erewrite (FIX y); auto. 
Qed.

Lemma fixset_swap (f' : A -> B) (g' : B -> A) : 
  fixset s (g' ∘ f') -> fixset (f' ↑₁ s) (f' ∘ g').
Proof using.
  unfolder.
  intros FIX x [y [DOM Fy]].
  unfold compose. 
  rewrite <- Fy.
  fold (compose g' f' y).
  rewrite FIX; auto. 
Qed.

(******************************************************************************)
(** ** TODO : structure other properties *)
(******************************************************************************)

Lemma set_compl_inter_id : set_compl s ∩₁ s ≡₁ ∅.
Proof using. basic_solver. Qed.

Lemma eq_opt_someE (a : A) : eq_opt (Some a) ≡₁ eq a.
Proof using. basic_solver. Qed. 

Lemma eq_opt_noneE : eq_opt (None : option A) ≡₁ ∅.
Proof using. basic_solver. Qed. 

Lemma empty_irr : r ≡ ∅₂ -> irreflexive r. 
Proof using. basic_solver. Qed.

Lemma restr_fun_fst (f g : A -> B) x : 
  s x -> restr_fun s f g x = f x. 
Proof using. clear. unfolder. basic_solver. Qed.

Lemma restr_fun_snd (f g : A -> B) x : 
  ~ s x -> restr_fun s f g x = g x. 
Proof using. clear. unfolder. basic_solver. Qed.

Lemma set_subset_union_minus : s ⊆₁ s \₁ s' ∪₁ s'. 
Proof using. 
  by unfold set_minus, set_union, set_subset; clear; intros; tauto.
Qed.

Lemma set_union_minus : s' ⊆₁ s -> s ≡₁ s \₁ s' ∪₁ s'. 
Proof using. 
  intros. 
  unfold set_equiv; splits; 
    [by apply set_subset_union_minus|basic_solver].
Qed.

Lemma union_minus : r' ⊆ r -> r ≡ r \ r' ∪ r'.
Proof using. 
  intros H.
  unfold same_relation; splits.
  { by apply inclusion_union_minus. }
  basic_solver.
Qed.

Lemma minus_eqv_absorb_rr : r' ⨾ ⦗ s ⦘ ≡ ∅₂ -> (r \ r') ⨾ ⦗ s ⦘ ≡ r ⨾ ⦗ s ⦘.
Proof using. 
  unfolder.
  ins; splits; ins; desf.
  eexists; splits; eauto. 
Qed.

Lemma minus_eqv_absorb_rl : ⦗ s ⦘ ⨾ r' ≡ ∅₂ -> ⦗ s ⦘ ⨾ (r \ r') ≡ ⦗ s ⦘ ⨾ r.
Proof using. 
  unfolder.
  ins; splits; ins; desf.
  eexists; splits; eauto.
Qed.

Lemma minus_disjoint : r ∩ r' ≡ ∅₂ -> r \ r' ≡ r. 
Proof using. clear. basic_solver 5. Qed.

Lemma set_minus_inter_set_compl : s \₁ s' ≡₁ s ∩₁ set_compl s'.
Proof using. basic_solver. Qed.

Lemma minus_inter_compl : r \ r' ≡ r ∩ compl_rel r'.
Proof using. basic_solver. Qed.

Lemma compl_top_minus : forall (r : relation A), compl_rel r ≡ (fun _ _ => True) \ r.
Proof using. basic_solver. Qed.

Lemma minus_union_r : forall (r r' r'': relation A), r \ (r' ∪ r'') ≡ (r \ r') ∩ (r \ r'').
Proof using. 
  unfolder; splits; ins; desf; splits; auto.
  unfold not; basic_solver.
Qed.

Lemma compl_union : compl_rel (r ∪ r')  ≡ compl_rel r ∩ compl_rel r'.
Proof using. 
  rewrite !compl_top_minus; by apply minus_union_r.
Qed.

Lemma seq_eqv_inter : ⦗s⦘ ⨾ (r ∩ r') ⨾ ⦗s'⦘ ≡ (⦗s⦘ ⨾ r ⨾ ⦗s'⦘) ∩ (⦗s⦘ ⨾ r' ⨾ ⦗s'⦘).
Proof using. 
  rewrite !seq_eqv_lr. 
  unfold inter_rel.
  unfold same_relation, inclusion.
  splits; ins; splits; desf. 
Qed.

Lemma seq_eqv_inter_rr :
        r ∩ (r' ⨾ ⦗s⦘) ≡ r ∩ r' ⨾ ⦗s⦘.
Proof using. basic_solver. Qed.

Lemma map_collect_id (f : A -> B) :
  r ⊆ f ↓ (f ↑ r).
Proof using. basic_solver 10. Qed.

Lemma set_subset_inter_l (LL : s ⊆₁ s'' \/ s' ⊆₁ s'') :
  s ∩₁ s' ⊆₁ s''.
Proof using.
  desf.
  all: rewrite LL.
  all: basic_solver.
Qed.

Lemma set_minus_remove_l (IN : s ⊆₁ s') :
  s \₁ s'' ⊆₁ s'.
Proof using. generalize IN. basic_solver. Qed.

Lemma restr_set_subset 
      (SUBS : s' ⊆₁ s) 
      (EQ   : restr_rel s r ≡ restr_rel s r') :
  restr_rel s' r ≡ restr_rel s' r'.
Proof using. 
  unfolder in *.
  destruct EQ as [INCL INCR].
  splits; ins; splits; desf;
    [ apply (INCL x y) | apply (INCR x y) ]; 
    auto.
Qed.

Lemma restr_inter_absorb_l :
  restr_rel s r ∩ restr_rel s r' ≡ r ∩ restr_rel s r'.
Proof using. basic_solver. Qed.

Lemma restr_inter_absorb_r :
  restr_rel s r ∩ restr_rel s r' ≡ restr_rel s r ∩ r'.
Proof using. basic_solver. Qed.

Lemma restr_irrefl_eq (IRRFLX: irreflexive r):
  forall x:A, (restr_rel (eq x) r) ≡ ∅₂.
Proof using. basic_solver. Qed.

Lemma restr_clos_trans : (restr_rel s r)⁺ ⊆ restr_rel s r⁺.
Proof using.
  unfold inclusion, restr_rel; ins. 
  induction H; desf; splits; eauto using t_step, t_trans. 
Qed.

Lemma rt_dom_ri (HH : r ⊆ ⦗ s ⦘ ⨾ r) : r＊ ⨾ ⦗ s ⦘ ⊆ (r ⨾ ⦗ s ⦘)＊.
Proof using.
  rewrite rtE at 1.
  rewrite seq_union_l.
  apply inclusion_union_l; [basic_solver|].
  rewrite HH at 1.
  rewrite clos_trans_rotl.
  rewrite !seqA.
  rewrite <- ct_end.
  rewrite inclusion_t_rt.
  basic_solver.
Qed. 

Lemma restr_clos_trans_eq (Hrestr : r ≡ restr_rel s r) : 
  clos_trans (r) ≡ restr_rel s (clos_trans (r)).
Proof using. 
  split; [|basic_solver].
  rewrite <- restr_clos_trans. 
  by rewrite Hrestr at 1.
Qed.

Lemma clos_refl_trans_union_ext (Hrr : r ⨾ r ≡ ∅₂) (Hrr' : r ⨾ r' ≡ ∅₂) : 
  (r ∪ r')＊ ≡ r'＊ ⨾ r^?.
Proof using. 
  clear r'' s s' s'' p p' p'' B C.
  rewrite crE, seq_union_r, seq_id_r.
  rewrite rt_unionE.
  rewrite <- cr_of_ct with (r := (r ⨾ r'＊)).
  rewrite crE, seq_union_r.
  apply union_more.
  { basic_solver. }
  arewrite (r ⨾ r'＊ ≡ r). 
  { rewrite <- cr_of_ct, crE, seq_union_r.
    arewrite (r ⨾ r'⁺ ≡ ∅₂).
    { split; [|basic_solver].
      intros x y HH.  
      destruct HH as [z [HA HB]].
      induction HB. 
      { eapply Hrr'. unfolder. eauto. }
      intuition. }
    basic_solver. }
  arewrite (r⁺ ≡ r); auto. 
  split. 
  { intros x y HH. 
    induction HH; auto.  
    exfalso. eapply Hrr. unfolder. eauto. }
  red. ins. constructor. auto. 
Qed.

Lemma clos_trans_union_ext (Hrr : r ⨾ r ≡ ∅₂) (Hrr' : r ⨾ r' ≡ ∅₂) : 
  (r ∪ r')⁺ ≡ r'⁺ ∪ r'＊ ⨾ r.
Proof using. 
  rewrite ct_unionE.
  arewrite ((r ⨾ r'＊)⁺ ≡ r); auto. 
  unfold same_relation; splits.
  { unfold inclusion; ins. 
    induction H. 
    { eapply seq_rtE_r in H. 
      unfold union in H; desf.
      repeat unfold seq in *; desf. 
      exfalso. 
      eapply Hrr'. 
      eexists; splits; eauto. }
    exfalso. 
    eapply Hrr. 
    unfold seq; exists y; splits; eauto. }
  rewrite seq_rtE_r.
  unfold inclusion; ins. 
  eapply clos_trans_mori.
  2: { eapply t_step. eauto. }
  apply inclusion_union_r1.
Qed.   

Lemma set_compl_union_id : s ∪₁ set_compl s ≡₁ ⊤₁.
Proof using.
  split; [basic_solver|].
  intros x _.
  destruct (classic (s x)).
  { by left. }
    by right.
Qed.

Lemma set_split : s' ∪₁ s'' ≡₁ ⊤₁ -> s ≡₁ s ∩₁ s' ∪₁ s ∩₁ s''.
Proof using. 
  unfolder. intros [_ HS]. 
  split; [|basic_solver].
  intros x Sx. 
  specialize (HS x I).
  basic_solver. 
Qed.

(* TODO: fix name *)
Lemma set_split_comlete : s' ≡₁ s' ∩₁ s ∪₁ s' ∩₁ (set_compl s).
Proof using. 
  (* copy paste of previous lemma because of section variables :( *)
  unfolder. 
  split; [|basic_solver].
  intros x Sx. 
  pose proof set_compl_union_id as [_ HH].
  specialize (HH x I).
  unfolder in HH.
  basic_solver. 
Qed.

Lemma eqv_l_set_compl_eqv_l : r ⊆ ⦗s⦘ ⨾ r ∪ r' -> ⦗set_compl s⦘ ⨾ r ⊆ r'.
Proof using. 
  rewrite !seq_eqv_l.
  intros Hr x y [nSx Rxy].
  apply Hr in Rxy.
  unfolder in Rxy. desf.
Qed.

Lemma dom_r2l_rt (HH : r ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r') : r＊ ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r'＊.
Proof using.
  unfolder in *. ins. desf.
  induction H.
  { edestruct HH; eauto. split; auto.
      by apply rt_step. }
  { split; auto. apply rt_refl. }
  destruct IHclos_refl_trans2; auto.
  destruct IHclos_refl_trans1; auto.
  split; auto.
  eapply transitive_rt; eauto.
Qed.

(* TODO: rename! collision w/ hahn *)
Lemma inter_trans : transitive r -> transitive r' -> transitive (r ∩ r').
Proof using. 
  clear.
  unfolder.
  intros TR TR' x y z.
  specialize (TR x y z).
  specialize (TR' x y z).
  intuition.
Qed.

Lemma immediate_in : immediate r ⊆ r. 
Proof using. basic_solver. Qed.

Lemma immediate_inter : 
  (immediate r) ∩ r' ⊆ immediate (r ∩ r').
Proof using. basic_solver. Qed.

Lemma immediate_transp :
  (immediate r)⁻¹ ≡ immediate (r⁻¹).
Proof using. basic_solver. Qed.

Lemma trans_prcl_immediate_seqr_split x y
      (TRANS : transitive r) (PRCL : downward_total r) (IMM : (immediate r) x y) :
  r ⨾ ⦗ eq y ⦘ ≡ (eq x ∪₁ dom_rel (r ⨾ ⦗ eq x ⦘)) × eq y.
Proof using. 
  red; split. 
  { unfolder.
    intros z y' [Rzy EQy].
    split; auto.
    assert (r^= z x) as Rzx. 
    { eapply PRCL; eauto; desf.  
      by apply immediate_in. }
    unfolder in *.
    unfold clos_refl_sym in Rzx.
    desf; eauto. 
    exfalso. eapply IMM0; eauto. }
  unfolder.  ins. desf.
  { splits; desf.
    by apply immediate_in. }
  splits; desf. 
  eapply TRANS; eauto. 
  by apply immediate_in.
Qed. 

Lemma clos_refl_trans_ind_step_left 
        (R : relation A) (P : A -> Prop) x y (Px : P x)
        (rtR : R＊ x y)
        (STEP : forall z z', P z -> R z z' -> R＊ z' y -> P z') :
    P y.
Proof using. 
  generalize dependent Px.
  induction rtR; auto.
  { intros Px.
    specialize (STEP x y).
    apply STEP; auto.
    apply rt_refl. }
  intros Px.
  apply IHrtR2; auto.
  apply IHrtR1; auto.
  ins. eapply STEP; eauto.
  eapply rt_trans; eauto.
Qed.

Lemma set_equiv_exp_equiv :
  s ≡₁ s' <-> forall x : A, s x <-> s' x.
Proof using.
  split.
  { apply set_equiv_exp. }
  intros HH. by split; red; ins; apply HH.
Qed.

Lemma fsupp_bunion_disj (ss : B -> A -> Prop) (rr: B -> relation A)
      (FS: forall b1 b2 (NEQ: b1 <> b2), set_disjoint (ss b1) (ss b2)) 
      (FSUPP: forall b, fsupp (restr_rel (ss b) (rr b))):
  fsupp (⋃ b, restr_rel (ss b) (rr b)). 
Proof using.
  red. ins.
  destruct (classic ((fun x => (⋃b, restr_rel (ss b) (rr b)) x y) ≡₁ ∅)).
  { exists nil. ins. eapply H. eauto. }
  apply set_nonemptyE in H. desc. red in H. desc.
  specialize (FSUPP a). red in FSUPP. specialize (FSUPP y). desc.
  exists findom. ins. red in REL. desc.
  enough (a0 = a).
  { subst a0. apply FSUPP. red in REL0. by desc. }
  red in H0, REL0. desc.
  destruct (classic (a0 = a)); auto.
  specialize (FS _ _ H3 _ REL2). vauto.
Qed.

Lemma rel_extensionality (r1 r2 : relation A) :
  r1 ≡ r2 -> r1 = r2.
Proof using.
  ins; extensionality x; extensionality y.
  apply propositional_extensionality; split; apply H.
Qed.

Lemma split_rel : r ≡ r ∩ r' ∪ r \ r'.
Proof using s s' r.
  clear  s''. 
  unfolder; splits; ins; desf; tauto.
Qed.


Lemma minus_eqv_r : r ⨾ ⦗ s ⦘ \ r' ≡ (r \ r') ⨾ ⦗ s ⦘.
Proof using.
basic_solver 21.
Qed.

Lemma fin_dom_rel_fsupp (S: A -> Prop)
      (FINS: set_finite S) (FSUPPr: fsupp r):
  set_finite (dom_rel (r ⨾ ⦗S⦘)).
Proof using.
  clear -FINS FSUPPr.
  red in FSUPPr. apply functional_choice in FSUPPr as [supp_map FSUPPr].
  destruct FINS as [Sl DOMS]. 
  exists (concat (map supp_map Sl)).
  intros a [s DOM%seq_eqv_r]. desc.
  apply in_concat_iff. eexists. split.
  - eapply FSUPPr; eauto.
  - apply in_map. intuition.
Qed. 

Lemma fsupp_fin_dom (M: A -> Prop)
      (FINM: set_finite M):
  fsupp (⦗M⦘ ⨾ r).
Proof using.
  destruct FINM as [findom FINDOM]. 
  red. ins. exists findom. ins. apply FINDOM.
  apply seq_eqv_l in REL. by desc.
Qed.

End Props.

Lemma dom_rel_clos_refl_trans_eqv {A: Type} (r: relation A) (d: A -> Prop)
      (DOM: dom_rel (r ⨾ ⦗d⦘) ⊆₁ d):
  dom_rel (r^* ⨾ ⦗d⦘) ⊆₁ d. 
Proof using.
  rewrite rtEE. rewrite seq_bunion_l, dom_rel_bunion.
  apply set_subset_bunion_l. intros n _. induction n.
  { rewrite pow_0. basic_solver. }
  rewrite pow_S_begin, seqA.
  apply dom_rel_helper in IHn. rewrite IHn.
  rewrite <- !seqA. do 2 rewrite dom_seq. auto. 
Qed.


Lemma InAE A x (l : list A) : SetoidList.InA eq x l <-> In x l.
Proof using.
  split; [by induction 1; desf; ins; eauto|].
  induction l; ins; desf; eauto using SetoidList.InA.
Qed.

Lemma NoDupAE A (l : list A) : SetoidList.NoDupA eq l <-> NoDup l.
Proof using.
  split; induction 1; constructor; eauto; rewrite InAE in *; eauto.
Qed.

Lemma NoDup_map_NoDupA A B (f : A -> B) l :
  SetoidList.NoDupA (fun p p' => f p = f p') l ->
  NoDup (map f l).
Proof using.
  induction 1; ins; constructor; eauto.
  clear -H; intro M; destruct H; induction l; ins; desf;
    eauto using SetoidList.InA.
Qed.


Lemma set_equiv_inter_singleton {A: Type} (S1 S2: A -> Prop) (a: A):
  (S1 a <-> S2 a) <-> (S1 ∩₁ eq a ≡₁ S2 ∩₁ eq a). 
Proof using. 
  split; ins; [basic_solver 10| ]. 
  split; ins; apply H; split; auto. 
Qed. 

Add Parametric Morphism A : (@compl_rel A) with signature 
  same_relation ==> same_relation as compl_more.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  inclusion --> inclusion as compl_mori.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@downward_total A) with signature 
    same_relation ==> iff as downward_total_more.
Proof using. 
  intros x y EQ. unfold downward_total. split; ins.
  eapply clos_refl_sym_more; [symmetry|]; eauto.
  2: eapply clos_refl_sym_more; eauto.
  all: apply EQ in Rxz.
  all: apply EQ in Ryz.
  all: eapply H; eauto.
Qed.

Add Parametric Morphism A B : (@eq_dom A B) with signature 
    set_equiv ==> eq ==> eq ==> iff as eq_dom_more.
Proof using. 
  intros s s' Heq f g. 
  unfold eq_dom. 
  split; ins; 
    specialize (H x); 
    apply H; auto; 
    apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@eq_dom A B) with signature 
    set_subset --> eq ==> eq ==> impl as eq_dom_mori.
Proof using. basic_solver. Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
    set_equiv ==> eq ==> iff as inj_dom_more.
Proof using. 
  intros s s' Heq f. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_subset --> eq ==> impl as inj_dom_mori.
Proof using. basic_solver. Qed.

(* TODO: separate section for fixset and move to Hahn *)
(* ****************** *)
Add Parametric Morphism A : (@fixset A) with signature 
    set_equiv ==> eq ==> iff as fixset_more.
Proof using. 
  intros s s' Heq f. red. 
  unfold fixset.
  splits; ins; specialize (H x); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A : (@fixset A) with signature 
  set_subset --> eq ==> impl as fixset_mori.
Proof using. unfold impl, fixset. basic_solver. Qed.
(* ****************** *)

(* TODO: move to Hahn *)
(* ****************** *)
Add Parametric Morphism A : (@set_compl A) with signature 
  set_equiv ==> set_equiv as set_compl_more.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_compl A) with signature 
  set_subset --> set_subset as set_compl_mori.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_minus A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_minus_more.
Proof using. red; unfolder; splits; ins; desf; split; eauto. Qed.

Add Parametric Morphism A : (@set_minus A) with signature 
  set_subset ==> set_subset --> set_subset as set_minus_mori.
Proof using. red; unfolder; splits; ins; desf; eauto. Qed.
(* ****************** *)
