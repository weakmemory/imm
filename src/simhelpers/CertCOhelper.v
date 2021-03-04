From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.

Set Implicit Arguments.

Section CO.

Variables G : execution.
Variable I : actid -> Prop.  (* issued *)
Variable T : actid -> Prop.  (* all writes in certified thread *)

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Hypothesis IT: I ∪₁ T ≡₁ E ∩₁ W.

Lemma IN_I: I ⊆₁ E ∩₁ W.
Proof using IT.
rewrite <- IT; basic_solver 21.
Qed.

Lemma IN_T: T ⊆₁ E ∩₁ W.
Proof using IT.
rewrite <- IT; basic_solver 21.
Qed.

Hypothesis wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘.
Hypothesis wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘.
Hypothesis wf_col : co ⊆ same_loc.
Hypothesis co_trans : transitive co.
Hypothesis wf_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co.
Hypothesis co_irr : irreflexive co.

Definition col l := (⦗Loc_ l⦘ ⨾ co ⨾ ⦗Loc_ l⦘).

Definition col0 l := (⦗I⦘ ⨾ col l ⨾ ⦗I⦘ ∪ ⦗T⦘ ⨾ col l ⨾ ⦗T⦘ ∪ ⦗I⦘ ⨾ col l ⨾ ⦗T⦘)⁺.

Definition new_col l := pref_union (col0 l) ((I ∩₁ Loc_ l) × (E ∩₁ W ∩₁ Loc_ l \₁ I)).

Definition new_co x y := exists l, (new_col l) x y.

Lemma col_in_co l : col l ⊆ co.
Proof using. 
unfold col; basic_solver. 
Qed.

Lemma co_in_col x y : co x y -> exists l, col l x y.
Proof using wf_coD wf_col.
unfold new_co, col; ins; unfolder; ins; desf.
hahn_rewrite (dom_l wf_coD) in H; unfolder in H; desc.
generalize (is_w_loc lab x H); ins; desf.
eexists; splits; eauto.
eexists; splits; eauto.
eexists; splits; eauto.
apply wf_col in H0; unfold Events.same_loc in H0; congruence.
Qed.

Lemma wf_colE l : col l ≡ ⦗E⦘ ⨾ col l ⨾ ⦗E⦘.
Proof using wf_coE. 
apply dom_helper_3; unfold col; rewrite wf_coE; basic_solver. 
Qed.

Lemma wf_colD l : col l ≡ ⦗W_ l⦘ ⨾ col l ⨾ ⦗W_ l⦘.
Proof using wf_coD.
apply dom_helper_3; unfold col; rewrite wf_coD; basic_solver. 
Qed.

Lemma wf_coll l : col l ⊆ same_loc.
Proof using wf_col.
unfold col; rewrite wf_col; basic_solver. 
Qed.

Lemma col_trans l : transitive (col l).
Proof using co_trans.
unfold col.
rewrite <- restr_relE.
by apply transitive_restr.
Qed.

Lemma wf_col_total l : is_total (E ∩₁ W ∩₁ Loc_ l) (col l).
Proof using wf_coD wf_coE wf_co_total.
rewrite wf_colD, wf_colE.
unfold col; rewrite !seqA.
arewrite (⦗W_ l⦘ ⨾ ⦗E⦘ ⨾ ⦗Loc_ l⦘ ≡ ⦗E ∩₁ W ∩₁ Loc_ l⦘) by basic_solver.
arewrite (⦗Loc_ l⦘ ⨾ ⦗E⦘ ⨾ ⦗W_ l⦘ ≡ ⦗E ∩₁ W ∩₁ Loc_ l⦘) by basic_solver.
rewrite <- restr_relE.
apply is_total_restr.
apply wf_co_total.
Qed.

Lemma col_irr l: irreflexive (col l).
Proof using co_irr.
unfold col.
rewrite <- restr_relE.
by apply irreflexive_restr.
Qed.

Lemma acyclic_new_col l : acyclic (new_col l).
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
eapply acyclic_pref_union with (dom:=I ∩₁ Loc_ l).
- unfold col0.
  arewrite_id ⦗I⦘.
  arewrite_id ⦗T⦘.
  relsf.
  generalize (@col_trans l); ins; relsf; apply col_irr.
- unfold col0; relsf.
- assert (XX: restr_rel (I ∩₁ Loc_ l) (col l) ⊆ col0 l).
  by unfold col0; rewrite <- ct_step; basic_solver 21.
  rewrite <- XX.
  apply is_total_restr.
  rewrite IN_I.
  eapply wf_col_total.
- unfolder; ins; desf; splits; eauto; intro; desf.
Qed.

Lemma wf_new_colE l : new_col l ≡ ⦗E⦘ ⨾ new_col l ⨾ ⦗E⦘.
Proof using IT wf_coE.
apply dom_helper_3.
unfold new_col, pref_union, col0; unfolder; ins; desf.
2: by generalize (IN_I H); basic_solver 12.
induction H; [|basic_solver].
desf; apply (wf_colE l) in H0; unfolder in H0; desf; eauto.
Qed.

Lemma wf_new_colD l : new_col l ≡ ⦗W_ l⦘ ⨾ new_col l ⨾ ⦗W_ l⦘.
Proof using IT wf_coD.
apply dom_helper_3.
unfold new_col, pref_union, col0; unfolder; ins; desf.
2: by generalize (IN_I H); basic_solver 12.
induction H; [|basic_solver].
desf; apply (wf_colD l) in H0; unfolder in H0; desf; eauto.
Qed.

Lemma wf_new_coll l : new_col l ⊆ same_loc.
Proof using IT wf_coD.
rewrite wf_new_colD; unfold Events.same_loc.
unfolder; ins; desf; congruence.
Qed.

Lemma wf_new_col_total l : is_total (E ∩₁ W ∩₁ Loc_ l) (new_col l).
Proof using IT wf_coD wf_coE wf_co_total.
unfold new_col, pref_union.
unfolder; ins; desf.
destruct (classic (col0 l a b)) as [|X]; eauto 8.
destruct (classic (col0 l b a)) as [|Y]; eauto 8.
assert (XX: ~ (⦗I⦘ ⨾ col l ⨾ ⦗I⦘ ∪ ⦗T⦘ ⨾ col l ⨾ ⦗T⦘ ∪ ⦗I⦘ ⨾ col l ⨾ ⦗T⦘) a b).
by intro; eapply X; vauto.
assert (YY: ~ (⦗I⦘ ⨾ col l ⨾ ⦗I⦘ ∪ ⦗T⦘ ⨾ col l ⨾ ⦗T⦘ ∪ ⦗I⦘ ⨾ col l ⨾ ⦗T⦘) b a).
by intro; eapply Y; vauto.
 
assert (Ta: ~ I a -> T a).
by assert (S: (E ∩₁ W) a) by basic_solver; apply IT in S; unfolder in S; ins; desf.
assert (Tb: ~ I b -> T b).
by assert (S: (E ∩₁ W) b) by basic_solver; apply IT in S; unfolder in S; ins; desf.

assert (TOT: col l a b \/ col l b a).
by apply wf_col_total; basic_solver.
destruct (classic (I a)), (classic (I b)); desf.
- exfalso; unfolder in XX; basic_solver 22.
- exfalso; unfolder in YY; basic_solver 22.
- exfalso; unfolder in XX; basic_solver 22.
- eauto 20.
- eauto 20.
- exfalso; unfolder in YY; basic_solver 22.
- exfalso; unfolder in XX; basic_solver 22.
- exfalso; unfolder in YY; basic_solver 22.
Qed.


Lemma new_col_trans l : transitive (new_col l).
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
apply transitiveI; unfolder; ins; desf.
eapply tot_ex.
- apply wf_new_col_total.
- hahn_rewrite wf_new_colE in H0.
hahn_rewrite wf_new_colD in H0.
unfolder in H0; basic_solver 21.
- hahn_rewrite wf_new_colE in H.
hahn_rewrite wf_new_colD in H.
unfolder in H; basic_solver 21.
- intro.
eapply acyclic_new_col.
eapply t_trans, t_trans; vauto.
- intro.
eapply acyclic_new_col.
eapply t_trans; vauto.
Qed.

Lemma new_col_irr l : irreflexive (new_col l).
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
red; ins; eapply acyclic_new_col; vauto.
Qed.

Lemma wf_new_coE : new_co ≡ ⦗E⦘ ⨾ new_co ⨾ ⦗E⦘.
Proof using IT wf_coE.
unfold new_co; unfolder; ins; desf; splits; ins; desf; eauto.
apply (wf_new_colE l) in H; unfolder in H; desf; eauto.
Qed.

Lemma wf_new_coD : new_co ≡ ⦗W⦘ ⨾ new_co ⨾ ⦗W⦘.
Proof using IT wf_coD.
unfold new_co; unfolder; ins; desf; splits; ins; desf; eauto.
apply (wf_new_colD l) in H; unfolder in H; desf; eauto.
Qed.

Lemma wf_new_col : new_co ⊆ same_loc.
Proof using IT wf_coD.
unfold new_co; unfolder; ins; desf; splits; ins; desf; eauto.
apply (@wf_new_coll l) in H; unfolder in H; desf; eauto.
Qed.

Lemma new_co_trans : transitive new_co.
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
unfold new_co; unfolder; ins; desf; splits; ins; desf; eauto.
hahn_rewrite wf_new_colD in H0.
hahn_rewrite wf_new_colD in H.
unfolder in H0; unfolder in H; desf.
exists l; eapply new_col_trans; eauto.
Qed.

Lemma wf_new_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) new_co.
Proof using IT wf_coD wf_coE wf_co_total.
unfold new_co; ins; unfolder; ins; desf.
generalize (is_w_loc lab a IWa1); ins; desf.
cut (new_col l a b \/ new_col l b a); [by basic_solver 21|].
apply wf_new_col_total; auto.
basic_solver.
unfolder; splits; ins; desf; congruence.
Qed.

Lemma new_co_irr : irreflexive new_co.
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
unfold new_co; ins; unfolder; ins; desf.
eapply new_col_irr; eauto.
Qed.

Lemma new_co_I : new_co ⨾ ⦗ I ⦘  ⊆ co ⨾ ⦗ I ⦘.
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
unfolder; intros x y [R K]; desf.
unfold new_co in R; desc.
hahn_rewrite wf_new_colE in R.
hahn_rewrite wf_new_colD in R.
unfolder in R; desf; splits; auto.
eapply tot_ex.
- apply wf_co_total.
- basic_solver.
- unfolder; splits; eauto; congruence.
- intro.
assert (S: (E ∩₁ W) z) by basic_solver.
apply IT in S; unfolder in S; ins; desf.
* eapply new_col_irr, new_col_trans; try edone.
red; red; unfold col0, col; left; apply t_step; basic_solver 12.
* eapply new_col_irr, new_col_trans; try edone.
red; red; unfold col0, col; left; apply t_step; basic_solver 12.
- intro; subst.
eby eapply new_col_irr.
Qed.

Lemma T_new_co : ⦗ T ⦘ ⨾ new_co  ⊆ ⦗ T ⦘ ⨾ co.
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
unfolder; intros x y [K1 R]; desf.
unfold new_co in R; desc.
hahn_rewrite wf_new_colE in R.
hahn_rewrite wf_new_colD in R.
unfolder in R; desf; splits; auto.
eapply tot_ex.
- apply wf_co_total.
- basic_solver.
- unfolder; splits; eauto; congruence.
- intro.
assert (S: (E ∩₁ W) z) by basic_solver.
apply IT in S; unfolder in S; ins; desf.
* eapply new_col_irr, new_col_trans; try edone.

red; red; unfold col0, col. left; apply t_step.
assert (I y \/ T y) by (apply IT; basic_solver).
desf; basic_solver 12.
* eapply new_col_irr, new_col_trans; try edone.
red; red; unfold col0, col; left; apply t_step.
assert (I y \/ T y) by (apply IT; basic_solver).
desf; basic_solver 12.
- intro; subst.
eby eapply new_col_irr.
Qed.

Lemma new_co_in : new_co  ⊆ co ⨾ ⦗ I ⦘ ∪ 
⦗ T ⦘ ⨾ co ∪ ⦗ I \₁ T ⦘ ⨾ new_co ⨾ ⦗ T \₁ I ⦘.
Proof using IT co_irr co_trans wf_coD wf_coE wf_co_total.
rewrite (wf_new_coD), (wf_new_coE) at 1.
rewrite !seqA.
arewrite (⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗E ∩₁ W⦘) by basic_solver.
arewrite (⦗E⦘ ⨾ ⦗W⦘ ⊆ ⦗E ∩₁ W⦘) by basic_solver.
rewrite <- IT.

arewrite (I ∪₁ T ⊆₁ (I \₁ T) ∪₁ T) at 1.
unfolder; ins; desf; tauto.

arewrite (I ∪₁ T ⊆₁ (T \₁ I) ∪₁ I) at 1.
unfolder; ins; desf; tauto.

rewrite !id_union; relsf.

sin_rewrite !T_new_co.
sin_rewrite new_co_I.
basic_solver 21.
Qed.

Lemma T_I_col0_I_T l : 
  ⦗ T \₁ I ⦘ ⨾ col0 l ⨾ ⦗ I \₁ T ⦘  ⊆ 
  ⦗ T \₁ I ⦘ ⨾ col l ⨾ ⦗ I ∩₁ T ⦘ ⨾ col l ⨾ ⦗ I \₁ T ⦘.
Proof using co_trans.
unfold col0 at 1.
arewrite (⦗T⦘ ⊆ ⦗T \₁ I⦘ ∪ ⦗I ∩₁ T⦘) at 2.
unfolder; ins ;desf; tauto.
relsf.
rewrite <- !unionA.
rewrite unionC.
rewrite <- !unionA.
rewrite path_ut_first; relsf; unionL.
- transitivity (∅₂ : actid -> actid -> Prop); [|basic_solver].
  rewrite path_ut_last; relsf; unionL.
  rewrite ct_begin; basic_solver.
  rewrite (rtE (⦗I⦘ ⨾ col l ⨾ ⦗T⦘ ∪ ⦗I⦘ ⨾ col l ⨾ ⦗I⦘)).
  relsf; unionL.
  basic_solver.
  rewrite ct_begin; basic_solver.
- arewrite (⦗I⦘ ⨾ col l ⨾ ⦗T⦘ ∪ ⦗I⦘ ⨾ col l ⨾ ⦗I⦘ ∪ ⦗T⦘ ⨾ col l ⨾ ⦗T \₁ I⦘ ⊆ col l).
  basic_solver.
  arewrite (col l ∪ ⦗T⦘ ⨾ col l ⨾ ⦗I ∩₁ T⦘ ⊆ col l).
  basic_solver.
  generalize (@col_trans l); ins; relsf.
  basic_solver 21.
Qed.

Lemma T_I_new_col_I_T l : 
  ⦗ T \₁ I ⦘ ⨾ new_col l ⨾ ⦗ I \₁ T ⦘  ⊆ 
  col l ⨾ ⦗ I ∩₁ T ⦘ ⨾ col l.
Proof using co_trans.
unfold new_col, pref_union.
unfolder; ins; desf.
assert (A: (⦗ T \₁ I ⦘ ⨾ col0 l ⨾ ⦗ I \₁ T ⦘) x y) by basic_solver.
apply T_I_col0_I_T in A; unfolder in A; basic_solver 10.
Qed.

Lemma T_I_new_co_I_T : 
  ⦗ T \₁ I ⦘ ⨾ new_co ⨾ ⦗ I \₁ T ⦘  ⊆ 
  co ⨾ ⦗ I ∩₁ T ⦘ ⨾ co.
Proof using co_trans.
unfold new_co.
unfolder; ins; desf.
assert (A: (⦗ T \₁ I ⦘ ⨾ new_col l ⨾ ⦗ I \₁ T ⦘) x y) by basic_solver.
apply T_I_new_col_I_T in A; unfolder in A; desf.
unfold col in *; unfolder in *; desf; eauto 10.
Qed.

Lemma co_for_split: codom_rel (⦗set_compl I⦘ ⨾ (immediate new_co)) ⊆₁ T.
Proof using IT wf_coD wf_coE.
unfolder; ins; desf.
destruct (classic (T x)) as [|X]; auto.
exfalso.
hahn_rewrite wf_new_coE in H0.
hahn_rewrite wf_new_coD in H0.
unfolder in H0; desf.
assert (Ix: I x).
by assert (S: (E ∩₁ W) x) by basic_solver; apply IT in S; unfolder in S; ins; desf.
unfold new_co, new_col, pref_union in *; desc.
destruct H4 as [K|]; cycle 1.
by unfolder in H2; basic_solver 21.
unfold col0 in *.
destruct K.
unfolder in H2; basic_solver 21.
eauto 12.
Qed.

Lemma new_col_helper l : ⦗ T ⦘ ⨾ col l ⨾ ⦗ I ∩₁ T ⦘ ⨾ col l ⨾ ⦗ I ⦘ ⊆ new_col l.
Proof using.
unfold new_col, pref_union, col0.
unfolder; ins; left; desf.
eapply t_trans; apply t_step; eauto 15.
Qed.

Lemma new_co_helper : ⦗ T ⦘ ⨾ co ⨾ ⦗ I ∩₁ T ⦘ ⨾ co ⨾ ⦗ I ⦘ ⊆ new_co.
Proof using wf_coD wf_col.
unfold new_co.
unfolder; ins; desf.
apply co_in_col in H0.
apply co_in_col in H2.
desf.
assert (l = l0); subst.
{ hahn_rewrite wf_colD in H0.
  hahn_rewrite wf_colD in H2.
  unfolder in *; desf. }
exists l0.
apply new_col_helper.
basic_solver 12.
Qed.

Lemma I_co_in_new_co : ⦗ I ⦘ ⨾ co ⊆ new_co.
Proof using IT wf_coD wf_coE wf_col.
unfold new_co.
unfolder; ins; desf.
apply co_in_col in H0.
desf.
exists l.
unfold new_col, pref_union, col0.
left.
apply t_step.
destruct (classic (I y)).
basic_solver 11.
right; unfolder; splits; eauto.
hahn_rewrite (wf_colE) in H0.
hahn_rewrite (wf_colD) in H0.
unfolder in H0; desf.
assert ((I ∪₁ T) y).
eapply IT; basic_solver.
unfolder in *; desf.
Qed.


End CO.
