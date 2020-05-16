(******************************************************************************)
(** * Sc-per-loc   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.

Set Implicit Arguments.
Remove Hints plus_n_O.


Section ECO.
Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'fre'" := G.(fre).
Notation "'fri'" := G.(fri).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.

(******************************************************************************)
(** ** extended coherence order  *)
(******************************************************************************)

Definition eco := rf ∪ co ⨾ rf^? ∪ fr ⨾ rf^?.

Definition sc_per_loc := irreflexive (sb ⨾ eco).

Implicit Type SC_PER_LOC : sc_per_loc.

(******************************************************************************)
(** ** Basic Properties  *)
(******************************************************************************)

Lemma co_in_eco: co ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma rf_in_eco: rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma fr_in_eco: fr ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma co_rf_in_eco: co ;; rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma fr_rf_in_eco: fr ;; rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma loceq_eco WF : funeq loc eco.
Proof using. destruct WF; desf. eauto 10 with hahn. Qed.

Lemma wf_ecoE WF : eco ≡ ⦗E⦘ ⨾ eco ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold eco.
rewrite (wf_rfE WF) at 1 2 3.
rewrite (wf_coE WF) at 1.
rewrite (wf_frE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_ecoD WF : eco ≡ ⦗RW⦘ ⨾ eco ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold eco.
rewrite wf_rfD at 1 2 3; try done.
rewrite wf_coD at 1; try done.
rewrite wf_frD at 1; try done.
type_solver 42.
Qed.

Lemma eco_alt WF: eco ≡ (co ∪ fr) ∪ (co ∪ fr)^? ⨾ rf.
Proof using.
  unfold eco, Execution.fr; basic_solver 42.
Qed.

Lemma eco_alt2 WF: eco ≡ rf ∪ (rf⁻¹)^? ⨾ co ⨾ rf^?.
Proof using.
  unfold eco, Execution.fr; basic_solver 42.
Qed.

Lemma eco_trans WF: transitive eco.
Proof using.
unfold eco.
apply transitiveI.
generalize (rf_rf WF) (rf_fr WF) (co_co WF) (rf_co WF) (co_fr WF) (fr_fr WF) (fr_co WF).
unfolder; ins; desf; try basic_solver 1.
all: try (exfalso; basic_solver).
all: basic_solver 42.
Qed.

Lemma eco_irr WF: irreflexive eco.
Proof using.
unfold eco.
generalize (co_irr WF) (rf_irr WF) (fr_irr WF).
generalize (rf_fr WF) (rf_co WF).
basic_solver 5.
Qed.

Lemma eco_alt3 WF: eco ≡ (rf ∪ co ∪ fr)⁺.
Proof using.
split; eauto 8 using rf_in_eco, co_in_eco, fr_in_eco, eco_trans with hahn.
unfold eco; rewrite !crE; relsf. 
unionL; eauto 6 using inclusion_step2_ct with hahn.
Qed.

Lemma eco_f WF : eco ⨾ ⦗F⦘ ⊆ ∅₂.
Proof using.
rewrite (wf_ecoD WF); type_solver.
Qed.

Lemma eco_almost_total WF COMP x y 
  (ACTx: E x) (ACTy: E y)
  (RWx: RW x) (RWy: RW y) (LOC: loc x = loc y)
  (NEQ: x <> y): 
  eco x y \/ eco y x \/ exists z, rf z x /\ rf z y.
Proof using.
generalize (dom_to_doma (wf_rfE WF)); intro rfE1; unfolder in rfE1.
generalize (dom_to_domb (wf_rfE WF)); intro rfE2; unfolder in rfE2.
generalize (dom_to_doma (wf_rfD WF)); intro rfD1; unfolder in rfD1.
generalize (dom_to_domb (wf_rfD WF)); intro rfD2; unfolder in rfD2.
generalize (loceq_rf WF); intro rfL; unfolder in rfL.
assert (exists l, loc x = l).
by destruct x; eauto.
unfolder in RWx. 
unfolder in RWy.
ins; desf.
- assert (exists wx, rf wx x) by (apply COMP; basic_solver).
  assert (exists wy, rf wy y) by (apply COMP; basic_solver).
  desf.
  destruct (classic (wx=wy)); try subst; eauto.
  assert (co wx wy \/ co wy wx); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; apply (loceq_rf WF) in H0; congruence.
- assert (exists wy, rf wy y) by (apply COMP; basic_solver).
  desf.
  destruct (classic (wy=x)); [subst; unfold eco; basic_solver 5|].
  assert (co wy x \/ co x wy); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; congruence.
- assert (exists wx, rf wx x).
  by apply COMP; basic_solver.
  desf.
  destruct (classic (wx=y)); [subst; unfold eco; basic_solver 5|].
  assert (co wx y \/ co y wx); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; congruence.
- assert (co x y \/ co y x); [eapply WF|unfold eco]; basic_solver 10.
Qed.


Lemma transp_rf_rf_eco_in_eco WF : rf⁻¹ ⨾ rf ⨾ eco ⊆ eco.
Proof using.
unfold eco, Execution.fr; relsf.
rewrite rf_rf; auto.
seq_rewrite rf_co; auto.
rewrite !seqA.
sin_rewrite rf_transp_rf; basic_solver 10.
Qed.

Lemma eco_transp_rf_rf_in_eco WF : eco ⨾ rf⁻¹ ⨾ rf ⊆ eco.
Proof using.
unfold eco, Execution.fr; relsf.
rewrite !seqA, !crE; relsf.
arewrite_false (co ⨾ rf⁻¹).
by rewrite (wf_coD WF), (wf_rfD WF); type_solver.
sin_rewrite !rf_transp_rf; auto.
basic_solver 8.
Qed.

(******************************************************************************)
(** ** implications of SC_PER_LOC  *)
(******************************************************************************)

Lemma no_co_to_init WF SC_PER_LOC : co ⊆ co ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
rewrite wf_coE at 1; try done.
unfolder; ins; splits; auto; desf; intro.
eapply SC_PER_LOC; exists x; splits; [|eby apply co_in_eco].
unfold Execution.sb; unfolder; splits; try done.
cut (~ is_init x).
by destruct x, y; ins.
intro.
assert (x=y).
eby apply (loceq_co WF) in H0; eapply init_same_loc.
eby subst; eapply (co_irr WF).
Qed.

Lemma no_fr_to_init WF SC_PER_LOC : fr ⊆ fr ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
unfold Execution.fr.
rewrite no_co_to_init at 1; try done.
basic_solver.
Qed.

Lemma co_from_init WF SC_PER_LOC : 
  ⦗fun x => is_init x⦘ ⨾ (same_loc \ (fun x y => x = y)) ⨾ ⦗E ∩₁ W⦘ ⊆ co.
Proof using.
unfolder; ins; desf.
generalize (init_w WF H); intro Wx.
generalize (is_w_loc lab x Wx).
unfold Events.same_loc in *; ins; desf.
eapply tot_ex.
- eapply WF.
- basic_solver.
- unfolder; splits; try edone.
  destruct x; [|unfold is_init in *; desf].
  eapply (wf_init WF); exists y; splits; eauto.
  unfold Events.loc in *.
  rewrite (wf_init_lab WF) in *.
  congruence.
- intro A.
  hahn_rewrite (no_co_to_init WF SC_PER_LOC) in A.
  unfolder in *; desf.
- intro; eauto.
Qed.

Lemma atomicity_alt WF SC_PER_LOC ATOM : rmw ∩ (fr ⨾ co) ⊆ ∅₂.
Proof using.
rewrite rmw_from_non_init, no_fr_to_init; eauto.
unfolder; red in ATOM; red in SC_PER_LOC; ins; desf.
destruct (classic (sb x z));
destruct (classic (sb z y)); eauto 8.
- by eapply wf_rmwi; eauto.
- eapply sb_semi_total_l with (y:=y) in H4; eauto.
  desf.
  eapply SC_PER_LOC.
  by eexists; splits; [eauto| apply co_in_eco].
  eby intro; subst; eapply (co_irr WF).
  eby apply rmw_in_sb.
- eapply sb_semi_total_r with (x:=y) (y:=x) in H5; eauto.
  desf.
  eapply SC_PER_LOC.
  by eexists; splits; [eauto| apply fr_in_eco].
  eby intro; subst; eapply fr_irr.
  eby apply rmw_in_sb.
- by eapply ATOM; unfolder; splits; eauto.
Qed.

Lemma BasicRMW WF SC_PER_LOC: irreflexive (co^? ⨾ rf ⨾ rmw).
Proof using.
rewrite rmw_in_sb; try done.
unfold sc_per_loc, eco in *; unfolder in *; basic_solver 10.
Qed.

Lemma w_r_loc_w_in_co WF r 
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘) (IRR: irreflexive r)
  (A: irreflexive (r ⨾ eco)): 
  ⦗W⦘ ⨾ r ∩ same_loc ⨾ ⦗W⦘ ⊆ co.
Proof using.
rewrite rE.
unfolder; ins; desf.
eapply tot_ex.
- eapply WF.
- unfolder; splits; try edone.
- unfolder; splits; try edone.
- intro; eapply A; unfold eco; basic_solver 12.
- intro; subst; eapply IRR; eauto.
Qed.

Lemma w_r_loc_r_in_co_rf WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘) 
  (A: irreflexive (r ⨾ eco)) COMP : 
  ⦗W⦘ ⨾ r ∩ same_loc ⨾ ⦗R⦘ ⊆ co^? ⨾ rf.
Proof using.
rewrite rE.
cut (⦗W⦘ ⨾  ⦗E⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ R⦘ ⊆ co^? ⨾ rf).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (dom_l (wf_rfE WF)) at 1.
rewrite (loceq_same_loc (loceq_rf WF)) at 1.
unfolder; ins; desf; eexists; splits; [|edone].
destruct (classic (x=z)); [eauto|].
right; eapply tot_ex.
- eapply WF.
- splits; try edone.
- splits; try edone.
- intro; eapply A.
unfold eco, Execution.fr; basic_solver 22.
- congruence. 
Qed.

Lemma r_r_loc_w_in_fr WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘) 
  (A: irreflexive (r ⨾ eco)) COMP : 
  ⦗R⦘ ⨾ r ∩ same_loc ⨾ ⦗W⦘ ⊆ fr.
Proof using.
rewrite rE.
cut (⦗E ∩₁ R⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ W⦘ ⊆ fr).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (dom_l (wf_rfE WF)) at 1.
rewrite (loceq_same_loc (loceq_rf WF)) at 1.
unfolder; ins; desf; eexists; splits; [edone|].
(* destruct (classic (x=z)); [eauto|]. *)
eapply tot_ex.
- eapply WF.
- splits; try edone.
- unfolder; splits; [done | done | unfolder in *; congruence].
- intro; eapply A.
unfold eco; basic_solver 22.
- intro; subst.  
eapply A.
unfold eco; basic_solver 22.
Qed.

Lemma r_r_loc_r_in_fr_rf WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘) 
  (A: irreflexive (r ⨾ eco)) COMP : 
  ⦗R⦘ ⨾ r ∩ same_loc ⨾ ⦗R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf.
Proof using.
rewrite rE.
cut (⦗E ∩₁ R⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1 2.
rewrite (dom_l (wf_rfE WF)) at 1 2.
rewrite (loceq_same_loc (loceq_rf WF)) at 1 2.
unfolder; ins; desf.
destruct (classic (z0=z)).
by right; eexists; subst; eauto.
left.
unfold Execution.fr; unfolder.
eexists; splits; [|edone].
eexists; splits; [edone|].
eapply tot_ex.
- eapply WF.
- splits; try edone.
- unfolder; splits; [done | done | unfolder in *; congruence].
- intro; eapply A.
unfold eco, Execution.fr; basic_solver 22.
- intro; subst; eauto.  
Qed.

Lemma w_sb_loc_w_in_coi WF SC_PER_LOC:
  ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ coi.
Proof using.
arewrite (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘) ∩ sb).
basic_solver.
rewrite (w_r_loc_w_in_co WF (@wf_sbE G) (@sb_irr G) SC_PER_LOC).
by ie_unfolder.
Qed.

Lemma w_sb_loc_r_in_co_rf WF SC_PER_LOC COMP:
  ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⊆ co^? ⨾ rf.
Proof using.
apply (w_r_loc_r_in_co_rf WF (@wf_sbE G) SC_PER_LOC COMP).
Qed.

Lemma r_sb_loc_w_in_fri WF SC_PER_LOC COMP:
  ⦗R⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ fri.
Proof using.
arewrite (⦗R⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ (⦗R⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘) ∩ sb).
basic_solver.
rewrite (r_r_loc_w_in_fr WF (@wf_sbE G) SC_PER_LOC COMP).
by ie_unfolder.
Qed.

Lemma r_sb_loc_r_in_fr_rf WF SC_PER_LOC COMP:
  ⦗R⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf.
Proof using.
apply (r_r_loc_r_in_fr_rf WF (@wf_sbE G) SC_PER_LOC COMP).
Qed.

Lemma rmw_in_fr WF SC_PER_LOC COMP : rmw ⊆ fr.
Proof using.
rewrite (wf_rmwD WF), (rmw_in_sb_loc WF).
rewrite (r_sb_loc_w_in_fri WF SC_PER_LOC COMP).
ie_unfolder; basic_solver.
Qed.

Lemma rf_rmw_in_co_helper WF SC_PER_LOC: rf ⨾ rmw ⊆ co ∪ co^{-1}.
Proof using.
rewrite (dom_l WF.(wf_rfE)).
rewrite (dom_r WF.(wf_rmwE)).
rewrite (dom_l WF.(wf_rfD)).
rewrite (dom_r WF.(wf_rmwD)).
unfolder; ins; desf.
eapply WF.(wf_co_total); [basic_solver| |].
{ unfolder; ins; desf; splits; eauto.
  apply WF.(wf_rfl) in H0.
  apply WF.(wf_rmwl) in H1.
  unfold Events.same_loc in *; congruence. }
intro; subst.
eapply SC_PER_LOC.
exists y; splits; eauto.
eapply WF.(rmw_in_sb); edone.
eapply rf_in_eco; edone.
Qed.

Lemma rf_rmw_in_co WF SC_PER_LOC : rf ⨾ rmw ⊆ co.
Proof using.
arewrite (rf ⨾ rmw ⊆ (rf ⨾ rmw) ∩ (rf ;; rmw)).
rewrite rf_rmw_in_co_helper at 1; eauto.
rewrite inter_union_l; unionL; [basic_solver|].
transitivity (fun _ _ : actid => False); [|basic_solver].
unfolder; ins; desf.
eapply SC_PER_LOC.
exists y; splits; eauto.
eapply WF.(rmw_in_sb); edone.
eapply co_rf_in_eco; basic_solver.
Qed.

Lemma rf_rmw_ct_in_co WF SC_PER_LOC : (rf ⨾ rmw)⁺ ⊆ co.
Proof using. by rewrite rf_rmw_in_co, (ct_of_trans (co_trans WF)). Qed.

Lemma rf_rmw_rt_in_co WF SC_PER_LOC : (rf ⨾ rmw)＊ ⊆ co^?.
Proof using. by rewrite rf_rmw_in_co, (rt_of_trans (co_trans WF)). Qed.

Lemma rf_rmw_in_coimm WF SC_PER_LOC ATOM: rf ⨾ rmw ⊆ immediate co.
Proof using.
ins; split; [by apply rf_rmw_in_co|].
ins; unfolder in *; desf.
eapply atomicity_alt; try done.
unfold Execution.fr; basic_solver 10.
Qed.

(******************************************************************************)
(** ** properties of external/internal relations *)
(******************************************************************************)

Lemma coe_coi WF SC_PER_LOC: coe ⨾ coi ⊆ coe.
Proof using.
cut ((co \ sb) ⨾ co ∩ sb ⊆ co ⨾ co \ sb).
by rewrite (co_co WF).
apply re_ri; try done; try by apply no_co_to_init.
by apply co_irr.
rotate 1.
by rewrite co_in_eco.
Qed.

Lemma fre_coi WF SC_PER_LOC : fre ⨾ coi ⊆ fre.
Proof using.
cut ((fr \ sb) ⨾ co ∩ sb ⊆ fr ⨾ co \ sb).
by rewrite (fr_co WF).
apply re_ri; try done; try by apply no_fr_to_init.
by apply fr_irr.
rotate 1.
by rewrite fr_in_eco.
Qed.

Lemma coi_coe WF SC_PER_LOC: 
 ⦗fun x => ~ is_init x⦘ ⨾ coi ⨾ coe ⊆ coe.
Proof using.
cut (⦗fun x => ~ is_init x⦘ ⨾ (co ∩ sb) ⨾ (co \ sb) ⊆ co ⨾ co \ sb).
by rewrite (co_co WF).
apply ri_re; try done; try by apply no_co_to_init.
by apply co_irr.
rotate 1.
by rewrite co_in_eco.
Qed.

Lemma eco_refl : 
  eco^? ⊆ ((co ∪ fre)^? ⨾ rf^?) ∪ fri ⨾ rfi^? ∪ fri ⨾ rfe.
Proof using.
unfold eco.
rewrite !(@fri_union_fre G).
rewrite !(@rfi_union_rfe G).
basic_solver 12.
Qed.

Lemma eco_alt4 WF : eco ⊆ ⦗RW⦘ ⨾ sb ∪ rfe ∪ co ⨾ rf^? ∪ fre ⨾ rf^? ∪ fri ⨾ rfe.
Proof using.
unfold eco.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (dom_l (wf_frD WF)) at 1.
rewrite !(@fri_union_fre G); relsf.
unionL.
- rewrite !(@rfi_union_rfe G).
  arewrite (rfi ⊆ sb) at 1.
  basic_solver 12.
- basic_solver 12.
- rewrite !(@rfi_union_rfe G).
  case_refl (rfi ∪ rfe).
  arewrite (fri ⊆ sb); basic_solver 12.
  relsf; unionL; [|basic_solver 12].
  arewrite (fri ⊆ sb); arewrite (rfi ⊆ sb).
  generalize (@sb_trans G).
  basic_solver 12.
- basic_solver 12.
Qed.

Lemma thread_rfe_sb WF SC_PER_LOC : (rfe^{-1} ⨾ sb) ∩ same_tid ⊆ ∅₂.
Proof using.
ie_unfolder; unfolder; unfold same_tid; ins; desf.
hahn_rewrite (@wf_sbE G) in H1; unfolder in H1; desf.
hahn_rewrite (wf_rfE WF) in H; unfolder in H; desf.
hahn_rewrite (no_rf_to_init WF) in H5; unfolder in H5; desf.
apply (@same_thread G) in H0; try done.
desf.
- destruct H0; [subst; auto|].
eapply sb_semi_total_r in H0; try edone.
2:  by intro; subst; eapply (rf_irr WF); edone.
desf; eapply SC_PER_LOC; unfold eco; basic_solver 12.
- eapply H2; eapply (@sb_trans G); edone. 
Qed.

Lemma co_sb_loc WF SC_PER_LOC : ⦗W⦘ ⨾ co^? ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ co^?.
Proof using.
  case_refl (sb ∩ same_loc); [basic_solver|].
  rewrite (dom_r (wf_coD WF)).
  arewrite (⦗W⦘ ⨾ (co ⨾ ⦗W⦘)^? ⊆ co^? ⨾ ⦗W⦘) by basic_solver.
  rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC), (dom_r (wf_coiD WF)).
  generalize (co_trans WF); ie_unfolder; basic_solver 12.
Qed.

End ECO.
