(******************************************************************************)
(** * Definition of the Power memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events Execution.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_ppo.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'fr'" := G.(fr).
Notation "'detour'" := G.(detour).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'F^isync'" := (F ∩₁ (fun a => is_true (is_rlx lab a))).

Implicit Type WF : Wf G.

(******************************************************************************)
(** ** PPO components *)
(******************************************************************************)

Definition ctrli := ⦗R⦘ ⨾ ctrl ⨾ ⦗F^isync⦘ ⨾  sb.

Definition rdw := (fre ⨾ rfe) ∩ sb.

Definition ii0 := addr ∪ data ∪ rdw ∪ rfi.
Definition ci0 := ctrli ⨾ ⦗RW⦘ ∪ detour.
Definition cc0 := data ∪ ctrl ⨾ ⦗RW⦘ ∪ addr ⨾ sb^? ⨾ ⦗RW⦘.

Inductive ii x y : Prop :=
      II0   : ii0 x y -> ii x y
    | CI    : ci x y -> ii x y
    | IC_CI : forall z, ic x z -> ci z y -> ii x y
    | II_II : forall z, ii x z -> ii z y -> ii x y
with ic x y : Prop := 
    | II    : ii x y -> ic x y
    | CC    : cc x y -> ic x y
    | IC_CC : forall z, ic x z -> cc z y -> ic x y
    | II_IC : forall z, ii x z -> ic z y -> ic x y
with ci x y : Prop := 
      CI0   : ci0 x y -> ci x y
    | CI_II : forall z, ci x z -> ii z y -> ci x y
    | CC_CI : forall z, cc x z -> ci z y -> ci x y
with cc x y : Prop := 
      CC0   : cc0 x y -> cc x y
    | CI_   : ci x y -> cc x y
    | CI_IC : forall z, ci x z -> ic z y -> cc x y
    | CC_CC : forall z, cc x z -> cc z y -> cc x y.

Scheme ii_rec := Minimality for ii Sort Prop
  with ic_rec := Minimality for ic Sort Prop
  with ci_rec := Minimality for ci Sort Prop
  with cc_rec := Minimality for cc Sort Prop.

Combined Scheme ppo_comp_ind from ii_rec, ic_rec, ci_rec, cc_rec.

(* Preserved program order *)
Definition ppo := ⦗R⦘ ⨾ ii ⨾ ⦗R⦘ ∪ ⦗R⦘ ⨾ ic ⨾ ⦗W⦘.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_ctrliE WF: ctrli ≡ ⦗E⦘ ⨾ ctrli ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ctrli.
sin_rewrite (wf_ctrlE WF).
sin_rewrite (wf_sbE).
basic_solver 42.
Qed.

Lemma wf_rdwE WF: rdw ≡ ⦗E⦘ ⨾ rdw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold rdw.
sin_rewrite (wf_freE WF).
sin_rewrite (wf_rfeE WF).
basic_solver 42.
Qed.

Lemma wf_ii0E WF: ii0 ≡ ⦗E⦘ ⨾ ii0 ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ii0.
rewrite (wf_addrE WF) at 1.
rewrite (wf_dataE WF) at 1.
rewrite (wf_rdwE WF) at 1.
rewrite (wf_rfiE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_ci0E WF: ci0 ≡ ⦗E⦘ ⨾ ci0 ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ci0.
rewrite (wf_ctrliE WF) at 1.
rewrite (wf_detourE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_cc0E WF: cc0 ≡ ⦗E⦘ ⨾ cc0 ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold cc0.
rewrite (wf_dataE WF) at 1.
rewrite (wf_ctrlE WF) at 1.
rewrite (wf_addrE WF) at 1.
rewrite (wf_sbE) at 1.
basic_solver 42.
Qed.

Lemma wf_helperE WF:
forall x y,
(ii x y -> E x /\ E y) /\
(ic x y -> E x /\ E y) /\
(ci x y -> E x /\ E y) /\ 
(cc x y -> E x /\ E y).
Proof.
generalize (dom_to_doma (wf_ii0E WF)) (dom_to_domb (wf_ii0E WF)).
generalize (dom_to_doma (wf_ci0E WF)) (dom_to_domb (wf_ci0E WF)).
generalize (dom_to_doma (wf_cc0E WF)) (dom_to_domb (wf_cc0E WF)).
unfolder; intros A1 A2 A3 A4 A5 A6.
apply ppo_comp_ind; basic_solver.
Qed.

Lemma wf_iiE WF: ii ≡ ⦗E⦘ ⨾ ii ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply wf_helperE in H; desf.
Qed.

Lemma wf_icE WF: ic ≡ ⦗E⦘ ⨾ ic ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply wf_helperE in H; desf.
Qed.

Lemma wf_ciE WF: ci ≡ ⦗E⦘ ⨾ ci ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply wf_helperE in H; desf.
Qed.

Lemma wf_ccE WF: cc ≡ ⦗E⦘ ⨾ cc ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply wf_helperE in H; desf.
Qed.

Lemma wf_ppoE WF: ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ppo.
rewrite (wf_iiE WF) at 1.
rewrite (wf_icE WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_ctrliD : ctrli ⊆ ⦗R⦘ ⨾ ctrli.
Proof.
unfold ctrli; basic_solver 12.
Qed.

Lemma wf_rdwD WF : rdw ≡ ⦗R⦘ ⨾ rdw ⨾ ⦗R⦘.
Proof.
split; [|basic_solver].
unfold rdw.
sin_rewrite (wf_freD WF).
sin_rewrite (wf_rfeD WF).
basic_solver 42.
Qed.

Lemma wf_ppoD WF: ppo ≡ ⦗R⦘ ⨾ ppo ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfold ppo.
type_solver 42.
Qed.

Lemma wf_ii0D WF: ii0 ≡ ⦗RW⦘ ⨾ ii0 ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfold ii0.
rewrite (wf_addrD WF) at 1.
rewrite (wf_dataD WF) at 1.
rewrite (wf_rdwD WF) at 1.
rewrite (wf_rfiD WF) at 1.
type_solver 42.
Qed.

Lemma wf_ci0D WF: ci0 ≡ ⦗RW⦘ ⨾ ci0 ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfold ci0.
rewrite wf_ctrliD at 1.
rewrite (wf_detourD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_cc0D WF: cc0 ≡ ⦗RW⦘ ⨾ cc0 ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfold cc0.
rewrite (wf_dataD WF) at 1.
rewrite (wf_ctrlD WF) at 1.
rewrite (wf_addrD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_helperD WF:
forall x y,
(ii x y -> RW x /\ RW y) /\
(ic x y -> RW x /\ RW y) /\
(ci x y -> RW x /\ RW y) /\ 
(cc x y -> RW x /\ RW y).
Proof.
generalize (dom_to_doma (wf_ii0D WF)) (dom_to_domb (wf_ii0D WF)).
generalize (dom_to_doma (wf_ci0D WF)) (dom_to_domb (wf_ci0D WF)).
generalize (dom_to_doma (wf_cc0D WF)) (dom_to_domb (wf_cc0D WF)).
unfolder; intros A1 A2 A3 A4 A5 A6.
apply ppo_comp_ind; basic_solver.
Qed.

Lemma wf_iiD WF: ii ≡ ⦗RW⦘ ⨾ ii ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply (wf_helperD WF) in H; desc; eauto.
Qed.

Lemma wf_icD WF: ic ≡ ⦗RW⦘ ⨾ ic ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply (wf_helperD WF) in H; desc; eauto.
Qed.

Lemma wf_ciD WF: ci ≡ ⦗RW⦘ ⨾ ci ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply (wf_helperD WF) in H; desc; eauto.
Qed.

Lemma wf_ccD WF: cc ≡ ⦗RW⦘ ⨾ cc ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfolder; ins; splits; try done; eapply (wf_helperD WF) in H; desc; eauto.
Qed.

(******************************************************************************)
(** ** Inclusion *)
(******************************************************************************)
Lemma ctrli_in_sb WF : ctrli ⊆ sb.
Proof. 
unfold ctrli.
rewrite (ctrl_in_sb WF).
generalize (@sb_trans G); basic_solver.
Qed.

Lemma ctrli_sb : ctrli ⨾ sb ⊆ ctrli.
Proof.
unfold ctrli.
generalize (@sb_trans G); basic_solver 12.
Qed.

Lemma ctrli_in_ctrl WF : ctrli ⊆ ctrl.
Proof. 
unfold ctrli.
generalize (ctrl_sb WF); basic_solver.
Qed.

Lemma ii0_in_ii : ii0 ⊆ ii.
Proof. vauto. Qed.
Lemma ci0_in_ci : ci0 ⊆ ci.
Proof. vauto. Qed.
Lemma cc0_in_cc : cc0 ⊆ cc.
Proof. vauto. Qed.

Lemma ci_in_ii : ci ⊆ ii.
Proof. vauto. Qed.
Lemma ci_in_ic : ci ⊆ ic.
Proof. vauto. Qed.
Lemma ii_in_ic : ii ⊆ ic.
Proof. vauto. Qed.
Lemma ci_in_cc : ci ⊆ cc.
Proof. vauto. Qed.
Lemma cc_in_ic : cc ⊆ ic.
Proof. vauto. Qed.

Lemma ic_ci_in_ii : ic ⨾ ci ⊆ ii.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ii_ii_in_ii : ii ⨾ ii ⊆ ii.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ic_cc_in_ic : ic ⨾ cc ⊆ ic.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ii_ic_in_ic : ii ⨾ ic ⊆ ic.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ci_ii_in_ci : ci ⨾ ii ⊆ ci.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma cc_ci_in_ci : cc ⨾ ci ⊆ ci.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ci_ic_in_cc : ci ⨾ ic ⊆ cc.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma cc_cc_in_cc : cc ⨾ cc ⊆ cc.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ii_cc_in_ic : ii ⨾ cc ⊆ ic.
Proof. unfolder; ins; desf; vauto. Qed.

Lemma ii0_in_sb WF: ii0 ⊆ sb.
Proof.
unfold ii0, rdw; ie_unfolder.
rewrite addr_in_sb, data_in_sb; try done.
basic_solver 42.
Qed.

Lemma ci0_in_sb WF: ci0 ⊆ sb.
Proof.
unfold ci0, Execution.detour.
rewrite ctrli_in_sb; try done.
basic_solver 42.
Qed.

Lemma cc0_in_sb WF: cc0 ⊆ sb.
Proof.
unfold cc0.
rewrite addr_in_sb, data_in_sb, ctrl_in_sb; try done.
generalize (@sb_trans G).
basic_solver 42.
Qed.

Lemma in_sb_helper WF:
forall x y,
(ii x y -> sb x y) /\
(ic x y -> sb x y) /\
(ci x y -> sb x y) /\ 
(cc x y -> sb x y).
Proof.
generalize (ii0_in_sb WF) (ci0_in_sb WF) (cc0_in_sb WF).
generalize (@sb_trans G).
unfolder; intros A A1 A2 A3.
apply ppo_comp_ind; basic_solver.
Qed.

Lemma ii_in_sb WF: ii ⊆ sb.
Proof.
unfolder; ins; splits; try done; eapply in_sb_helper in H; desf.
Qed.

Lemma ic_in_sb WF: ic ⊆ sb.
Proof.
unfolder; ins; splits; try done; eapply in_sb_helper in H; desf.
Qed.

Lemma ci_in_sb WF: ci ⊆ sb.
Proof.
unfolder; ins; splits; try done; eapply in_sb_helper in H; desf.
Qed.

Lemma cc_in_sb WF: cc ⊆ sb.
Proof.
unfolder; ins; splits; try done; eapply in_sb_helper in H; desf.
Qed.
Lemma ppo_in_sb WF : ppo ⊆ sb.
Proof.
unfold ppo.
rewrite ii_in_sb, ic_in_sb; try done.
basic_solver.
Qed.

Lemma rdw_in_ppo WF : rdw ⊆ ppo.
Proof.
unfold ppo.
rewrite (wf_rdwD WF).
rewrite <- ii0_in_ii.
unfold ii0; basic_solver 42.
Qed.

Lemma rfi_in_ii : rfi ⊆ ii.
Proof.
rewrite <- ii0_in_ii.
unfold ii0; basic_solver 42.
Qed.

Lemma detour_in_ci : detour ⊆ ci.
Proof.
rewrite <- ci0_in_ci.
unfold ci0; basic_solver 42.
Qed.

Lemma detour_in_ii : detour ⊆ ii.
Proof.
by rewrite <- ci_in_ii, detour_in_ci.
Qed.

Lemma data_in_ii : data ⊆ ii.
Proof.
rewrite <- ii0_in_ii.
unfold ii0; basic_solver 42.
Qed.

Lemma addr_in_ii : addr ⊆ ii.
Proof.
rewrite <- ii0_in_ii.
unfold ii0; basic_solver 42.
Qed.

Lemma ctrl_in_cc : ctrl ⨾ ⦗RW⦘ ⊆ cc.
Proof.
rewrite <- cc0_in_cc.
unfold cc0; basic_solver 42.
Qed.

Lemma addr_sb_in_cc : addr ⨾ sb^? ⨾ ⦗RW⦘ ⊆ cc.
Proof.
rewrite <- cc0_in_cc.
unfold cc0; basic_solver 42.
Qed.

Lemma deps_in_ppo WF: deps ⨾ ⦗W⦘ ⊆ ppo.
Proof.
unfold Execution.deps, ppo.
rewrite (wf_dataD WF), (wf_addrD WF), (wf_ctrlD WF).
rewrite data_in_ii, addr_in_ii.
generalize ii_in_ic cc_in_ic ctrl_in_cc.
basic_solver 42.
Qed.

Lemma addrsbW_in_ppo WF: addr ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof.
unfold ppo.
rewrite <- cc_in_ic, <- cc0_in_cc.
rewrite (wf_addrD WF) at 1.
unfold cc0; basic_solver 42.
Qed.

Lemma rdw_rbi_in_rbi WF: rdw ⨾ fri ⊆ fri.
Proof.
unfold rdw; ie_unfolder.
generalize (rf_fr WF) (fr_co WF) (@sb_trans G).
basic_solver 42.
Qed.

Lemma ctrli_fri_in_ci0 WF: ctrli ⨾ fri ⊆ ci0.
Proof.
rewrite (wf_friD WF).
arewrite (⦗R⦘ ⨾ fri ⊆ sb).
by ie_unfolder; basic_solver.
sin_rewrite ctrli_sb.
unfold ci0; type_solver.
Qed.

Lemma ctrli_fri_in_cc0 WF: ctrli ⨾ fri ⊆ cc0.
Proof.
rewrite (wf_friD WF).
arewrite (⦗R⦘ ⨾ fri ⊆ sb).
by ie_unfolder; basic_solver.
sin_rewrite ctrli_sb.
rewrite (ctrli_in_ctrl WF).
unfold cc0; basic_solver 12.
Qed.

Lemma R_ci0_W_in_ppo : ⦗R⦘ ⨾ ci0 ⨾ ⦗W⦘ ⊆ ppo.
Proof.
unfold ppo.
rewrite <- ci_in_ic, <- ci0_in_ci.
basic_solver.
Qed.


(******************************************************************************)
(** ** L <-> PPO components *)
(******************************************************************************)
(* Single-transition definition *)
Inductive L x y : Prop :=
  | L_cc      : cc0 x y -> L x y
  | L_Li      : Li x y -> L x y
  | L_L_cc    : forall z, L x z -> cc0 z y -> L x y
with Li x y : Prop :=
  | Li_ci     : ci0 x y -> Li x y
  | Li_ii     : ii0 x y -> Li x y
  | Li_L_ci   : forall z, L x z -> ci0 z y -> Li x y
  | Li_Li_ii  : forall z, Li x z -> ii0 z y -> Li x y.

Scheme L_rec := Minimality for L Sort Prop
  with Li_rec := Minimality for Li Sort Prop.

Combined Scheme L_comb from L_rec, Li_rec.


Lemma L_in_union : L ⊆ ii ∪ ic ∪ ci ∪ cc.
Proof.
  red; ins.
  apply L_rec with (x:=x) 
  (P:=fun y => (ii ∪ ic ∪ ci ∪ cc) x y) (P0:=fun y => (ii ∪ ci) x y);
  auto; ins; try vauto; try (by unfolder in *; desf; (right + left); vauto).
  - left; left; right; unfolder in *; desf; vauto.
    assert (ci ⊆ ic) by (unfolder; vauto).
    apply H3 in H1; vauto.
Qed.

Lemma seq_alt A (r r' r'' : relation A) :
  (forall x y, r' x y -> forall z, r z x -> r'' z y) <->
  r ⨾ r' ⊆ r''.
Proof.
  split.
  - ins; red; ins; unfold seq in H0; desf; eapply H; eauto; edone.
  - unfolder; ins; apply H; eexists; splits; eauto.
Qed.

Lemma basic_to_transitional : 
  (Li^? ⨾ ii ⊆ Li) /\
  (Li^? ⨾ ic ⊆ L) /\
  (L^? ⨾ ci ⊆ Li) /\
  (L^? ⨾ cc ⊆ L).
Proof.
  rewrite <- !seq_alt.
  cut (forall x y, 
    (ii x y -> forall z, Li^? z x -> Li z y) /\ 
    (ic x y -> forall z, Li^? z x -> L z y) /\
    (ci x y -> forall z, L^? z x -> Li z y) /\
    (cc x y -> forall z, L^? z x -> L z y)).
  { ins; splits; ins; desf;
    specialize (H x y); desf; eauto. }
  apply ppo_comp_ind with 
  (*ii*) (P:=fun x y => forall z, (Li^?) z x -> Li z y)
  (*ic*) (P0:=fun x y => forall z, (Li^?) z x -> L z y)
  (*ci*) (P1:=fun x y => forall z, (L^?) z x -> Li z y)
  (*cc*) (P2:=fun x y => forall z, (L^?) z x -> L z y);
  rewrite ?seq_alt;
  (* base cases *)
  try (by unfolder; ins; desf; vauto);
  ins;
  (* single derivations *)
  try (by apply H2; right; apply H0);
  (* double derivations *)
  try (by apply H0; red in H1; desf; (left + right); vauto);
  by apply L_Li, H0.
Qed.

Lemma L_Li_in_ppo_components : Li ⊆ ii ∪ ci /\ L ⊆ ii ∪ ic ∪ ci ∪ cc.
Proof.
  unfolder.
  assert (forall x y,
    (L x y -> ii x y \/ ic x y \/ ci x y \/ cc x y) /\ 
    (Li x y -> ii x y \/ ci x y)
  ).
  { ins; apply L_comb with
      (P := fun y => ii x y \/ ic x y \/ ci x y \/ cc x y)
      (P0 := fun y => ii x y \/ ci x y);
    auto; ins.
    all: try by vauto.
    all: try by (desf; by (left + right); vauto).
    all: try by (desf; by repeat right; vauto).
    desf; by (right; left + (repeat right)); vauto.
  }
  split; ins; specialize (H x y); desf; intuition.
Qed.

Lemma Li_is_ii : Li ≡ ii.
Proof.
  split.
  - arewrite (Li ⊆ ii ∪ ci) by apply L_Li_in_ppo_components.
    rewrite ci_in_ii.
    basic_solver.
  - generalize basic_to_transitional.
basic_solver 12.
Qed.

Lemma L_is_ic : L ≡ ic.
Proof.
  split.
  - arewrite (L ⊆ ii ∪ ic ∪ ci ∪ cc) by apply L_Li_in_ppo_components.
  rewrite ii_in_ic, ci_in_ic, cc_in_ic; basic_solver.
  - red; ins.
    assert (Li^? ⨾ ic ⊆ L) by apply basic_to_transitional.
    apply H0; eexists; splits; eauto.
Qed.

Lemma wf_LD WF: L ⊆ ⦗RW⦘ ⨾ L ⨾ ⦗RW⦘.
Proof.
by rewrite L_is_ic; apply wf_icD. 
Qed.

Lemma wf_LiD WF: Li ⊆ ⦗RW⦘ ⨾ Li ⨾ ⦗RW⦘.
Proof.
by rewrite Li_is_ii; apply wf_iiD. 
Qed.

Lemma L_in_ppo : ⦗R⦘ ⨾ L ⨾ ⦗W⦘ ⊆ ppo.
Proof.
rewrite L_is_ic; unfold ppo; basic_solver.
Qed.

Lemma Li_in_ppo WF: ⦗R⦘ ⨾ Li ⊆ ppo.
Proof.
rewrite Li_is_ii; unfold ppo.
rewrite (wf_iiD WF) at 1.
generalize ii_in_ic.
basic_solver 42.
Qed.

Lemma Li_in_L : Li ⊆ L.
Proof. vauto. Qed.

Lemma ppo_in_L WF: ppo ⊆ ⦗R⦘ ⨾ L.
Proof.
unfold ppo.
rewrite L_is_ic, ii_in_ic.
rewrite (wf_icD WF) at 3.
basic_solver.
Qed.

Lemma ppo_R_in_R_Li WF: ppo ⨾ ⦗R⦘ ⊆ ⦗R⦘ ⨾ Li.
Proof.
rewrite (wf_ppoD WF), Li_is_ii.
unfold ppo; type_solver 12.
Qed.

Lemma ppo_W_in_R_L WF: ppo ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ L.
Proof.
rewrite (wf_ppoD WF), L_is_ic.
unfold ppo; type_solver 12.
Qed.

(******************************************************************************)
(** ** Extra *)
(******************************************************************************)

Lemma deps_in_cc: deps ⨾ ⦗RW⦘ ⊆ cc.
Proof.
rewrite <- cc0_in_cc.
unfold Execution.deps, cc0; basic_solver 42.
Qed.

Lemma deps_in_ic : deps ⨾ ⦗RW⦘ ⊆ ic.
Proof.
rewrite <- cc_in_ic.
by apply deps_in_cc.
Qed.

(*
Lemma ctrl_sb_W_in_ppo WF: ctrl ⨾ sb ⨾ ⦗W⦘ ⊆ ppo ⨾ ⦗W⦘.
Proof.
unfold ppo.
rewrite (wf_ctrlD WF).
rewrite !seqA.
sin_rewrite (ctrl_sb WF).
rewrite <- cc_in_ic.
rewrite <- ctrl_in_cc.
basic_solver 42.
Qed.
*)

Lemma ctrli_RW_in_ic: ctrli ⨾ ⦗RW⦘ ⊆ ic.
Proof.
rewrite <- ci_in_ic, <- ci0_in_ci; vauto.
Qed.

Lemma ctrli_R_in_ii: ctrli ⨾ ⦗RW⦘ ⊆ ii.
Proof.
rewrite <- ci_in_ii, <- ci0_in_ci; vauto.
Qed.

Lemma ctrl_ctrli_in_ii WF: ctrl ⨾ ctrli ⨾ ⦗RW⦘ ⊆ ii.
Proof.
rewrite wf_ctrliD.
unfolder; ins; desc.
eapply CI, CC_CI.
apply CC0; unfold cc0; basic_solver 12.
apply CI0; unfold ci0; basic_solver 12.
Qed.


Lemma ctrl_ctrli_RW_in_ppo WF: ctrl ⨾ ctrli ⨾ ⦗RW⦘ ⊆ ppo.
Proof.
rewrite (wf_ctrlD WF).
arewrite (⦗RW⦘ ⊆ ⦗RW⦘ ⨾ ⦗RW⦘) by basic_solver.
sin_rewrite (ctrl_ctrli_in_ii WF).
unfold ppo.
generalize ii_in_ic.
basic_solver 12.
Qed.

Lemma ctrli_RW_in_ppo WF : ctrli ⨾ ⦗RW⦘ ⊆ ppo.
Proof.
unfold ppo.
rewrite wf_ctrliD.
generalize ctrli_RW_in_ic, ctrli_R_in_ii.
basic_solver 12.
Qed.

(******************************************************************************)
(** ** Propositions *)
(******************************************************************************)

Lemma ppo_trans : transitive ppo.
Proof.
  unfold transitive, ppo; unfolder.
  ins; desf; try type_solver.
  by left; exists z2; split; auto; exists z; vauto.
  by right; exists z2; split; auto; exists z; splits; vauto.
Qed.

Lemma ct_ppo_ctrli_rw_in_ppo WF : (ppo ∪ ctrli)⁺ ⨾ ⦗RW⦘ ⊆ ppo.
Proof.
apply ct_ind_left with (P:= fun r => r ⨾ ⦗RW⦘).
- by eauto with hahn.
- generalize ctrli_RW_in_ppo; basic_solver.
- ins; rewrite !seqA, H.
  rewrite (dom_l (wf_ppoD WF)) at 2. 
  relsf.
  arewrite (ctrli ⨾ ⦗R⦘ ⊆ ppo).
  by generalize ctrli_RW_in_ppo; basic_solver.
  generalize ppo_trans; basic_solver.
Qed.

Lemma deps_R_in_ppo WF: 
  (deps ∪ addr ⨾ sb) ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof.
 arewrite ((deps ∪ addr ⨾ sb) ⨾ ⦗R⦘ ⊆ ctrl ∪ addr ⨾ sb^?).
  by unfold Execution.deps; rewrite (wf_dataD WF); type_solver 42.
relsf.
sin_rewrite (ctrl_sb WF).
arewrite (ctrl ⊆ deps).
generalize (addrsbW_in_ppo WF) (deps_in_ppo WF).
generalize (@sb_trans G).
basic_solver 42.
Qed.

Lemma ci0_fri WF:  ci0 ⨾ fri ⊆ ppo ∪ co.
Proof.
unfold ci0.
rewrite wf_ctrliD at 1.
rewrite (wf_friD WF) at 1.
generalize (ctrli_fri_in_ci0 WF), (R_ci0_W_in_ppo).
generalize (detour_fr_in_co WF).
ie_unfolder.
basic_solver 42.
Qed.

Lemma L_ctrli_fri WF:  ⦗R⦘ ⨾  L ⨾ ctrli ⨾ fri ⊆ ppo.
Proof.
rewrite (dom_r (wf_friD WF)).
rewrite <- L_in_ppo.
rewrite (ctrli_in_ctrl WF).
arewrite (fri ⊆ sb).
sin_rewrite (ctrl_sb WF). 
unfolder; splits; auto; desf.
apply L_L_cc with z; auto.
unfold cc0; basic_solver 20.
Qed.

Lemma ppo_fri WF : ppo ⨾ fri ⊆ ppo ∪ ppo ⨾ co ∪ co ∪ fri.
Proof.
rewrite (wf_friD WF) at 1.
rels.
sin_rewrite ppo_R_in_R_Li; auto.
red; ins. unfolder in H; desf.
unfolder in H; desf; subst.
rename y into c, x into a, z into b.
apply Li_rec with (P:=L a)
 (P0:=(fun b => fri b c -> (ppo ∪ ppo ⨾ co ∪ co ∪ fri) a c)) in H2; eauto; ins; vauto.
- cut ((ppo ∪ co) a c).
  by basic_solver.
  generalize (ci0_fri WF).
  basic_solver.
- (* ii0 *)
  red in H3; unfolder in H3; desf.
  + (* addr *)
    generalize (addrsbW_in_ppo WF).
    ie_unfolder.
    unfolder in *.
    basic_solver 12.
    + (* data *)
    exfalso.
    apply (wf_dataD WF) in H3.
    apply (wf_friD WF) in H4.
    unfolder in *; type_solver.
    + (* rdw *)
    generalize (rdw_rbi_in_rbi WF); basic_solver 12.
    + (* rf∙ *)
    generalize (rf_fr WF).
    ie_unfolder.
    unfolder in *;  basic_solver 12.
- (* ci0 *)
  unfold ci0 in *; unfolder in *; desf.
  + (* ctrli *)
    generalize (L_ctrli_fri WF); basic_solver 12.
  + (* ctrli *)
    generalize (L_ctrli_fri WF); basic_solver 12.
  + (* detour *)
    apply (wf_detourD WF) in H5.
    generalize (detour_fr_in_co WF) L_in_ppo.
    ie_unfolder.
    unfolder in *; basic_solver 42.
- unfold ii0 in *; unfolder in *; desf.
  + (* addr *)
    hahn_rewrite (wf_friD WF) in H6; unfolder in H6; desc.
    do 3 left.
    apply L_in_ppo.
    unfolder. splits; auto. 
    apply L_L_cc with z; vauto.
    unfold cc0.
    ie_unfolder.
    unfolder in *; basic_solver 42.
  + (* data *)
    exfalso.
    apply (wf_dataD WF) in H5.
    apply (wf_friD WF) in H6.
    unfolder in *; type_solver.
  + (* rdw *)
    generalize (rdw_rbi_in_rbi WF).
    basic_solver 12.
  + (* rf∙ *)
    do 2 left; right.
    eexists.
    split.
    * generalize L_in_ppo, L_Li.
      apply (wf_rfiD WF) in H5.
      unfolder in *; basic_solver 12.
    * generalize (rf_fr WF).
      ie_unfolder.
      unfolder in *; basic_solver.
Qed.

Lemma deps_rfi WF : 
  (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⊆ ctrl ∪ addr ⨾ sb^? ∪ ii ⨾ (ctrl ∪ addr ⨾ sb^?)^?.
Proof.
eapply ct_ind_left with (P:= fun x : _ => x).
by eauto with hahn.
by rewrite <- ii0_in_ii; unfold ii0; basic_solver 12.
intros k H; desf; rewrite H; clear H.
rewrite rfi_in_ii, data_in_ii at 1.
arewrite (ii ∪ ctrl ∪ addr ⨾ sb^? ∪ ii ⊆ ii ∪ ctrl ∪ addr ⨾ sb^?).
rewrite !seq_union_l; unionL.
- by generalize ii_ii_in_ii; basic_solver 12.
- rewrite (ctrl_in_sb WF) at 2 3.
rewrite (ii_in_sb WF) at 1.
rewrite (addr_in_sb WF) at 1 2.
generalize (ctrl_sb WF) (@sb_trans G); basic_solver 12.
- rewrite (ctrl_in_sb WF) at 1 2.
rewrite (ii_in_sb WF) at 1.
rewrite (addr_in_sb WF) at 2 3.
generalize (@sb_trans G); basic_solver 12.
Qed.

Lemma r_deps_rfi WF: ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo.
Proof.
rewrite (deps_rfi WF).
unfold ppo.
rewrite (wf_ctrlD WF) at 1.
rewrite (dom_l (wf_iiD WF)) at 1.
generalize addr_sb_in_cc, ctrl_in_cc, ii_in_ic, ii_cc_in_ic, cc_in_ic; basic_solver 22.
Qed.

(*
Lemma r_deps_rfi_w WF : ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo ⨾ ⦗W⦘.
Proof.
rewrite (deps_rfi WF).
unfold ppo.
rewrite (wf_ctrlD WF) at 1.
rewrite (dom_l (wf_iiD WF)) at 1.
generalize ctrl_in_cc, ii_in_ic, ii_cc_in_ic, cc_in_ic; basic_solver 22.
Qed.
*)

Lemma ppo_detour_ppo WF : ppo ⨾  detour ⨾  ppo^?  ⊆ ppo.
Proof.
rewrite (wf_detourD WF).
unfold ppo.
rewrite detour_in_ci.
relsf; rewrite !seqA.
arewrite_false !(⦗R⦘ ⨾ ⦗W⦘); [by type_solver|].
generalize ic_ci_in_ii, ii_ii_in_ii, ii_ic_in_ic; basic_solver 22.
Qed.

Lemma ppo_rt_detour_ppo WF : ppo ⨾ (detour ⨾ ppo^?)⁺ ⊆ ppo.
Proof.
eapply ct_ind_left. 
by eauto with hahn.
apply (ppo_detour_ppo WF).
intros k H; desf; rewrite !seqA.
by sin_rewrite (ppo_detour_ppo WF).
Qed.

Lemma r_ct_ppo_detour_ppo WF: ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour)⁺ ⨾ ⦗RW⦘ ⊆ ppo.
Proof.
rewrite path_union.
rewrite (dom_l (wf_detourD WF)) at 1.
relsf.
rewrite (ct_ppo_ctrli_rw_in_ppo WF).
arewrite (⦗W⦘ ⊆ ⦗RW⦘).
arewrite !((ppo ∪ ctrli)＊ ⨾ ⦗RW⦘ ⊆ ppo^?).
by generalize (ct_ppo_ctrli_rw_in_ppo WF); basic_solver 12.
arewrite !((ppo ∪ ctrli)＊ ⨾ ⦗RW⦘ ⊆ ppo^?).
by generalize (ct_ppo_ctrli_rw_in_ppo WF); basic_solver 12.
apply inclusion_union_l.
by basic_solver.
rewrite ct_seq_swap, ct_begin.
rewrite (dom_l (wf_detourD WF)) at 1; rewrite !seqA.
arewrite (⦗R⦘ ⨾ ppo^? ⨾ ⦗W⦘ ⊆ ppo) by type_solver.
arewrite (detour ⨾ ppo^? ⨾ (detour ⨾ ppo^?)＊ ⊆ (detour ⨾ ppo^?)⁺).
by rewrite <- seqA, <- ct_begin.
apply (ppo_rt_detour_ppo WF).
Qed.







End Power_ppo.
