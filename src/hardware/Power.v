(******************************************************************************)
(** * Definition of the Power memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Power_fences.
Require Import Power_ppo.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power.

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
Notation "'ctrli'" := G.(ctrli).
Notation "'deps'" := G.(deps).
Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).

Notation "'sync'" := G.(sync).
Notation "'lwsync'" := G.(lwsync).
Notation "'fence'" := G.(fence).
Notation "'ppo'" := G.(ppo).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'F^lwsync'" := (F ∩₁ (fun a => is_true (is_ra lab a))).
Notation "'F^sync'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* Power happens-before *)
Definition hb := ppo ∪ fence ∪ rfe.

(* Propagation order *)
Definition prop1 := ⦗W⦘ ⨾ rfe^? ⨾ fence ⨾ hb＊ ⨾ ⦗W⦘.
Definition prop2 := (coe ∪ fre)^? ⨾ rfe^? ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊.
Definition prop := prop1 ∪ prop2.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Definition PowerConsistent :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: sc_per_loc G ⟫ /\
  ⟪ POWER_ATOMICITY : rmw_atomicity G ⟫ /\
  ⟪ OBSERVATION : irreflexive (fre ⨾ prop ⨾ hb＊) ⟫ /\
  ⟪ PROPAGATION : acyclic (co ∪ prop) ⟫ /\
  ⟪ NO_THIN_AIR: acyclic hb ⟫.

Implicit Type CON : PowerConsistent.

Lemma CON_WF CON : Wf G.
Proof. apply CON. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_hbE WF: hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold hb.
rewrite (wf_ppoE WF) at 1.
rewrite (wf_fenceE WF) at 1.
rewrite (wf_rfeE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_prop1E WF: prop1 ≡ ⦗E⦘ ⨾ prop1 ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold prop1.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_fenceE WF) at 1.
rewrite <- cr_of_ct.
rewrite inclusion_t_t at 1; [|eapply (wf_hbE WF)].
arewrite ((⦗E⦘ ⨾ hb ⨾ ⦗E⦘)⁺ ⊆ ⦗E⦘ ⨾ hb⁺ ⨾ ⦗E⦘).
by rewrite <- inclusion_ct_seq_eqv_r; rewrite <- inclusion_ct_seq_eqv_l.
basic_solver 42.
Qed.

Lemma wf_prop2E WF: prop2 ≡ ⦗E⦘ ⨾ prop2 ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold prop2.
rewrite (wf_coeE WF) at 1.
rewrite (wf_freE WF) at 1.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_fenceE WF) at 1.
rewrite (wf_syncE WF) at 1.
rewrite <- cr_of_ct.
rewrite inclusion_t_t at 2; [|eapply (wf_hbE WF)].
arewrite ((⦗E⦘ ⨾ hb ⨾ ⦗E⦘)⁺ ⊆ ⦗E⦘ ⨾ hb⁺ ⨾ ⦗E⦘).
by rewrite <- inclusion_ct_seq_eqv_r; rewrite <- inclusion_ct_seq_eqv_l.
basic_solver 42.
Qed.

Lemma wf_propE WF: prop ≡ ⦗E⦘ ⨾ prop ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold prop.
rewrite (wf_prop1E WF) at 1.
rewrite (wf_prop2E WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_hbD WF: hb ≡ ⦗RW⦘ ⨾ hb ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
unfold hb.
rewrite (wf_ppoD WF) at 1.
rewrite (wf_fenceD WF) at 1.
rewrite (wf_rfeD WF) at 1.
type_solver 42.
Qed.

Lemma wf_cthbD WF: hb⁺ ≡ ⦗RW⦘ ⨾ hb⁺ ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
rewrite (dom_r (wf_hbD WF)) at 1.
rewrite inclusion_ct_seq_eqv_r at 1.
rewrite (dom_l (wf_hbD WF)) at 1.
rewrite inclusion_ct_seq_eqv_l at 1.
basic_solver.
Qed.

(******************************************************************************)
(** ** Inclusion *)
(******************************************************************************)

Lemma rfe_in_hb : rfe ⊆ hb.
Proof.
vauto.
Qed.

Lemma fence_in_hb : fence ⊆ hb.
Proof.
vauto.
Qed.

Lemma ctrli_RW_in_hb WF : ctrli ⨾ ⦗RW⦘ ⊆ hb.
Proof.
unfold hb; rewrite ctrli_RW_in_ppo; basic_solver.
Qed.

(******************************************************************************)
(** ** Extra *)
(******************************************************************************)

Lemma hb_helper WF: hb＊ ⊆ sb^? ∪ sb^? ⨾ rfe ⨾ hb＊.
Proof.
rewrite rtE; relsf; unionL; [basic_solver|].
unfold hb.
rewrite path_ut_first at 1.
rewrite (ppo_in_sb WF) at 1 2.
rewrite (fence_in_sb) at 1 2.
generalize (@sb_trans G); ins; relsf.
basic_solver 12.
Qed.

Lemma sync_hb_rbi WF: 
  sync ⨾ hb＊ ⨾ fri ⊆ sync ⨾ hb＊ ⨾ co^?.
Proof.
  rewrite rtEE at 1; relsf; unionL; ins.
  induction x.
  - (* x = 0 *)
simpl; rels.
rewrite (sync_fri_in_sync WF).
basic_solver 42.
  - (* x > 0 *)
    simpl; rewrite seqA; unfold hb at 2; relsf; unionL.
    + (* ppo *)
    rewrite ppo_fri; auto. arewrite (ppo ⊆ hb).
      relsf; unionL; try (by rewrite IHx); rewrite pow_rt.
      all: generalize (ct_end hb); basic_solver 12.
    + (* fence *)
rewrite (fence_fri_in_fence WF).
      arewrite (fence ⊆ hb).
      rewrite pow_seq, pow_rt; basic_solver 12.
    + (* rfe *)
rewrite pow_rt.
      arewrite (rfe ⨾ fri ⊆ co).
generalize (rf_fr WF).
ie_unfolder.
basic_solver 42.
basic_solver 12.
Qed.

Lemma lwsync_hb_rbi WF: 
  lwsync ⨾ hb＊ ⨾ fri ⊆ lwsync ⨾ hb＊ ⨾ co^?.
Proof.
  rewrite rtEE at 1; relsf; unionL; ins.
  induction x.
  - (* x = 0 *)
simpl; rels.
rewrite (lwsync_fri_in_lwsync WF).
basic_solver 42.
  - (* x > 0 *)
    simpl; rewrite seqA; unfold hb at 2; relsf; unionL.
    + (* ppo *)
    rewrite ppo_fri; auto. arewrite (ppo ⊆ hb).
      relsf; unionL; try (by rewrite IHx); rewrite pow_rt. 
      all: generalize (ct_end hb); basic_solver 12.
    + (* fence *)
rewrite (fence_fri_in_fence WF).
      arewrite (fence ⊆ hb).
      rewrite pow_seq, pow_rt; basic_solver 12.
    + (* rfe *)
rewrite pow_rt.
      arewrite (rfe ⨾ fri ⊆ co).
generalize (rf_fr WF).
ie_unfolder.
basic_solver 42.
basic_solver 12.
Qed.

Proposition fence_hb_fri WF: 
  fence ⨾ hb＊ ⨾ fri ⊆ fence ⨾ hb＊ ⨾ co^?.
Proof.
unfold Power_fences.fence.
generalize (sync_hb_rbi WF) (lwsync_hb_rbi WF).
relsf.
basic_solver 12.
Qed.

(* Proposition F.11 *)
Proposition fence_hb WF: 
  fence ⨾ hb＊ ⊆ sb ∪ fence ⨾ ⦗W⦘ ⨾ hb＊.
Proof.
rewrite rtE at 1. relsf.
apply inclusion_union_l.
- rewrite fence_in_sb at 1; basic_solver.
- unfold hb.
  rewrite path_ut_first with (r:=ppo ∪ fence) (r':=rfe).
  rewrite (ppo_in_sb WF) at 1 2.
  relsf; apply inclusion_union_l.
  + rewrite fence_in_sb at 1 2.
    rels.
    generalize (@sb_trans G) (ct_of_trans (@sb_trans G)).
    basic_solver 42.
  + rewrite (dom_l (wf_rfeD WF)) at 1.
    arewrite (rfe ⊆ (ppo ∪ fence ∪ rfe)＊) at 1.
    rewrite rt_rt.
    rewrite fence_in_sb at 2.
    rels.
    rewrite rtE at 1.
    rewrite (ct_of_trans (@sb_trans G)).
    relsf.
    sin_rewrite (fence_sb_w_in_fence WF).
    basic_solver 12.
Qed.

(* Proposition F.12 *)
Proposition RW_sb_fence_hb_sync WF:
  ⦗RW⦘ ⨾ sb ⨾ (fence ⨾ hb＊)^? ⨾ sync ⊆ (fence ⨾ hb＊)^? ⨾ sync.
Proof.
rewrite (fence_hb WF) at 1; auto.
rewrite cr_union_r.
relsf.
sin_rewrite !(rewrite_trans (@sb_trans G)).
generalize (@RW_sb_sync_in_sync G) (RW_sb_fence_in_fence WF).
basic_solver 42.
Qed.

Proposition eco_fench_hb_acyclic CON:
  acyclic (eco^? ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊).
Proof.
  rewrite eco_refl, seq_union_l.
  remember (((co ∪ fre)^? ⨾ rf^? ∪ fri ⨾ (rfi)^?) ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊) as A.
  remember ((fri ⨾ rfe) ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊) as B.
  assert (H: A ⨾ B ⊆ A ⨾ A /\ B ⨾ B ⊆ B ⨾ A).
  { split; subst; rewrite !seqA;
    sin_rewrite (sync_hb_rbi (CON_WF CON)); auto;
    rewrite !seqA;
    (arewrite (co^? ⨾ rfe ⊆ (co ∪ fre)^? ⨾ rf^? ∪ fri ⨾ (rfi)^?) 
      by (unionR left; arewrite (co^? ⊆ (co ∪ fre)^?); 
          arewrite (rfe ⊆ rf^?); done));
    done. }
  destruct H.
  apply acyclic_specific_absorb; try done.
  - (* acyclic A *)
    arewrite (A ⊆ co^? ⨾ prop2).
    { clear H H0; subst. 
      unfold prop2.
      rewrite cr_union_l.
      rewrite (@rfi_union_rfe G) at 1.
      rewrite cr_union_r.
      arewrite (rf ∩ sb ⊆ ⦗RW⦘ ⨾ sb) at 1.
      ie_unfolder; rewrite (wf_rfD (CON_WF CON)); basic_solver.
      arewrite (fri ⨾ rfi^? ⊆ ⦗RW⦘ ⨾ sb).
      ie_unfolder; rewrite (wf_frD (CON_WF CON)).
      generalize (@sb_trans G).
      basic_solver.
      relsf; rewrite !seqA.
      sin_rewrite !(RW_sb_fence_hb_sync (CON_WF CON)).
      basic_solver 42. }
    arewrite (prop2 ⊆ prop).
    arewrite (prop ⊆ (co ∪ prop)⁺).
    arewrite (co ⊆ (co ∪ prop)⁺) at 1.
    relsf; cdes CON; red; relsf.
  - (* irreflexive B *)
    clear H H0; subst.
    rotate 9.
    sin_rewrite (sync_hb_rbi (CON_WF CON)).
    arewrite (rfe ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊ ⊆ prop).
      by unfold prop, prop2; basic_solver 25.
    arewrite (prop ⊆ (co ∪ prop)⁺).
    arewrite (co ⊆ (co ∪ prop)⁺) at 2.
    relsf; cdes CON; red; relsf.
Qed.

Definition S := sb^? ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ rfe ⨾ hb＊ ⨾ (sb ⨾ ⦗F^lwsync⦘ ∪ (eco ∩ sb))^?.

Lemma S_helper_1 WF: rfe ⨾ hb＊ ⊆ rfe ⨾ hb＊ ⨾ ⦗RW⦘.
Proof.
rewrite (dom_r (wf_rfeD WF)) at 1.
rewrite rtE.
rewrite (dom_r (wf_cthbD WF)) at 1.
basic_solver 12.
Qed.

Lemma S_helper_2: 
 ⦗RW⦘ ⨾ (sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^? ⨾ sb^? ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗W⦘  ⊆ fence.
Proof.
unfold Power_fences.fence; rewrite lwsync_alt.
arewrite ((sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^? ⨾ sb^? ⊆ sb^?).
generalize (@sb_trans G); basic_solver.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗F^lwsync⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F^lwsync⦘) by type_solver.
basic_solver 20.
Qed.

Lemma S_trans WF : transitive S.
Proof.
apply transitiveI.
unfold S.
sin_rewrite (S_helper_1 WF).
rewrite (dom_l (wf_rfeD WF)) at 2.
rewrite !seqA.
sin_rewrite S_helper_2.
arewrite (fence ⊆ hb＊).
arewrite (rfe ⊆ hb＊) at 2.
rels.
Qed.

Lemma S_irr CON : irreflexive (S ⨾ sb^?).
Proof.
unfold S.
sin_rewrite (S_helper_1 (CON_WF CON)).
rewrite (dom_l (wf_rfeD (CON_WF CON))) at 1.
rotate 4.
arewrite (sb^? ⨾ sb^? ⊆ sb^?).
by generalize (@sb_trans G); basic_solver.
sin_rewrite S_helper_2.
arewrite (fence ⊆ hb＊).
arewrite (rfe ⊆ hb⁺).
rels.
apply CON.
Qed.



Lemma eco_fence_hb_irr CON: irreflexive (eco ⨾ fence ⨾ hb＊).
Proof.
rewrite (fence_hb (CON_WF CON)).
relsf; unionL.
by rotate 1; apply CON.
rewrite (eco_alt4 (CON_WF CON)).
relsf; unionL.
all: simpl_rels.
+ (* ⟪a,b⟫ ∈ sb *)
  sin_rewrite (RW_sb_fence_in_fence (CON_WF CON)).
  arewrite (fence ⊆ hb).
  rewrite <- ct_begin.
  apply CON.
+ (* ⟪a,b⟫ ∈ rf∘ *)
  arewrite (rfe ⊆ hb); arewrite (fence ⊆ hb); arewrite_id ⦗W⦘; simpl_rels.
  rewrite <- ct_begin, ct_step with (r := hb) at 1; rewrite ct_ct.
  apply CON.
+ (* ⟪a,b⟫ ∈ mo;rf? *)
  sin_rewrite (rf_fence_W_in_fence (CON_WF CON)); simpl_rels.
  rewrite (wf_coD (CON_WF CON)); rewrite !seqA.
  rotate 6.
  arewrite (⦗W⦘ ⨾ rfe^? ⨾ fence ⨾ ⦗W⦘ ⨾ hb＊ ⨾ ⦗W⦘ ⊆ prop1).
  arewrite (co ⊆ (co ∪ prop)⁺).
  arewrite (prop1 ⊆ (co ∪ prop)＊).
  rels; apply CON.
+ (* ⟪a,b⟫ ∈ rb∘;rf? *)
  sin_rewrite (rf_fence_W_in_fence (CON_WF CON)); simpl_rels.
  rewrite (dom_r (wf_freD (CON_WF CON))); rewrite !seqA.
  arewrite (⦗W⦘ ⨾ rfe^? ⨾ fence ⨾ ⦗W⦘  ⊆ prop1).
  by unfold prop1; basic_solver 42.
  arewrite (prop1 ⊆ prop).
  apply CON.
+ (* ⟪a,b⟫ ∈ rb∙;rf∘ *)
  cut(irreflexive (⦗W⦘ ⨾ rfe ⨾ fence ⨾ hb＊ ⨾ fri ⨾ ⦗W⦘)).
  rewrite (dom_r (wf_friD (CON_WF CON))) at 2.
  basic_solver 42.
  sin_rewrite (fence_hb_fri (CON_WF CON)).
  rewrite (dom_l (wf_coD (CON_WF CON))).
  rewrite !seqA.
  arewrite ((⦗W⦘ ⨾ co)^? ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ co^?) by basic_solver 12.
  arewrite (⦗W⦘ ⨾ rfe ⨾ fence ⨾ hb＊ ⨾ ⦗W⦘ ⊆ prop1).
  arewrite (prop1 ⊆ (co ∪ prop)⁺).
  arewrite (co^? ⊆ (co ∪ prop)＊).
  rels; apply CON.
Qed.

Lemma rw_S CON : ⦗RW⦘ ⨾ S ⊆ fence ⨾ rfe ⨾ hb＊ ⨾ (sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^?.
Proof.
unfold S.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗F^lwsync⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F^lwsync⦘) by type_solver.
rewrite (dom_l (wf_rfeD (CON_WF CON))) at 1; rewrite !seqA.
by sin_rewrite (@RW_sb_F_sb_W_in_fence G).
Qed.

Lemma S_rw CON : S ⨾ ⦗RW⦘ ⊆ sb^? ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ rfe ⨾ hb＊ ⨾ (eco ∩ sb)^?.
Proof.
unfold S; rewrite !seqA.
arewrite ((sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^? ⨾ ⦗RW⦘ ⊆ (eco ∩ sb)^?).
type_solver 12.
done.
Qed.

Lemma S_eco_irr CON : irreflexive (S ⨾ eco).
Proof.
rewrite (dom_r (wf_ecoD (CON_WF CON))).
rotate 1.
sin_rewrite (rw_S CON).
rewrite !seqA.
arewrite ((sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^? ⨾ eco ⊆ eco).
by rewrite (dom_l (wf_ecoD (CON_WF CON))); generalize (eco_trans (CON_WF CON)); type_solver.
sin_rewrite rfe_in_hb.
rotate 1.
rewrite <- ct_begin.
rewrite inclusion_t_rt.
by apply eco_fence_hb_irr.
Qed.


Proposition eco_sb_fence_hb_irr CON : 
  irreflexive (eco ⨾ (sb ∪ fence ⨾ hb＊)).
Proof.
relsf.
cdes CON; red in SC_PER_LOC; unfolder in SC_PER_LOC.
generalize (eco_fence_hb_irr CON).
basic_solver 15.
Qed.

Proposition eco_sb_fence_hb_eco_R_irr CON:
  irreflexive (eco ⨾ (sb ∪ (fence ⨾ hb＊ ⨾ (sb ⨾ ⦗F⦘ ∪ eco)^?))).
Proof.
  relsf; unionL.
  by rotate 1; apply CON.
  rewrite crE.
  relsf; unionL.
  apply (eco_fence_hb_irr CON).
  rewrite (dom_l (wf_ecoD (CON_WF CON))); type_solver.
  generalize (eco_fence_hb_irr CON), (eco_trans (CON_WF CON)); basic_solver 12.
Qed.

End Power.
