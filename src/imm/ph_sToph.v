(******************************************************************************)
(** * S_PH is weaker than PH   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events Execution Execution_eco.
Require Import ph_common ph_hb ph_s_hb ph ph_s.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section S_PH_TO_PH.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).

Notation "'detour'" := G.(detour).

Notation "'rs'" := G.(ph_hb.rs).
Notation "'release'" := G.(ph_hb.release).
Notation "'sw'" := G.(ph_hb.sw).
Notation "'hb'" := G.(ph_hb.hb).
Notation "'psc'" := G.(ph.psc).

Notation "'s_rs'" := G.(ph_s_hb.rs).
Notation "'s_release'" := G.(ph_s_hb.release).
Notation "'s_sw'" := G.(ph_s_hb.sw).
Notation "'s_hb'" := G.(ph_s_hb.hb).

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ph.ar).
Notation "'s_ar'" := G.(ph_s.ar).

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
Notation "'R_ex'" := (R_ex G).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)
Lemma s_rs_in_rs : s_rs ⊆ rs.
Proof.
unfold ph_s_hb.rs, ph_hb.rs.
hahn_frame.
rewrite rtE at 1; relsf.
apply inclusion_union_l.
rewrite rtE at 1; relsf.
basic_solver.
unionR right.
arewrite_id ⦗W⦘; rels.
arewrite (rf ⨾ rmw ⊆ (sb ∩ same_loc)^? ⨾ rf ⨾ rmw) at 1 by basic_solver 12.
rewrite ct_begin.
generalize (@sb_same_loc_trans G); ins; rewrite !seqA; relsf.
generalize (ct_begin ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)).
basic_solver 40.
Qed.

Lemma s_release_in_release : s_release ⊆ release.
Proof.
unfold ph_s_hb.release, ph_hb.release.
by rewrite s_rs_in_rs.
Qed.

Lemma s_sw_in_sw : s_sw ⊆ sw.
Proof.
unfold ph_s_hb.sw, ph_hb.sw.
rewrite s_release_in_release.
rewrite (rfi_union_rfe).
basic_solver 21.
Qed.

Lemma s_hb_in_hb : s_hb ⊆ hb.
Proof.
unfold ph_s_hb.hb, ph_hb.hb.
by rewrite s_sw_in_sw.
Qed.

(*Lemma s_ar_in_ar sc (WF_SC: wf_sc G sc) : s_ar sc ⊆ ar.
Proof.
unfold ph_s.ar, ph.ar.
destr
by rewrite s_psc_in_psc.
Qed.
*)

(******************************************************************************)
(** Properties **  *)
(******************************************************************************)

Lemma coherence_implies_s_coherence (WF: Wf G) (COMP: complete G) :
ph_hb.coherence G -> ph_s_hb.coherence G.
Proof.
unfold ph_s_hb.coherence.
unfolder; ins; desf.
eapply ph_hb.hb_irr; eauto.
eapply s_hb_in_hb; edone.
unfold ph_hb.coherence in *; unfolder in *.
eapply H; eexists; split; eauto.
eapply s_hb_in_hb; edone.
Qed.

Lemma acyc_ext_implies_s_acyc_ext (WF: Wf G): ph.acyc_ext G -> 
  exists sc, wf_sc G sc /\ ph_s.acyc_ext G sc /\ coh_sc G sc.
Proof.
unfold ph_s.acyc_ext, ph.acyc_ext.
intro.
exists (⦗ E ∩₁ F ∩₁ Sc ⦘ ⨾ tot_ext G.(acts) ar ⨾ ⦗ E ∩₁ F ∩₁ Sc ⦘).
splits.
- constructor.
   * apply dom_helper_3; basic_solver.
   * apply dom_helper_3; basic_solver.
   * rewrite <- restr_relE; apply transitive_restr, tot_ext_trans.
   * unfolder; ins; desf.
     cut (tot_ext (acts G) ar a b \/ tot_ext (acts G) ar b a).
     { basic_solver 12. }
     eapply tot_ext_total; desf; eauto.
   * rewrite <- restr_relE.
     apply irreflexive_restr.
       by apply tot_ext_irr.
- unfold ph_s.ar, ph.ar.
  apply acyclic_mon with (r:= tot_ext (acts G) (psc ∪ rfe ∪ ar_int)).
  apply trans_irr_acyclic.
  apply tot_ext_irr, H.
  apply tot_ext_trans.
  apply inclusion_union_l.
  apply inclusion_union_l.
  basic_solver.
  rewrite <- tot_ext_extends; basic_solver.
  rewrite <- tot_ext_extends; basic_solver.
- unfold coh_sc.
  rotate 4.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⨾ s_hb ⨾ (eco ⨾ s_hb)^? ⨾ ⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ar^+).
  case_refl _.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘) by basic_solver.
  by rewrite f_sc_hb_f_sc_in_ar; basic_solver 12.
  rewrite s_hb_in_hb, !seqA.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗E ∩₁ F ∩₁ Sc⦘ ⊆ psc).
  unfold ph.psc; basic_solver 12.
  arewrite (psc ⊆ ar); vauto.
  rewrite (tot_ext_extends (acts G) ar) at 2.
  generalize (tot_ext_trans (acts G) ar); ins; relsf.
  by eapply tot_ext_irr.
Qed.

Lemma ph_consistentimplies_s_ph_consistent (WF: Wf G): ph.ph_consistent G -> 
  exists sc, ph_s.ph_consistent G sc.
Proof.
unfold ph_s.ph_consistent, ph.ph_consistent.
ins; desf.
apply acyc_ext_implies_s_acyc_ext in Cext; eauto; desf.
exists sc; splits; eauto 10 using coherence_implies_s_coherence.
Qed.

End S_PH_TO_PH.
