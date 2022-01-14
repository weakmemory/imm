(******************************************************************************)
(** * S_IMM is weaker than IMM   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm_s_hb.
Require Import imm.
Require Import imm_s.
Require Import imm_s_hb_hb.

Set Implicit Arguments.

Section S_IMM_TO_IMM.

Variable G : execution.
Hypothesis WF : Wf G.
Hypothesis FINDOM : set_finite G.(acts_set).

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).

Notation "'detour'" := (detour G).

Notation "'rs'" := (imm_hb.rs G).
Notation "'release'" := (imm_hb.release G).
Notation "'sw'" := (imm_hb.sw G).
Notation "'hb'" := (imm_hb.hb G).
Notation "'psc'" := (imm.psc G).

Notation "'s_rs'" := (imm_s_hb.rs G).
Notation "'s_release'" := (imm_s_hb.release G).
Notation "'s_sw'" := (imm_s_hb.sw G).
Notation "'s_hb'" := (imm_s_hb.hb G).

Notation "'ar_int'" := (ar_int G).
Notation "'s_ar_int'" := (imm_s_ppo.ar_int G).
Notation "'ppo'" := (ppo G).
Notation "'s_ppo'" := (imm_s_ppo.ppo G).
Notation "'bob'" := (bob G).

Notation "'ar'" := (imm.ar G).
Notation "'s_ar'" := (imm_s.ar G).

Notation "'lab'" := (lab G).
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
Notation "'R_ex'" := (R_ex lab).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Lemma s_psc_in_psc : ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘ ⊆ psc.
Proof using. unfold imm.psc. by rewrite s_hb_in_hb. Qed.

Lemma s_ppo_in_ppo : s_ppo ⊆ ppo.
Proof using WF.
  unfold imm_s_ppo.ppo, imm_ppo.ppo.
  assert (rmw ∪ (rmw_dep ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb) ⊆
          (rmw ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺) as AA.
  2: { rewrite !unionA. rewrite AA.
       rewrite <- !unionA. rewrite ct_of_union_ct_r. by rewrite <- !unionA. }
  unionL.
  2: { rewrite crE, seq_union_r, seq_id_r. unionL.
       { rewrite <- ct_step. basic_solver. }
       rewrite <- ct_unit. rewrite <- ct_step.
       rewrite (dom_r (wf_rmw_depD WF)) at 1. basic_solver 10. }
  all: rewrite <- ct_step; unionR left; basic_solver 10.
Qed.

Lemma s_ar_int_in_ar_int : ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘.
Proof using WF. unfold imm_s_ppo.ar_int, imm_ppo.ar_int. by rewrite s_ppo_in_ppo. Qed.

Lemma acyc_ext_implies_s_acyc_ext_helper (AC : imm.acyc_ext G) :
  imm_s.acyc_ext G (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
Proof using WF.
  unfold imm_s.acyc_ext, imm.acyc_ext in *.
  unfold imm_s.ar.
  apply s_acyc_ext_psc_helper; auto.
  unfold imm_s.psc.
  rewrite s_psc_in_psc.
  rewrite s_ar_int_in_ar_int.
  arewrite (sb^? ⨾ psc ⨾ sb^? ⊆ ar⁺).
  { rewrite imm.wf_pscD. rewrite !seqA.
    arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ bob^?).
    { unfold imm_bob.bob, imm_bob.fwbob. mode_solver 10. }
    arewrite (⦗F ∩₁ Sc⦘ ⨾ sb^?⊆ bob^?).
    { unfold imm_bob.bob, imm_bob.fwbob. mode_solver 10. }
    arewrite (bob ⊆ ar).
    { unfold imm.ar, imm_ppo.ar_int. basic_solver 10. }
    arewrite (psc ⊆ ar).
    rewrite ct_step with (r:=ar) at 2. by rewrite ct_cr, cr_ct. }
  arewrite (rfe ⊆ ar).
  arewrite (ar_int ⊆ ar).
  arewrite (⦗R⦘ ⨾ ar⁺ ⨾ ⦗W⦘ ⊆ ar⁺) by basic_solver.
  rewrite ct_step with (r:=ar) at 2. sin_rewrite !unionK.
  red. by rewrite ct_of_ct.
Qed.

Lemma acyc_ext_implies_s_acyc_ext (AC : imm.acyc_ext G) :
  exists sc, wf_sc G sc /\ imm_s.acyc_ext G sc /\ coh_sc G sc.
Proof using WF FINDOM.
  apply imm_s.s_acyc_ext_helper; auto.
    by apply acyc_ext_implies_s_acyc_ext_helper.
Qed.

Lemma imm_consistentimplies_s_imm_consistent (AC : imm.acyc_ext G) :
  imm.imm_consistent G -> exists sc, imm_s.imm_consistent G sc.
Proof using WF FINDOM.
  unfold imm_s.imm_consistent, imm.imm_consistent.
  ins; desf.
  edestruct acyc_ext_implies_s_acyc_ext as [sc]; auto. desf.
  exists sc; splits; eauto 10 using coherence_implies_s_coherence.
Qed.

Lemma imm_consistentimplies_s_imm_psc_consistent
      (IC : imm.imm_consistent G) :
  exists sc, imm_s.imm_psc_consistent G sc.
Proof using WF FINDOM.
  edestruct imm_consistentimplies_s_imm_consistent as [sc]; eauto.
  { apply IC. }
  exists sc. red. splits; auto.
  unfold psc_f, psc_base, scb. rewrite s_hb_in_hb.
  apply IC.
Qed.

Lemma imm_consistentimplies_s_imm_psc_consistent_with_fsupp
      (NOSC : E ∩₁ F ∩₁ Sc ⊆₁ ∅)
      (FSUPPSB : fsupp sb) (* NEXT TODO: remove the restriction *)
      (FSUPPRF : fsupp rf) (* NEXT TODO: remove the restriction *)
      (FSUPP : fsupp ar⁺)
      (IC : imm.imm_consistent G) :
    ⟪ CONS : imm_s.imm_psc_consistent G ∅₂ ⟫ /\
    ⟪ FSUPP : fsupp (s_ar ∅₂)⁺ ⟫.
Proof using WF.
  assert (transitive sb) as TSB by apply sb_trans.
  splits.
  2: { unfold imm_s.ar. rewrite union_false_l.
       rewrite ct_unionE.
       assert (fsupp s_ar_int⁺) as AA.
       { rewrite imm_s_ppo.ar_int_in_sb; auto.
         rewrite ct_of_trans; auto. }
       apply fsupp_union; auto.
       apply fsupp_seq.
       { now apply fsupp_ct_rt. }
       rewrite (wf_rfeD WF), !seqA.
       rewrite ct_rotl, !seqA.
       repeat (apply fsupp_seq); try apply fsupp_eqv.
       3: { rewrite imm_s_ppo.ar_int_in_sb; auto.
            rewrite rt_of_trans; auto.
            now apply fsupp_cr. }
       2: now rewrite rfe_in_rf.
       arewrite (⦗R⦘ ⨾ s_ar_int＊ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘).
       { rewrite rtE. clear. type_solver. }
       rewrite s_ar_int_in_ar_int.
       arewrite (rfe ⊆ ar).
       arewrite (ar_int ⊆ ar).
       arewrite_id ⦗R⦘. arewrite_id ⦗W⦘.
       rewrite seq_id_l, seq_id_r.
       arewrite (ar ⊆ ar⁺) at 1.
       rewrite ct_ct. rewrite rt_of_ct.
       rewrite <- cr_of_ct. now apply fsupp_cr. }
  red. splits.
  2: { unfold psc_f, psc_base, scb. rewrite s_hb_in_hb.
       apply IC. }
  red. splits; try apply IC.
  { constructor; rewrite ?NOSC.
    all: basic_solver. }
  { red. basic_solver. }
  { cdes IC. apply coherence_implies_s_coherence; auto. }
  red. unfold imm_s.ar.
  arewrite (∅₂ ⊆ ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
  apply acyc_ext_implies_s_acyc_ext_helper. apply IC.
Qed.

End S_IMM_TO_IMM.
