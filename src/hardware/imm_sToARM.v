(******************************************************************************)
(** * Compilation correctness from the S_IMM memory model to the ARMv8.3 model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Arm.
Require Import imm_bob.
Require Import imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm.
Require Import immToARMhelper.
Require Import imm_s_hb_hb.

Set Implicit Arguments.

Section immToARM.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'deps'" := (deps G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'coi'" := (coi G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'detour'" := (detour G).
Notation "'bob'" := (bob G).

(* imm_s *)
Notation "'s_sw'" := (imm_s_hb.sw G).
Notation "'s_release'" := (imm_s_hb.release G).
Notation "'s_rs'" := (imm_s_hb.rs G).
Notation "'s_hb'" := (imm_s_hb.hb G).
Notation "'s_ppo'" := (imm_s_ppo.ppo G).
Notation "'s_psc_f'" := (imm_s.psc_f G).
Notation "'s_psc_base'" := (imm_s.psc_base G).
Notation "'s_ar_int'" := (imm_s_ppo.ar_int G).

(* imm *)
Notation "'sw'" := (imm_hb.sw G).
Notation "'release'" := (imm_hb.release G).
Notation "'rs'" := (imm_hb.rs G).
Notation "'hb'" := (imm_hb.hb G).
Notation "'ppo'" := (imm_ppo.ppo G).
Notation "'psc'" := (imm.psc G).
Notation "'psc_f'" := (imm.psc_f G).
Notation "'psc_base'" := (imm.psc_base G).
Notation "'ar_int'" := (imm_ppo.ar_int G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* arm *)
Notation "'obs'" := (obs G).
Notation "'obs''" := (obs' G).
Notation "'aob'" := (aob G).
Notation "'boba'" := (Arm.bob G).
Notation "'boba''" := (bob' G).
Notation "'dob'" := (dob G).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

Hypothesis RMW_DEPS : rmw ⊆ ctrl ∪ data.
Hypothesis W_EX_ACQ_SB : ⦗W_ex_acq⦘ ⨾ sb ⊆ sb ⨾ ⦗F^ld⦘ ⨾  sb^?.
Hypothesis DEPS_RMW_SB : rmw_dep ⨾ sb ⊆ ctrl.
Hypothesis REX_IN_RMW_CTRL : ⦗R_ex⦘ ⨾ sb ⊆ ctrl.

Hypothesis CON: ArmConsistent G.

Lemma WF : Wf G.
Proof using CON. apply CON. Qed.
Lemma COMP : complete G.
Proof using CON. apply CON. Qed.
Lemma SC_PER_LOC : sc_per_loc G.
Proof using CON. apply CON. Qed.

Lemma RMW_COI : rmw ⨾ coi ⊆ obs' ∪ dob ∪ aob ∪ boba.
Proof using CON.
  cdes CON. rewrite rmw_in_fri; auto.
  rewrite fri_coi; auto. rewrite fri_in_fr. 
  unfold Arm.obs'. eauto with hahn.
Qed.

Lemma R_ex_fail_sb_in_ctrl : ⦗R_ex \₁ dom_rel rmw⦘ ⨾ sb ⊆ ctrl.
Proof using REX_IN_RMW_CTRL.
  rewrite <- REX_IN_RMW_CTRL.
  basic_solver.
Qed.

Lemma s_ppo_in_dob : s_ppo ⊆ dob⁺.
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  unfold imm_s_ppo.ppo.
  rewrite REX_IN_RMW_CTRL.
  arewrite (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ∪ rmw_dep ⨾ sb^? ∪ ctrl ⊆
            data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw_dep ⨾ sb^?).
  { rewrite RMW_DEPS. unionL; eauto with hahn. }
  rewrite path_union, !seq_union_l, !seq_union_r. unionL.
  { apply ppo_in_dob_helper; auto. }
  assert ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)＊ ⊆ sb^?) as AA.
  { rewrite (data_in_sb WF), (ctrl_in_sb WF), (addr_in_sb WF).
    arewrite (rfi ⊆ sb).
    generalize (@sb_trans G). ins. relsf. }
  rewrite AA at 2.
  rewrite ct_begin, !seqA.
  rewrite AA at 2.
  arewrite (sb^? ⨾ (sb^? ⨾ rmw_dep ⨾ sb^?)＊ ⨾ sb^? ⊆ sb^?).
  { rewrite (rmw_dep_in_sb WF). generalize (@sb_trans G). ins. relsf. }
  arewrite (rmw_dep ⨾ sb^? ⨾ ⦗W⦘ ⊆ rmw_dep ⨾ sb ⨾ ⦗W⦘).
  { rewrite (dom_r (wf_rmw_depD WF)) at 1. rewrite R_ex_in_R. type_solver. }
  sin_rewrite DEPS_RMW_SB.
  arewrite (ctrl ⊆ data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi) at 2.
  seq_rewrite <- ct_end.
  apply ppo_in_dob_helper; auto.
Qed.

Lemma s_ppo_in_ord : s_ppo ⊆ (obs⁺ ∩ sb ∪ dob ∪ aob ∪ boba' ∪ sb ⨾ ⦗F^ld⦘)⁺.
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  rewrite s_ppo_in_dob. apply clos_trans_mori. eauto with hahn. 
Qed.

Lemma s_ar_int_in_ord : ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  unfold imm_s_ppo.ar_int.
  transitivity (⦗R⦘ ⨾  ((obs⁺∩ sb) ∪ dob ∪ aob ∪ boba' ∪ sb ⨾ ⦗F^ld⦘)⁺ ⨾ ⦗W⦘).
  2: { rewrite path_union.
       relsf; unionL.
       { arewrite_id ⦗R⦘; arewrite_id ⦗W⦘.
         rels.
         arewrite (obs⁺ ∩ sb ⊆ obs⁺).
         apply inclusion_t_t2.
         apply_unionL_once.
         apply_unionL_once.
         apply_unionL_once.
         { apply inclusion_t_t. basic_solver. }
         all: rewrite <- ct_step; basic_solver. }
       rewrite (dob_in_sb WF) at 1 2.
       rewrite (aob_in_sb WF) at 1 2.
       rewrite (bob'_in_sb WF) at 1 2.
       arewrite (obs⁺ ∩ sb ⊆ sb).
       rewrite ct_begin.
       arewrite_id ⦗F^ld⦘ at 2.
       generalize (@sb_trans G); ins; relsf.
       arewrite (⦗F^ld⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗F^ld⦘ ⨾ sb) by type_solver.
       unfold Arm.bob', Arm.bob.
       rewrite <- ct_step. basic_solver 21. }
  arewrite (detour ⊆ detour ∩ sb).
  rewrite W_ex_acq_sb_in_boba1; auto.
  rewrite bob_in_boba; auto.
  rewrite detour_in_obs; auto.
  hahn_frame.
  apply inclusion_t_t2.
  apply_unionL_once.
  2: { rewrite <- ct_step. unfold Arm.aob. basic_solver 12. }
  apply_unionL_once.
  2: { apply inclusion_t_t; basic_solver 12. }
  apply_unionL_once.
  2: by unfolder; ins; econs; eauto.
  apply_unionL_once.
  { rewrite <- ct_step; rewrite <- ct_step; unfold Arm.obs; ie_unfolder; basic_solver 12. }
  apply s_ppo_in_ord.
Qed.

Lemma C_EXT_helper: imm_s.acyc_ext G (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  apply (s_acyc_ext_psc_helper WF).
  rewrite s_ar_int_in_ord.
  arewrite (rfe ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺ ).
  { unfold Arm.obs; rewrite <- ct_step; basic_solver 12. }
  arewrite (imm_s.psc G ⊆ imm.psc G).
  { unfold imm_s.psc, imm.psc. by rewrite s_hb_in_hb. }
  rewrite psc_in_ord; auto.
  relsf; red; relsf.
  apply (external_alt_bob' WF CON).
Qed.

Lemma C_SC : acyclic (imm_s.psc_f G ∪ imm_s.psc_base G).
Proof using CON RMW_DEPS W_EX_ACQ_SB.
  unfold imm_s.psc_f, imm_s.psc_base, imm_s.scb.
  rewrite s_hb_in_hb. 
  apply immToARMhelper.C_SC; auto.
Qed.

Lemma IMM_s_coherence :
  imm_s_hb.coherence G.
Proof using CON.
  red.
  rewrite crE, seq_union_r, seq_id_r.
  rewrite s_hb_in_hb. 
  apply irreflexive_union. split.
  2: { apply COH; auto. } 
  rewrite hb_in_ord; auto. 
  apply irreflexive_union. split.
  { by apply (@sb_irr G). }
  apply (external_alt_bob' WF CON).
Qed.

Lemma IMM_s_psc_consistent (FINDOM : set_finite E) :
  exists sc, imm_psc_consistent G sc.
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  edestruct (imm_s.s_acyc_ext_helper WF FINDOM C_EXT_helper) as [sc HH]. desc.
  exists sc. red. splits; eauto.
  2: by apply C_SC.
  red. splits; eauto; try apply CON.
  now apply IMM_s_coherence.
Qed.

Lemma IMM_s_fsupp_consistent
      (FSUPPSB : fsupp sb) (* NEXT TODO: remove the restriction *)
      (FSUPPRF : fsupp rf) (* NEXT TODO: remove the restriction *)
      (* NEXT TODO: note that here we use boba' instead of original Arm.bob *)
      (FSUPP : fsupp (obs ∪ dob ∪ aob ∪ boba')⁺) 
      (NOSC : E ∩₁ F ∩₁ Sc ⊆₁ ∅) :
  ⟪ CONS  : imm_psc_consistent G ∅₂ ⟫ /\
  ⟪ FSUPP : fsupp (imm_s.ar G ∅₂)⁺ ⟫.
Proof using CON DEPS_RMW_SB REX_IN_RMW_CTRL RMW_DEPS W_EX_ACQ_SB.
  assert (WF' : Wf G) by apply WF.
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
       rewrite s_ar_int_in_ord.
       arewrite (rfe ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺).
       { rewrite <- ct_step. unfold Arm.obs. eauto with hahn. }
       rewrite ct_ct, rt_of_ct.
       rewrite <- cr_of_ct. now apply fsupp_cr. }
  red; splits.
  2: now apply C_SC.
  red. splits; try apply CON.
  { constructor; rewrite ?NOSC.
    all: basic_solver. }
  { red. basic_solver. }
  { now apply IMM_s_coherence. }
  red. unfold imm_s.ar.
  arewrite (∅₂ ⊆ ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
  apply C_EXT_helper.
Qed.

End immToARM.
