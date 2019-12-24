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

Set Implicit Arguments.
Remove Hints plus_n_O.

Section immToARM.

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
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'coi'" := G.(coi).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).

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
Notation "'detour'" := G.(detour).
Notation "'bob'" := G.(bob).

(* imm_s *)
Notation "'s_sw'" := G.(imm_s_hb.sw).
Notation "'s_release'" := G.(imm_s_hb.release).
Notation "'s_rs'" := G.(imm_s_hb.rs).
Notation "'s_hb'" := G.(imm_s_hb.hb).
Notation "'s_ppo'" := G.(imm_s_ppo.ppo).
Notation "'s_psc_f'" := G.(imm_s.psc_f).
Notation "'s_psc_base'" := G.(imm_s.psc_base).
Notation "'s_ar_int'" := G.(imm_s_ppo.ar_int).

(* imm *)
Notation "'sw'" := G.(imm_hb.sw).
Notation "'release'" := G.(imm_hb.release).
Notation "'rs'" := G.(imm_hb.rs).
Notation "'hb'" := G.(imm_hb.hb).
Notation "'ppo'" := G.(imm_ppo.ppo).
Notation "'psc'" := G.(imm.psc).
Notation "'psc_f'" := G.(imm.psc_f).
Notation "'psc_base'" := G.(imm.psc_base).
Notation "'ar_int'" := G.(imm_ppo.ar_int).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* arm *)
Notation "'obs'" := G.(obs).
Notation "'obs''" := G.(obs').
Notation "'aob'" := G.(aob).
Notation "'boba'" := G.(Arm.bob).
Notation "'boba''" := G.(bob').
Notation "'dob'" := G.(dob).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

Hypothesis RMW_DEPS : rmw ⊆ ctrl ∪ data.
Hypothesis W_EX_ACQ_SB : ⦗W_ex_acq⦘ ⨾ sb ⊆ sb ⨾ ⦗F^ld⦘ ⨾  sb^?.
Hypothesis DEPS_RMW_SB : rmw_dep ⨾ sb ⊆ ctrl.

Lemma RMW_COI : rmw ⨾ coi ⊆ obs ∪ dob ∪ aob ∪ boba.
Proof.
  rewrite RMW_DEPS, seq_union_l.
Admitted.

Hypothesis CON: ArmConsistent G.

Lemma WF : Wf G.
Proof. apply CON. Qed.
Lemma COMP : complete G.
Proof. apply CON. Qed.
Lemma SC_PER_LOC : sc_per_loc G.
Proof. apply CON. Qed.

Lemma s_ppo_in_ord : s_ppo ⊆ (obs'⁺ ∩ sb ∪ dob ∪ aob ∪ boba' ∪ sb ⨾ ⦗F^ld⦘)⁺.
Proof.
  unfold imm_s_ppo.ppo.
  arewrite (rmw ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⊆ rmw ∪ rmw ;; coi).
  { admit. }
  rewrite path_union, !seq_union_l, !seq_union_r. unionL.
  { admit. }
  (* TODO: continue from here *)
  (* rewrite rtE. *)
  (* rewrite !seq_union_l, !seq_union_r, seq_id_l. unionL. *)
  (* 2: { admit. } *)
Admitted.

Lemma s_ar_int_in_ord : ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
  unfold imm_s_ppo.ar_int.
  transitivity (⦗R⦘ ⨾  ((obs'⁺∩ sb) ∪ dob ∪ aob ∪ boba' ∪ sb ⨾ ⦗F^ld⦘)⁺ ⨾ ⦗W⦘).
  2: { rewrite path_union.
       relsf; unionL.
       { arewrite_id ⦗R⦘; arewrite_id ⦗W⦘.
         rels.
         arewrite (obs'⁺ ∩ sb ⊆ obs'⁺).
         apply inclusion_t_t2.
         apply_unionL_once.
         apply_unionL_once.
         apply_unionL_once.
         { apply inclusion_t_t. basic_solver. }
         all: rewrite <- ct_step; basic_solver. }
       rewrite (dob_in_sb WF) at 1 2.
       rewrite (aob_in_sb WF) at 1 2.
       rewrite (bob'_in_sb WF) at 1 2.
       arewrite (obs'⁺ ∩ sb ⊆ sb).
       rewrite ct_begin.
       arewrite_id ⦗F^ld⦘ at 2.
       generalize (@sb_trans G); ins; relsf.
       arewrite (⦗F^ld⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗F^ld⦘ ⨾ sb) by type_solver.
       unfold Arm.bob', Arm.bob.
       rewrite <- ct_step. basic_solver 21. }
  arewrite (detour ⊆ detour ∩ sb).
  rewrite W_ex_acq_sb_in_boba1, bob_in_boba, detour_in_obs; auto.
  hahn_frame.
  apply inclusion_t_t2.
  apply_unionL_once.
  2: { rewrite <- ct_step. unfold Arm.aob. basic_solver 12. }
  apply_unionL_once.
  2: { apply inclusion_t_t; basic_solver 12. }
  apply_unionL_once.
  2: by unfolder; ins; econs; eauto.
  apply_unionL_once.
  { rewrite <- ct_step; rewrite <- ct_step; unfold Arm.obs'; ie_unfolder; basic_solver 12. }
  apply s_ppo_in_ord.
Qed.

Lemma C_EXT_helper: imm_s.acyc_ext G (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
Proof.
apply (acyc_ext_helper WF).
rewrite s_ar_int_in_ord. psc_in_ord.
arewrite (rfe ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺ ).
unfold Arm.obs'; rewrite <- ct_step; basic_solver 12.
relsf; red; relsf.
apply (external_alt2 WF CON rmw_sb_in_ctrl).
Qed.

Lemma C_SC: acyclic (psc_f ∪ psc_base).
Proof.
  rewrite psc_base_in_ord, psc_f_in_ord.
  rewrite unionK.
  red. rewrite ct_of_ct.
  apply (external_alt2 WF CON rmw_sb_in_ctrl).
Qed.

Lemma IMM_consistent : imm_consistent G.
Proof.
cdes CON.
red; splits; eauto.
apply COH.
apply C_EXT.
apply C_SC.
Qed.

End immToARM.
