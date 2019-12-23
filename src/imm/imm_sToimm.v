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
Remove Hints plus_n_O.

Section S_IMM_TO_IMM.

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

Notation "'rs'" := G.(imm_hb.rs).
Notation "'release'" := G.(imm_hb.release).
Notation "'sw'" := G.(imm_hb.sw).
Notation "'hb'" := G.(imm_hb.hb).
Notation "'psc'" := G.(imm.psc).

Notation "'s_rs'" := G.(imm_s_hb.rs).
Notation "'s_release'" := G.(imm_s_hb.release).
Notation "'s_sw'" := G.(imm_s_hb.sw).
Notation "'s_hb'" := G.(imm_s_hb.hb).

Notation "'ar_int'" := G.(ar_int).
Notation "'s_ar_int'" := G.(imm_s_ppo.ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'s_ppo'" := G.(imm_s_ppo.ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(imm.ar).
Notation "'s_ar'" := G.(imm_s.ar).

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

Lemma s_acyc_ext_helper (WF : Wf G)
      (AC : acyclic (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘)) :
  acyclic (imm_s.ar G psc).
Proof.
  generalize (@sb_trans G); intro SBT.
  red. unfold imm_s.ar.
  apply acyclic_mon with (r:=s_ar_int ∪ (psc ∪ rfe)).
  2: by basic_solver 12.
  apply acyclic_union1.
  { rewrite (imm_s_ppo.ar_int_in_sb WF). apply sb_acyclic. }
  { eapply acyclic_mon; [edone|basic_solver 12]. }
  rewrite (C_EXT_helper2 WF); unionL.
  arewrite (psc ⊆ sb^? ⨾ psc ⨾ sb^?) by basic_solver 12.
  relsf.
  rewrite (imm_s_ppo.ar_int_in_sb WF) at 1; relsf.
  rewrite ct_begin, !seqA; relsf.
  arewrite (sb ⊆ sb^?) at 1.
  rewrite <- !seqA, <- ct_begin, !seqA.
  apply acyclic_union1.
  { red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  { rewrite (dom_l (wf_rfeD WF)), <- seqA, acyclic_rotl.
    rewrite (dom_r (wf_rfeD WF)), !seqA.
    apply acyclic_seq_from_union.
    red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  relsf.
  rewrite (ct_begin (s_ar_int⁺ ⨾ rfe)).
  rewrite (imm_s_ppo.ar_int_in_sb WF) at 1.
  rewrite !seqA; relsf.
  arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⨾ sb ⊆ (sb^? ⨾ psc ⨾ sb^?)⁺).
  { rewrite ct_end at 1; rewrite !seqA.
    arewrite (sb^? ⨾ sb ⊆ sb^?).
      by generalize (@sb_trans G); basic_solver.
        by rewrite <- ct_end. }
  rewrite (dom_l (wf_rfeD WF)) at 2.
  arewrite (rfe ⨾ (s_ar_int⁺ ⨾ ⦗W⦘ ⨾ rfe)＊ ⊆ (rfe ⨾ s_ar_int⁺ ⨾ ⦗W⦘)＊ ⨾ rfe).
  { by rewrite <- seqA; apply rt_seq_swap. }
  rewrite (dom_r (wf_rfeD WF)) at 1.
  rewrite !seqA.
  arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘)⁺).
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  arewrite (⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘)＊) at 3.
  relsf.
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  relsf; red; rels.
Qed.

Lemma s_psc_in_psc : ⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘ ⊆ psc.
Proof. unfold imm.psc. by rewrite s_hb_in_hb. Qed.

Lemma s_ppo_in_ppo (WF: Wf G) : s_ppo ⊆ ppo.
Proof.
  unfold imm_s_ppo.ppo, imm_ppo.ppo.
  assert (rmw ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ∪ rmw_dep ⨾ sb^? ⊆
          (⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺) as AA.
  2: { rewrite !unionA. rewrite AA.
       rewrite <- !unionA. rewrite ct_of_union_ct_r. by rewrite <- !unionA. }
  unionL.
  2: { rewrite crE, seq_union_r, seq_id_r. unionL.
       { rewrite <- ct_step. basic_solver. }
       rewrite <- ct_unit. rewrite <- ct_step.
       rewrite (dom_r WF.(wf_rmw_depD)) at 1. basic_solver 10. }
  rewrite <- ct_step. unionR left.
  rewrite (dom_l WF.(wf_rmwD)). rewrite WF.(rmw_in_sb).
  generalize (@sb_trans G). basic_solver.
Qed.

Lemma s_ar_int_in_ar_int (WF: Wf G) : ⦗R⦘ ⨾ s_ar_int⁺ ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘.
Proof.
  unfold imm_s_ppo.ar_int, imm_ppo.ar_int.
  rewrite WF.(s_ppo_in_ppo).
  rewrite path_union. rewrite seq_union_l, seq_union_r. unionL; [done|].
Admitted.

(* Lemma R_ar_int_alt WF : ⦗R⦘ ⨾ s_ar_int⁺ ⊆ ⦗R⦘ ⨾ (bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺. *)
(* Proof using. *)
(*   unfold ar_int. *)
(*   rewrite path_union2. *)
(*   rewrite !seq_union_r. unionL. *)
(*   { done. } *)
(*   { rewrite ct_begin. rewrite !seqA. *)
(*     arewrite (⦗R⦘ ⨾ ⦗W_ex⦘ ⊆ ∅₂). *)
(*     { rewrite WF.(W_ex_in_W). type_solver. } *)
(*     basic_solver. } *)
(*   arewrite (⦗R⦘ ⨾ (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)＊ ⊆ ⦗R⦘). *)
(*   { admit. } *)
(*   arewrite ((⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⊆ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘). *)
(*   { admit. } *)
(*   rewrite ct_begin. *)
(*   arewrite (((bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)＊ ⊆ sb^?). *)
(*   { admit. } *)
(*   arewrite (rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^? ⊆ sb^?). *)
(*   { admit. } *)
(*   rewrite ct_end at 1. *)
(*   arewrite ((bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) ⊆ sb) at 2. *)
(*   { admit. } *)
(*   arewrite (sb ⨾ ⦗W_ex⦘ ⊆ sb^? ;; rmw). *)
(*   { admit. } *)
(*   rewrite (dom_l WF.(wf_rmwD)). *)
(*   rewrite WF.(rmw_in_sb), !seqA. *)
(*   arewrite (⦗R_ex⦘ ⨾ sb ⨾ sb^? ⨾ (bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⊆ ppo). *)
(*   { admit. } *)

(* (*   rewrite rtE. *) *)
(* (*   rewrite seq_union_l *) *)

(* (* admit. } *) *)

(* (*   rewrite ct_begin. *) *)
(* (*   rewrite seq_union_l. *) *)
(* Admitted. *)


Lemma acyc_ext_implies_s_acyc_ext_helper (WF: Wf G)
      (AC : imm.acyc_ext G) :
  imm_s.acyc_ext G (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘).
Proof.
  unfold imm_s.acyc_ext, imm.acyc_ext in *.
  unfold imm_s.ar.
  rewrite s_psc_in_psc.
  apply s_acyc_ext_helper; auto.
  rewrite WF.(s_ar_int_in_ar_int).
  arewrite (sb^? ⨾ psc ⨾ sb^? ⊆ ar⁺).
  { rewrite wf_pscD. rewrite !seqA.
    arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ bob^?).
    { unfold imm_bob.bob, imm_bob.fwbob. mode_solver 10. }
    arewrite (⦗F ∩₁ Sc⦘ ⨾ sb^?⊆ bob^?).
    { unfold imm_bob.bob, imm_bob.fwbob. mode_solver 10. }
    arewrite (bob ⊆ ar).
    arewrite (psc ⊆ ar).
    rewrite ct_step with (r:=ar) at 2. by rewrite ct_cr, cr_ct. }
  arewrite (rfe ⊆ ar).
  arewrite (ar_int ⊆ ar).
  arewrite (⦗R⦘ ⨾ ar⁺ ⨾ ⦗W⦘ ⊆ ar⁺) by basic_solver.
  rewrite ct_step with (r:=ar) at 2. rewrite !unionK.
  red. by rewrite ct_of_ct.
Qed.

Lemma acyc_ext_implies_s_acyc_ext (WF: Wf G) (AC : imm.acyc_ext G) :
  exists sc, wf_sc G sc /\ imm_s.acyc_ext G sc /\ coh_sc G sc.
Proof.
  set (ar' := s_ar (⦗F∩₁Sc⦘ ⨾ s_hb ⨾ eco ⨾ s_hb ⨾ ⦗F∩₁Sc⦘)).
  assert (acyclic ar') as AC'.
  { by apply acyc_ext_implies_s_acyc_ext_helper. }
  unfold imm_s.acyc_ext, imm.acyc_ext in *.
  exists (⦗ E ∩₁ F ∩₁ Sc ⦘ ⨾ tot_ext G.(acts) ar' ⨾ ⦗ E ∩₁ F ∩₁ Sc ⦘).
  splits.
  { constructor.
    1,2: apply dom_helper_3; basic_solver.
    { rewrite <- restr_relE; apply transitive_restr, tot_ext_trans. }
    { unfolder; ins; desf.
      cut (tot_ext (acts G) ar' a b \/ tot_ext (acts G) ar' b a).
      { basic_solver 12. }
      eapply tot_ext_total; desf; eauto. }
    rewrite <- restr_relE.
    apply irreflexive_restr. by apply tot_ext_irr. }
  { unfold imm_s.ar.
    apply acyclic_mon with (r:= tot_ext (acts G) ar').
    { apply trans_irr_acyclic.
      { apply tot_ext_irr, AC'. }
      apply tot_ext_trans. }
    apply inclusion_union_l; [apply inclusion_union_l|].
    { basic_solver. }
    all: subst ar'; rewrite <- tot_ext_extends; unfold imm_s.ar; basic_solver. }
  unfold coh_sc.
  rotate 4.
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⨾ s_hb ⨾ (eco ⨾ s_hb)^? ⨾ ⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ar'⁺).
  2: { arewrite (ar' ⊆ tot_ext (acts G) ar') at 2.
       { apply tot_ext_extends. }
       rewrite ct_step with (r:= tot_ext (acts G) ar') at 1.
       rewrite ct_ct.
       apply trans_irr_acyclic.
       { apply tot_ext_irr, AC'. }
       apply tot_ext_trans. }
  arewrite (⦗E ∩₁ F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘) by basic_solver.
  case_refl _. 
  { erewrite f_sc_hb_f_sc_in_ar; eauto. by subst ar'. }
  rewrite !seqA. rewrite <- ct_step. subst ar'. 
  unfold imm_s.ar. by unionR left -> left.
Qed.

Lemma imm_consistentimplies_s_imm_consistent (WF: Wf G): imm.imm_consistent G -> 
  exists sc, imm_s.imm_consistent G sc.
Proof.
unfold imm_s.imm_consistent, imm.imm_consistent.
ins; desf.
apply acyc_ext_implies_s_acyc_ext in Cext; eauto; desf.
exists sc; splits; eauto 10 using coherence_implies_s_coherence.
Qed.

Lemma imm_consistentimplies_s_imm_psc_consistent (WF: Wf G)
      (IC : imm.imm_consistent G) :
  exists sc, imm_s.imm_psc_consistent G sc.
Proof.
  edestruct imm_consistentimplies_s_imm_consistent as [sc];
    eauto.
  exists sc. red. splits; auto.
  unfold psc_f, psc_base, scb. rewrite s_hb_in_hb.
  apply IC.
Qed.

End S_IMM_TO_IMM.
