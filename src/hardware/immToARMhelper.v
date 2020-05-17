(******************************************************************************)
(** * Helper lemmas relating IMM and ARM *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Arm.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm.

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


(* imm *)
Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).
Notation "'rs'" := G.(rs).
Notation "'hb'" := G.(hb).
Notation "'ppo'" := G.(ppo).
Notation "'psc'" := G.(psc).
Notation "'psc_f'" := G.(psc_f).
Notation "'psc_base'" := G.(psc_base).
Notation "'bob'" := G.(bob).
Notation "'detour'" := G.(detour).

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

Hypothesis W_EX_ACQ_SB : ⦗W_ex_acq⦘ ⨾ sb ⊆ sb ⨾ ⦗F^ld⦘ ⨾  sb^?.

Hypothesis CON: ArmConsistent G.

Lemma WF : Wf G.
Proof using CON. apply CON. Qed.
Lemma COMP : complete G.
Proof using CON. apply CON. Qed.
Lemma SC_PER_LOC : sc_per_loc G.
Proof using CON. apply CON. Qed.

(******************************************************************************)
(** * imm.hb in terms of Arm relations *)
(******************************************************************************)

(* Lemma rs_sb_loc_W_in_coe_sb : *)
(*   rs ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ (coe ∪ ⦗W⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^?. *)
(* Proof using CON. *)
(*   transitivity ((rs ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘) ∩ co^?). *)
(*   { apply inclusion_inter_r; [done|]. apply (rs_sb_loc WF SC_PER_LOC). } *)
(*   rewrite crE with (r:=co). rewrite inter_union_r. *)
(*   rewrite crE with (r:=coe ∪ ⦗W⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘). apply union_mori. *)
(*   { clear. basic_solver. } *)
(*   rewrite coi_union_coe. rewrite inter_union_r. *)
(*   unionL.  *)
(*   2: { clear. basic_solver. } *)
(*   unionR right. rewrite (coi_in_sbloc' WF), (wf_rsD WF). *)
(*   clear. basic_solver. *)
(* Qed. *)

Lemma rs_rfi_Q: rs ⨾ rfi ⨾ ⦗Q⦘ ⊆ sb ∩ same_loc ⨾ ⦗Q⦘ ∪ (obs ∪ dob ∪ aob ∪ boba')⁺  ⨾ ⦗Q⦘.
Proof using CON.
  generalize (rs_in_co  WF SC_PER_LOC).
  unfold imm_hb.rs.
  intro X.
  rewrite rtE; relsf; unionL.
  { rewrite (rfi_in_sbloc' WF); generalize (@sb_same_loc_trans G).
    basic_solver 12. }
  { ie_unfolder. rewrite (rfi_in_sbloc WF).
    unionR left. basic_solver 12. }
  rewrite !seqA, ct_end, !seqA.
  arewrite (⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊ ⊆ ⦗W⦘ ⨾ co^?).
  revert X.
  relsf.
  { unfolder; ins; desf; splits; eauto; eapply H; eauto. }
  rewrite (dom_l (wf_rfD WF)) at 1; rewrite !seqA.
  sin_rewrite (co_sb_loc WF SC_PER_LOC).
  rewrite rmw_W_ex, !seqA, (rmw_in_fr  WF SC_PER_LOC COMP).
  sin_rewrite (rf_fr WF).
  generalize (co_trans WF); ins; relsf.
  rewrite coi_union_coe.
  rewrite !seq_union_l.
  apply union_mori.
  { arewrite_id ⦗W_ex⦘. rewrite seq_id_l. hahn_frame_r.
    rewrite (coi_in_sbloc' WF). rewrite (rfi_in_sbloc' WF).
    apply transitiveI. apply sb_same_loc_trans. }
  rewrite ct_begin, rtE, <- ct_step.
  unfold Arm.aob at 2.
  unfold Arm.obs at 1.
  basic_solver 42.
Qed.

Lemma rs_prefix_co_in_ord :
  ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ co^? ⊆ ⦗L ∪₁ F^sy⦘ ⨾ (obs ∪ dob ∪ aob ∪ boba')＊.
Proof using.
  arewrite (co^? ⊆ coi^? ;; obs^?).
  { rewrite coi_union_coe.
    rewrite cr_union_l.
    arewrite (coe ⊆ obs).
    basic_solver 10. }
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ coi^?  ⊆ ⦗L ∪₁ F^sy⦘ ⨾ boba'^?).
  { case_refl _.
    2: rewrite coi_in_sb; generalize (@sb_trans G).
    all: unfold Arm.bob', Arm.bob; basic_solver 21. }
  hahn_frame.
  arewrite (boba' ⊆ obs ∪ dob ∪ aob ∪ boba') at 1.
  arewrite (obs   ⊆ obs ∪ dob ∪ aob ∪ boba') at 2.
  rewrite <- rt_cr.
  hahn_frame. by apply inclusion_r_rt.
Qed.

Lemma rfe_sb_Acq_in_ord :
  rfe ⨾ ⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof using.
  arewrite (⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ boba'^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
  { unfold Arm.bob'. basic_solver 21. }
  hahn_frame_r.
  arewrite (boba' ⊆ obs ∪ dob ∪ aob ∪ boba') at 1.
  arewrite (rfe ⊆ obs).
  arewrite (obs ⊆ obs ∪ dob ∪ aob ∪ boba') at 1.
  rewrite <- ct_cr. hahn_frame_r. apply ct_step.
Qed.

Lemma sw_in_ord :
  sw ⊆ ⦗L⦘ ⨾ sb ∩ same_loc ⨾ ⦗Q⦘ ∪
       ⦗L⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ 
       ⦗L∪₁F^sy⦘ ⨾ (obs ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof using CON.
  unfold imm_hb.sw, imm_hb.release.
  rewrite (dom_l (wf_rsD WF)), (dom_r (wf_rfeD WF)), !seqA; relsf.
  rewrite !seqA.
  unionL.
  2: { unionR right.
       rewrite (dom_l (wf_rfeD WF)), !seqA.
       sin_rewrite (rs_sb_loc WF SC_PER_LOC).
       sin_rewrite rs_prefix_co_in_ord. rewrite <- rt_ct. rewrite !seqA.
       do 2 hahn_frame_l.
       apply rfe_sb_Acq_in_ord. }
  case_refl (sb ⨾ ⦗F⦘).
  { rewrite (dom_r (wf_rfiD WF)) at 1; rewrite !seqA.
    arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⊆ ⦗Q⦘) by basic_solver.
    rewrite rs_rfi_Q; relsf; unionL.
    { case_refl _. 
      { basic_solver 12. }
      unionR right.
      arewrite (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗Q⦘ ⊆ sb^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
      { basic_solver 12. }
      generalize (@sb_trans G); ins; relsf.
      rewrite <- ct_step; unfold Arm.bob'; basic_solver 12. }
    case_refl _. 
    { basic_solver 12. }
    unionR right.
    arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb) ⨾ ⦗W⦘ ⊆ ⦗L ∪₁ F^sy⦘ ⨾ boba'^?).
    { unfold Arm.bob'. basic_solver 21. }
    arewrite (boba' ⊆ obs ∪ dob ∪ aob ∪ boba') at 1.
    arewrite (Q ⊆₁ Q ∪₁ F^ld ∪₁ F^sy) at 1 by basic_solver.
    hahn_frame. apply cr_ct. }
  sin_rewrite (rs_rfi WF SC_PER_LOC). relsf. rewrite !seqA.
  generalize (@sb_trans G); ins; relsf; unionL.
  { case_refl _.
    arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
    basic_solver 12.
    unionR right.
    arewrite (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⊆ sb^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
    arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
    { generalize (@sb_trans G). basic_solver 12. }
    rewrite <- ct_step; unfold Arm.bob'; basic_solver 12. }
  unionR right.
  sin_rewrite rs_prefix_co_in_ord. rewrite <- rt_ct. rewrite !seqA.
  do 2 hahn_frame_l.
  arewrite (sb ⨾ ⦗F⦘ ⊆ (sb ⨾ ⦗F⦘)^?).
  apply rfe_sb_Acq_in_ord.
Qed.

Lemma swe_in_ord :
  sw \ sb ⊆ ⦗L∪₁F^sy⦘ ⨾ (obs ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof using CON.
  rewrite sw_in_ord.
  arewrite (sb ∩ same_loc ⨾ ⦗R⦘ ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). basic_solver. }
  rewrite !minus_union_l. unionL.
  3: by eauto with hahn.
  transitivity (fun x y : actid => False).
  all: basic_solver.
Qed.

Lemma ct_sb_swe_in_ord :
  (sb^? ⨾ (sw \ sb))⁺ ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof using CON.
  clear W_EX_ACQ_SB.
  sin_rewrite swe_in_ord.
  rewrite <- !seqA. rewrite inclusion_ct_seq_eqv_r.
  hahn_frame_r.
  arewrite (sb^? ⨾ ⦗L ∪₁ F^sy⦘ ⊆ boba'^?).
  { rewrite !crE. rewrite seq_union_l, seq_id_l.
    unfold Arm.bob', Arm.bob. basic_solver 20. }
  arewrite (boba'^? ⨾ (obs ∪ dob ∪ aob ∪ boba')⁺ ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺).
  { arewrite (boba'^? ⊆ (obs ∪ dob ∪ aob ∪ boba')＊) at 1. apply rt_ct. }
  apply ct_of_ct.
Qed.

Lemma hb_in_ord : hb ⊆ sb ∪ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON.
  rewrite hb_in_sb_swe.
  rewrite path_union.
   generalize (@sb_trans G); ins; relsf.
  apply union_mori; [done|].
  rewrite ct_sb_swe_in_ord, !seqA.
  arewrite (⦗Q ∪₁ F^ld ∪₁ F^sy⦘ ⨾ sb^? ⊆ boba'^?).
  { unfold Arm.bob', Arm.bob; basic_solver 14. }
  arewrite (boba' ⊆ (obs ∪ dob ∪ aob ∪ boba')＊) at 2.
  relsf.
Qed.

Lemma sbrel_in_ord : sb ⨾ ⦗L ∪₁ F^sy⦘ ⊆ boba'.
Proof using CON.
  unfold Arm.bob', Arm.bob; basic_solver 14.
Qed.

(******************************************************************************)
(** * Coherence *)
(******************************************************************************)

Lemma COH: coherence G.
Proof using CON.
  red. rewrite (eco_in_sb_obs_sb WF).
  rewrite <- !seqA, irreflexive_seqC, !seqA.
  arewrite (sb^? ⨾ hb ⨾ sb^? ⊆ hb).
  { rewrite sb_in_hb.
    rewrite rewrite_trans_seq_cr_r; [|by apply hb_trans].
    rewrite rewrite_trans_seq_cr_l; [|by apply hb_trans].
    done. }
  arewrite (obs^? ⨾ obs^? ⊆ obs^*).
  { rewrite <- rt_cr. hahn_frame. by apply inclusion_r_rt. }
  rewrite hb_in_ord.
  rewrite seq_union_l.
  apply irreflexive_union. split.
  2: { arewrite (obs ⊆ obs ∪ dob ∪ aob ∪ boba') at 2.
       rewrite ct_rt. apply (external_alt_bob' WF); auto. }
  rewrite obs_in_eco. rewrite rt_of_trans; [|by apply (eco_trans WF)].
  rewrite crE, seq_union_r, seq_id_r.
  apply irreflexive_union. split.
  { apply sb_irr. }
  apply CON.
Qed.

(******************************************************************************)
(** * C_ext *)
(******************************************************************************)

Lemma psc_in_ord : sb^? ⨾ psc ⨾ sb^? ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺ .
Proof using CON W_EX_ACQ_SB.
  unfold imm.psc.
  rewrite (eco_in_sb_obs_sb WF). rewrite !seqA.
  arewrite (hb ⨾ sb^? ⊆ hb).
  { rewrite sb_in_hb. apply rewrite_trans_seq_cr_r. by apply hb_trans. }
  arewrite (sb^? ⨾ hb ⊆ hb).
  { rewrite sb_in_hb. apply rewrite_trans_seq_cr_l. by apply hb_trans. }
  arewrite (F ∩₁ Sc ⊆₁ F^sy) by mode_solver.
  arewrite (sb^? ⨾ ⦗F^sy⦘ ⨾ hb ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺).
  { rewrite hb_in_ord. rewrite !seq_union_r.
    unionL.
    { rewrite <- ct_step. unionR right.
      unfold Arm.bob', Arm.bob.
      rewrite crE. rewrite !seq_union_l, seq_id_l.
      unionL.
      2: by eauto 10 with hahn.
      unionR left -> right.
      basic_solver. }
    rewrite <- cr_ct at 2.
    hahn_frame_r.
    transitivity boba'^?.
    2: basic_solver.
    unfold Arm.bob'. basic_solver 10. }
  arewrite (hb ⨾ ⦗F^sy⦘ ⨾ sb^? ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺).
  { rewrite hb_in_ord. rewrite !seq_union_l.
    unionL.
    { rewrite <- ct_step. unionR right.
      unfold Arm.bob', Arm.bob.
      rewrite crE. rewrite !seq_union_r, seq_id_r.
      unionL.
      2: by eauto 10 with hahn.
      unionR left -> left -> right.
      basic_solver. }
    rewrite <- ct_cr at 2.
    hahn_frame_l.
    transitivity boba'^?.
    2: basic_solver.
    unfold Arm.bob'. basic_solver 10. }
  arewrite (obs ⊆ obs ∪ dob ∪ aob ∪ boba') at 2.
  arewrite (obs ⊆ obs ∪ dob ∪ aob ∪ boba') at 3.
  rewrite !cr_ct. apply transitiveI. apply transitive_ct.
Qed.

Lemma hb_f_sy_in_ord : hb ⨾ ⦗F^sy⦘ ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON.
  rewrite hb_in_ord.
  rewrite !seq_union_l.
  unionL.
  2: { basic_solver. }
  arewrite !(sb ⨾ ⦗F^sy⦘⊆ boba').
  rewrite <- ct_step.
  basic_solver 10.
Qed.

Lemma f_sy_hb_in_ord : ⦗F^sy⦘ ⨾ hb ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON.
  rewrite hb_in_ord.
  rewrite !seq_union_r.
  unionL.
  2: { basic_solver. }
  arewrite !(⦗F^sy⦘ ⨾ sb ⊆ boba').
  2: { rewrite <- ct_step. basic_solver 10. }
  unfold Arm.bob'. basic_solver 10.
Qed.

Lemma sb_psc_f_sb_in_ord : sb^? ⨾ psc_f ⨾ sb^? ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON W_EX_ACQ_SB.
  unfold imm.psc_f.
  rewrite crE with (r := eco ⨾ hb).
  repeat (rewrite !seq_union_l, !seq_union_r).
  rewrite !seq_id_l, !seqA.
  unionL.
  2: { generalize psc_in_ord. unfold imm.psc. by rewrite !seqA. }
  arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) by mode_solver.
  arewrite !(sb^? ⨾ ⦗F^sy⦘⊆ boba'^? ⨾ ⦗F^sy⦘).
  { unfold Arm.bob'. basic_solver 21. }
  arewrite !(⦗F^sy⦘ ⨾ sb^? ⊆ ⦗F^sy⦘ ⨾ boba'^? ).
  { unfold Arm.bob'. basic_solver 21. }
  sin_rewrite hb_f_sy_in_ord.
  arewrite_id ⦗F^sy⦘. rewrite seq_id_l.
  set (X:= (obs ∪ dob ∪ aob ∪ boba')).
  assert (boba' ⊆ X⁺) as BB.
  { rewrite <- ct_step. unfold X. basic_solver. }
  sin_rewrite !BB.
  relsf.
Qed.

Lemma psc_f_in_ord : psc_f ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON W_EX_ACQ_SB.
  arewrite (psc_f ⊆ sb^? ⨾ psc_f ⨾ sb^?) by basic_solver 10.
  apply sb_psc_f_sb_in_ord.
Qed.

Lemma sc_sb_sc_in_boba' : ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘ ⊆ boba'.
Proof using CON W_EX_ACQ_SB.
  arewrite (Sc ⊆₁ ((R ∪₁ F) ∪₁ W) ∩₁ Sc) at 1 by type_solver.
  rewrite set_inter_union_l, id_union, !seq_union_l.
  unionL.
  { arewrite_id ⦗Sc⦘. rewrite seq_id_r.
    rewrite set_inter_union_l, id_union, !seq_union_l.
    arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) by mode_solver.
    arewrite (⦗R ∩₁ Sc⦘ ⊆ ⦗Q⦘) by mode_solver.
    unfold Arm.bob', Arm.bob.
    basic_solver 10. }
  arewrite (Sc ⊆₁ ((W ∪₁ F) ∪₁ R) ∩₁ Sc) at 2 by type_solver.
  rewrite set_inter_union_l, id_union, !seq_union_r.
  unionL.
  { arewrite_id ⦗W ∩₁ Sc⦘. rewrite seq_id_l.
    rewrite set_inter_union_l, id_union, !seq_union_r.
    arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) by mode_solver.
    arewrite (⦗W ∩₁ Sc⦘ ⊆ ⦗L⦘) by mode_solver.
    unfold Arm.bob', Arm.bob.
    basic_solver 20. }
  arewrite (⦗W ∩₁ Sc⦘ ⊆ ⦗L⦘) by mode_solver.
  unfold Arm.bob', Arm.bob.
  basic_solver 10.
Qed.

Lemma psc_base_in_ord : psc_base ⊆ (obs ∪ dob ∪ aob ∪ boba')⁺.
Proof using CON W_EX_ACQ_SB.
  unfold imm.psc_base, imm.scb.
  rewrite coi_union_coe, fri_union_fre.
  rewrite coi_in_sb, fri_in_sb. 
  rewrite sb_in_hb.
  arewrite (hb \ same_loc ⊆ hb).
  repeat arewrite (hb ⨾ hb ⊆ hb).
  arewrite (hb ∪ hb ∪ hb ∩ same_loc ⊆ hb).
  arewrite (hb ∪ (hb ∪ coe) ∪ (hb ∪ fre) ⊆ hb ∪ obs).
  { arewrite (coe ⊆ obs). arewrite (fre ⊆ obs).
    unionL; eauto with hahn. }
  rewrite !seq_union_l, !seq_union_r.
  arewrite ((⦗F⦘ ⨾ hb)^? ⨾ hb ⨾ (hb ⨾ ⦗F⦘)^? ⊆ hb).
  { generalize (@hb_trans G). basic_solver. }
  assert (⦗Sc⦘ ⨾ (⦗F⦘ ⨾ hb)^? ⊆ (⦗F∩₁Sc⦘ ⨾ hb)^?) as AA by basic_solver 10.
  sin_rewrite !AA.
  assert ((hb ⨾ ⦗F⦘)^? ⨾ ⦗Sc⦘ ⊆ (hb ⨾ ⦗F∩₁Sc⦘)^?) as BB. by basic_solver 10.
  sin_rewrite !BB.
  assert (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) as CC by mode_solver.
  sin_rewrite !CC.

  rewrite f_sy_hb_in_ord, hb_f_sy_in_ord.
  rewrite hb_in_ord. rewrite !seq_union_l, !seq_union_r.

  set (X:= (obs ∪ dob ∪ aob ∪ boba')).
  unionL.
  3: { arewrite (obs ⊆ X⁺). relsf. }
  2: basic_solver.
  
  rewrite sc_sb_sc_in_boba'. by arewrite (boba' ⊆ X⁺).
Qed.

Lemma ppo_in_dob_helper : ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ dob⁺ .
Proof using CON W_EX_ACQ_SB.
  rewrite path_union1.
  assert (transitive rfi).
  { apply transitiveI; rewrite (wf_rfiD WF). type_solver. }
  relsf; unionL.
  { rewrite (wf_rfiD WF). type_solver. }
  rewrite !seqA.
  arewrite_id (⦗R⦘ ⨾ rfi^?).
  { rewrite (wf_rfiD WF). type_solver. }
  rels.
  arewrite (data ∪ ctrl ∪ addr ⨾ sb^? ∪ (data ⨾ rfi ∪ ctrl ⨾ rfi ∪ addr ⨾ sb^? ⨾ rfi) 
                 ⊆ (data ∪ ctrl ∪ addr ⨾ sb^?) ⨾ rfi^?) by basic_solver 12.
  relsf.
  rewrite unionA.
  rewrite path_ut_first.
  arewrite (data ⨾ rfi^? ⊆ dob).
  rewrite (dob_in_sb WF) at 3.
  rewrite (ctrl_in_sb WF) at 2.
  rewrite (addr_in_sb WF) at 2.
  arewrite (rfi ⊆ sb).
  generalize (@sb_trans G); ins; relsf.
  rewrite !seqA; relsf.
  arewrite (ctrl ⨾ sb^? ⊆ ctrl).
  generalize (ctrl_sb WF); basic_solver 12.
  arewrite (ctrl ⨾ ⦗W⦘⊆ dob).
  unfold Arm.dob; basic_solver 12.

  arewrite ( addr ⨾ sb^? ⨾ ⦗W⦘⊆ dob).
  unfold Arm.dob; basic_solver 12.

  rewrite <- ct_end; basic_solver.
Qed.

Lemma bob_in_boba : bob ⊆ boba' ∪ sb ⨾ ⦗F^ld⦘.
Proof using CON W_EX_ACQ_SB.
  unfold imm_bob.bob, imm_bob.fwbob, Arm.bob', Arm.bob.
  unionL.
  { basic_solver 20. }
  { arewrite (⦗L⦘ ⊆ ⦗L⦘ ⨾ ⦗W⦘) at 1 by basic_solver.
    rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC); rels. }
  { mode_solver 22. }
  { mode_solver 22. }
  basic_solver 15.
Qed.

Lemma W_ex_acq_sb_in_boba1 : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (sb ⨾ ⦗F^ld⦘ ∪ boba')⁺.
Proof using W_EX_ACQ_SB.
  unfold Arm.bob'.
  sin_rewrite W_EX_ACQ_SB.
  case_refl _.
    by type_solver 12.
    rewrite ct_begin.
    rewrite <- inclusion_t_rt, <- ct_step.
    basic_solver 42.
Qed.

Lemma C_SC: acyclic (psc_f ∪ psc_base).
Proof using CON W_EX_ACQ_SB.
  rewrite psc_base_in_ord, psc_f_in_ord.
  rewrite unionK.
  red. rewrite ct_of_ct.
  apply (external_alt_bob' WF CON); auto.
Qed.

End immToARM.
