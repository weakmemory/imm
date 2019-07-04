(******************************************************************************)
(** * Compilation correctness from the IMM memory model to the ARMv8.3 model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Arm.
Require Import imm_common.
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

Hypothesis RMW_CTRL_FAIL : ⦗R_ex⦘ ⨾ sb ⊆ rmw ∩ data ∪ ctrl.
Hypothesis DEPS_RMW_FAIL : rmw_dep ⨾ (rmw ∪ ctrl) ⊆ ctrl.
Hypothesis W_EX_ACQ_SB : ⦗W_ex_acq⦘ ⨾ sb ⊆ sb ⨾ ⦗F^ld⦘ ⨾  sb^?.


Hypothesis CON: ArmConsistent G.

Lemma WF : Wf G.
Proof. apply CON. Qed.
Lemma COMP : complete G.
Proof. apply CON. Qed.
Lemma SC_PER_LOC : sc_per_loc G.
Proof. apply CON. Qed.

(******************************************************************************)
(** * consequences of the compilation scheme  *)
(******************************************************************************)

Lemma rmw_sb_in_ctrl: rmw ⨾ sb ⊆ ctrl.
Proof.
rewrite (dom_l (wf_rmwD WF)).
rewrite (wf_rmwi WF), immediateE, !seqA.
unfolder; ins; desf.
assert (AA: (rmw ∩ data ∪ ctrl) x y).
by revert RMW_CTRL_FAIL; generalize (@sb_trans G); basic_solver 14.
unfolder in AA; desf.
exfalso; eapply (wf_rmwi WF); eauto.
Qed.


Lemma rmw_in_deps: rmw ⊆ deps.
Proof.
rewrite (dom_l (wf_rmwD WF)), (rmw_in_sb WF).
rewrite RMW_CTRL_FAIL; unfold Execution.deps; basic_solver.
Qed.

Lemma rmw_sb_in_deps: rmw ⨾ sb^? ⊆ deps.
Proof.
case_refl _.
apply rmw_in_deps.
rewrite rmw_sb_in_ctrl; vauto.
Qed.

Lemma RMW_CTRL_FAIL' : ⦗R_ex⦘ ⨾ sb ⊆ rmw ∪ ctrl.
Proof.
rewrite RMW_CTRL_FAIL; basic_solver.
Qed.
(******************************************************************************)
(** * imm.hb in terms of Arm relations *)
(******************************************************************************)

Lemma co_sb_loc : ⦗W⦘ ⨾ co^? ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ co^?.
Proof.
case_refl (sb ∩ same_loc); [basic_solver|].
rewrite (dom_r (wf_coD WF)).
arewrite (⦗W⦘ ⨾ (co ⨾ ⦗W⦘)^? ⊆ co^? ⨾ ⦗W⦘) by basic_solver.
rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC), (dom_r (wf_coiD WF)).
generalize (co_trans WF); ie_unfolder; basic_solver 12.
Qed.


Lemma rs_sb_loc : rs ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ co^?.
Proof.
rewrite (rs_in_co  WF SC_PER_LOC COMP), !seqA.
apply co_sb_loc.
Qed.

Lemma rs_sb_loc_rfe : rs ⨾ (sb ∩ same_loc)^? ⨾ rfe ⊆ obs'⁺.
Proof.
rewrite (dom_l (wf_rfeD WF)).
sin_rewrite rs_sb_loc.
unfold Arm.obs'.
rewrite ct_end, rtE, <- ct_step.
basic_solver 12.
Qed.

Lemma rs_rfi: rs ⨾ rfi ⊆ sb ∩ same_loc ⨾ ⦗R⦘ ∪ obs'⁺ ⨾ ⦗R⦘ ⨾ sb.
Proof.
generalize (@sb_same_loc_trans G); ins.
assert (SB: (sb ∩ same_loc)^? ⨾ rfi ⨾ rmw ⊆ sb ∩ same_loc).
{ rewrite (rfi_in_sbloc' WF).
  arewrite (rmw ⊆ rmw ∩ rmw).
  rewrite (rmw_in_sb WF) at 1; rewrite (wf_rmwl WF).
  relsf. }
unfold imm_hb.rs.
rewrite rtE; relsf; unionL.
by rewrite (dom_r (wf_rfiD WF)), (rfi_in_sbloc' WF);
generalize (@sb_same_loc_trans G); basic_solver 12.
by rewrite (dom_r (wf_rfiD WF)); rewrite (rfi_in_sbloc' WF); basic_solver 12.
rewrite rfi_union_rfe; relsf.
rewrite path_ut_last; relsf; unionL.
rewrite (dom_r (wf_rfiD WF)) at 2; rewrite (rfi_in_sbloc' WF) at 2.
sin_rewrite SB; rewrite !seqA; relsf; basic_solver.
arewrite (⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ rfi ⨾ rmw ∪ (sb ∩ same_loc)^? ⨾ rfe ⨾ rmw)＊ ⊆ rs).
by unfold imm_hb.rs; rewrite rfi_union_rfe; relsf.
sin_rewrite rs_sb_loc_rfe.
rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1.
arewrite (rfi ⊆ sb); rewrite (rmw_in_sb WF).
arewrite ((sb ∩ same_loc)^? ⊆ sb^?).
generalize (@sb_trans G); ins; relsf.
Qed.

Lemma rs_rfi_Q: rs ⨾ rfi ⨾ ⦗Q⦘ ⊆ sb ∩ same_loc ⨾ ⦗Q⦘ ∪ (obs' ∪ dob ∪ aob ∪ boba')⁺  ⨾ ⦗Q⦘.
Proof.
generalize (rs_in_co  WF SC_PER_LOC COMP).
unfold imm_hb.rs.
intro X.
rewrite rtE; relsf; unionL.
by rewrite (rfi_in_sbloc' WF);
generalize (@sb_same_loc_trans G); basic_solver 12.
by ie_unfolder; rewrite (rfi_in_sbloc WF); basic_solver 12.
rewrite !seqA, ct_end, !seqA.
arewrite (⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊ ⊆ ⦗W⦘ ⨾ co^?).
revert X.
relsf.
by unfolder; ins; desf; splits; eauto; eapply H; eauto.
rewrite (dom_l (wf_rfD WF)) at 1; rewrite !seqA.
sin_rewrite co_sb_loc.
rewrite rmw_W_ex, !seqA, (rmw_in_fr  WF SC_PER_LOC COMP).
sin_rewrite (rf_fr WF).
generalize (co_trans WF); ins; relsf.
unionR right.
rewrite ct_begin, rtE, <- ct_step.
unfold Arm.aob at 2.
unfold Arm.obs' at 1.
basic_solver 42.
Qed.

Lemma sw_in_ord :
  sw ⊆    ⦗L⦘ ⨾  sb ∩ same_loc ⨾ ⦗Q⦘
        ∪ ⦗L⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘
        ∪ ⦗L∪₁F^sy⦘ ⨾ (obs' ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof.
unfold imm_hb.sw, imm_hb.release.
rewrite (dom_l (wf_rsD WF)), (dom_r (wf_rfeD WF)), !seqA; relsf.
rewrite !seqA.
unionL.
- case_refl (sb ⨾ ⦗F⦘).
  * rewrite (dom_r (wf_rfiD WF)) at 1; rewrite !seqA.
    arewrite (⦗R⦘ ⨾ ⦗Acq⦘ ⊆ ⦗Q⦘) by basic_solver.
    rewrite rs_rfi_Q; relsf; unionL.
    + case_refl _. 
      by basic_solver 12.
      unionR right.
      arewrite (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗Q⦘ ⊆ sb^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
      by basic_solver 12.
      generalize (@sb_trans G); ins; relsf.
      rewrite <- ct_step; unfold Arm.bob'; basic_solver 12.
    + case_refl _. 
      by basic_solver 12.
      unionR right.
      arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb) ⨾ ⦗W⦘ ⊆ ⦗L ∪₁ F^sy⦘ ⨾ boba'^?).
      by unfold Arm.bob'; by basic_solver 21.
      arewrite (boba' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 1.
      relsf; basic_solver.
  * sin_rewrite rs_rfi; relsf; rewrite !seqA.
    generalize (@sb_trans G); ins; relsf; unionL.
    + case_refl _.
      arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
      basic_solver 12.
      unionR right.
      arewrite (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⊆ sb^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
      arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
      by generalize (@sb_trans G); basic_solver 12.
      rewrite <- ct_step; unfold Arm.bob'; basic_solver 12.
    + arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⊆ ⦗L ∪₁ F^sy⦘ ⨾ boba'^?).
      by unfold Arm.bob'; by basic_solver 21.
      arewrite (⦗R⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⊆ boba'^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
      arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
      by unfold Arm.bob'; by basic_solver 21.
      arewrite (boba' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 1.
      arewrite (boba' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 2.
      arewrite (obs' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 2.
      relsf.
- rewrite (dom_l (wf_rsD WF)).
  rewrite !seqA.
  sin_rewrite rs_sb_loc_rfe.
  arewrite (⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ boba'^? ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘).
  { case_refl _.
    by unfold Arm.bob'; by basic_solver 21.
    rewrite !seqA; arewrite (⦗F⦘ ⨾ ⦗Acq⦘ ⊆ ⦗F^ld⦘) by mode_solver 12.
    by unfold Arm.bob'; by basic_solver 21. }
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⊆ ⦗L ∪₁ F^sy⦘ ⨾ boba'^?).
  by unfold Arm.bob'; by basic_solver 21.
  arewrite (boba' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 1.
  arewrite (boba' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 2.
  arewrite (obs' ⊆ obs' ∪ dob ∪ aob ∪ boba') at 2.
  arewrite_id ⦗W⦘.
  relsf.
Qed.

Lemma swe_in_ord : 
  sw \ sb ⊆ ⦗L∪₁F^sy⦘ ⨾ (obs' ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof.
rewrite sw_in_ord.
arewrite_id ⦗L⦘.
arewrite_id ⦗Q⦘.
arewrite_id ⦗R⦘.
arewrite_id ⦗F^ld⦘.
rels.
arewrite (sb ∩ same_loc ⊆ sb).
generalize (@sb_trans G); ins; relsf.
basic_solver 12.
Qed.

Lemma ct_swe_in_ord : 
  (sw \ sb)⁺ ⊆ ⦗L∪₁F^sy⦘ ⨾ (obs' ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof.
apply inclusion_t_ind_left.
apply swe_in_ord.
rewrite swe_in_ord, !seqA.
arewrite_id (⦗Q ∪₁ F^ld ∪₁ F^sy⦘ ⨾ ⦗L ∪₁ F^sy⦘).
basic_solver.
rewrite inclusion_t_rt at 1.
relsf.
Qed.

Lemma sb_ct_swe_in_ord :
  sb ⨾ (sw \ sb)⁺ ⊆  (obs' ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof.
  rewrite ct_swe_in_ord.
  arewrite (sb ⨾ ⦗L ∪₁ F^sy⦘ ⊆ boba').
  { unfold Arm.bob', Arm.bob; basic_solver 15. }
  arewrite (boba' ⊆ (obs' ∪ dob ∪ aob ∪ boba')＊) at 1.
  relsf.
Qed.

Lemma ct_sb_swe_in_ord :
  (sb^? ⨾ (sw \ sb))⁺ ⊆  (obs' ∪ dob ∪ aob ∪ boba')⁺ ⨾ ⦗Q ∪₁ F^ld ∪₁ F^sy⦘.
Proof.
sin_rewrite swe_in_ord.
arewrite (sb^? ⨾ ⦗L ∪₁ F^sy⦘ ⊆ boba'^?).
unfold Arm.bob', Arm.bob; basic_solver 14.
arewrite (boba' ⊆ (obs' ∪ dob ∪ aob ∪ boba')＊) at 1.
relsf.
rewrite inclusion_ct_seq_eqv_r.
relsf.
Qed.

Lemma hb_in_sb_swe : hb ⊆ (sb ∪ (sw \ sb))⁺.
Proof.
unfold imm_hb.hb.
rewrite (ri_union_re G sw) at 1.
apply inclusion_t_t.
basic_solver.
Qed.

Lemma hb_in_ord : hb ⊆ sb ∪ (obs' ∪ dob ∪ aob ∪ boba')⁺ .
Proof.
rewrite hb_in_sb_swe.
rewrite path_union.
generalize (@sb_trans G); ins; relsf.
unionL.
basic_solver.
rewrite ct_sb_swe_in_ord, !seqA.
arewrite (⦗Q ∪₁ F^ld ∪₁ F^sy⦘ ⨾ sb^? ⊆ boba'^?).
unfold Arm.bob', Arm.bob; basic_solver 14.
arewrite (boba' ⊆ (obs' ∪ dob ∪ aob ∪ boba')＊) at 2.
relsf.
Qed.

Lemma sbrel_in_ord : sb ⨾ ⦗L ∪₁ F^sy⦘ ⊆ boba'.
Proof.
unfold Arm.bob', Arm.bob; basic_solver 14.
Qed.

(******************************************************************************)
(** * Coherence *)
(******************************************************************************)

Lemma COH: coherence G.
Proof.
apply coherence_alt.
rewrite hb_in_ord; relsf; unionL.
1: by apply (@sb_irr G).
all:
try by (try arewrite (rfe  ⊆ rf)); rewrite ?rf_in_eco;
rewrite ?co_in_eco, ?fr_in_eco; generalize (eco_trans WF); ins; relsf; 
try (rewrite irreflexive_seqC; apply SC_PER_LOC); apply SC_PER_LOC.
all: try arewrite (rfe ⊆ obs').
all: try arewrite (co ⊆ obs').
all: try arewrite (fr ⊆ obs').
all: set (X := (obs' ∪ dob ∪ aob ∪ boba')⁺).
all: try arewrite (obs' ⊆ (obs' ∪ dob ∪ aob ∪ boba')＊).
all: try unfold X.
all: relsf.
all: apply (external_alt2 WF CON rmw_sb_in_ctrl).
Qed.

(******************************************************************************)
(** * C_ext *)
(******************************************************************************)

Lemma psc_in_ord : sb^? ⨾ psc ⨾ sb^? ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺ .
Proof.
unfold imm.psc.
arewrite (eco ⊆ (co ∪ fr ∪ rfe)＊⨾ rfi^?).
{ unfold Execution_eco.eco; rewrite crE.
  rewrite rfi_union_rfe; relsf; unionL.
  basic_solver 12.
  all: try by rewrite <- inclusion_t_rt, <- ct_step; basic_solver 12.
  all: by rewrite rt_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 12. }
arewrite (rfe ⊆ obs').
arewrite (co ⊆ obs').
arewrite (fr ⊆ obs').
relsf.
arewrite (rfi^? ⨾ hb ⊆ hb).
by arewrite (rfi^?  ⊆ (sb ∪ sw)＊); unfold imm_hb.hb; relsf.
arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) by mode_solver.
rewrite hb_in_ord; relsf.
arewrite !(sb^? ⨾ ⦗F^sy⦘⊆ boba'^? ⨾ ⦗F^sy⦘).
unfold Arm.bob'; basic_solver 21.
arewrite !(⦗F^sy⦘ ⨾ sb^? ⊆ ⦗F^sy⦘ ⨾ boba'^? ).
unfold Arm.bob'; basic_solver 21.
arewrite !(sb ⨾ ⦗F^sy⦘⊆ boba').
arewrite !(⦗F^sy⦘ ⨾ sb⊆ boba').
by unfold Arm.bob'; basic_solver 21.
arewrite_id ⦗F^sy⦘.
rels.
set (X:= (obs' ∪ dob ∪ aob ∪ boba')).
arewrite (boba' ⊆ X⁺).
arewrite (obs' ⊆ X⁺).
relsf.
unfolder; ins; desc; eapply t_trans; eauto.
Qed.

Lemma hb_f_sy_in_ord : hb ⨾ ⦗F^sy⦘ ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
  rewrite hb_in_ord.
  rewrite !seq_union_l.
  unionL.
  2: { basic_solver. }
  arewrite !(sb ⨾ ⦗F^sy⦘⊆ boba').
  rewrite <- ct_step.
  basic_solver 10.
Qed.

Lemma f_sy_hb_in_ord : ⦗F^sy⦘ ⨾ hb ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
  rewrite hb_in_ord.
  rewrite !seq_union_r.
  unionL.
  2: { basic_solver. }
  arewrite !(⦗F^sy⦘ ⨾ sb ⊆ boba').
  2: { rewrite <- ct_step. basic_solver 10. }
  unfold Arm.bob'. basic_solver 10.
Qed.

Lemma sb_psc_f_sb_in_ord : sb^? ⨾ psc_f ⨾ sb^? ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
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
  set (X:= (obs' ∪ dob ∪ aob ∪ boba')).
  assert (boba' ⊆ X⁺) as BB.
  { rewrite <- ct_step. unfold X. basic_solver. }
  sin_rewrite !BB.
  relsf.
Qed.

Lemma psc_f_in_ord : psc_f ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
  arewrite (psc_f ⊆ sb^? ⨾ psc_f ⨾ sb^?) by basic_solver 10.
  apply sb_psc_f_sb_in_ord.
Qed.

Lemma sc_sb_sc_in_boba' : ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘ ⊆ boba'.
Proof.
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

Lemma psc_base_in_ord : psc_base ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺.
Proof.
  unfold imm.psc_base, imm.scb.
  rewrite sb_in_hb.
  arewrite (hb \ same_loc ⊆ hb).
  repeat arewrite (hb ⨾ hb ⊆ hb).
  arewrite (hb ∪ hb ∪ hb ∩ same_loc ⊆ hb).
  rewrite !seq_union_l, !seq_union_r.
  arewrite ((⦗F⦘ ⨾ hb)^? ⨾ hb ⨾ (hb ⨾ ⦗F⦘)^? ⊆ hb).
  { generalize (@hb_trans G). basic_solver. }

  arewrite (co ⊆ obs').
  arewrite (fr ⊆ obs').
  rewrite unionA, unionK.
  assert (⦗Sc⦘ ⨾ (⦗F⦘ ⨾ hb)^? ⊆ (⦗F∩₁Sc⦘ ⨾ hb)^?) as AA
      by basic_solver 10.
  sin_rewrite !AA.
  assert ((hb ⨾ ⦗F⦘)^? ⨾ ⦗Sc⦘ ⊆ (hb ⨾ ⦗F∩₁Sc⦘)^?) as BB.
      by basic_solver 10.
  sin_rewrite !BB.
  assert (⦗F ∩₁ Sc⦘ ⊆ ⦗F^sy⦘) as CC by mode_solver.
  sin_rewrite !CC.

  rewrite f_sy_hb_in_ord, hb_f_sy_in_ord.
  rewrite hb_in_ord. rewrite !seq_union_l, !seq_union_r.

  set (X:= (obs' ∪ dob ∪ aob ∪ boba')).
  unionL.
  3: { arewrite (obs' ⊆ X⁺). relsf. }
  2: basic_solver.
  
  rewrite sc_sb_sc_in_boba'. by arewrite (boba' ⊆ X⁺).
Qed.

Lemma ppo_in_dob_helper : ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ dob⁺ .
Proof.
rewrite path_union1.
assert (transitive rfi).
by apply transitiveI; rewrite (wf_rfiD WF); type_solver.
relsf; unionL.
by rewrite (wf_rfiD WF); type_solver.
rewrite !seqA.
arewrite_id (⦗R⦘ ⨾ rfi^?).
by rewrite (wf_rfiD WF); type_solver.
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

Lemma detour_in_obs : detour ⊆ obs'⁺ .
Proof.
unfold Execution.detour.
arewrite (coe ⊆ obs').
arewrite (rfe ⊆ obs').
rewrite ct_end.
basic_solver 12.
Qed.

Lemma bob_in_boba : bob ⊆ boba' ∪ coi ∪ sb ⨾ ⦗F^ld⦘.
Proof.
unfold imm_common.bob, imm_common.fwbob, Arm.bob', Arm.bob.
unionL.
- basic_solver 15.
- arewrite (⦗L⦘ ⊆ ⦗W⦘) at 1 by basic_solver.
  rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC); rels.
- mode_solver 22.
- mode_solver 22.
- basic_solver 15.
Qed.

Lemma W_ex_acq_sb_in_boba1 : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (sb ⨾ ⦗F^ld⦘ ∪ boba')⁺.
Proof.
unfold Arm.bob'.
sin_rewrite W_EX_ACQ_SB.
case_refl _.
by type_solver 12.
rewrite ct_begin.
rewrite <- inclusion_t_rt, <- ct_step.
basic_solver 42.
Qed.

Lemma ar_int_in_ord : ⦗R⦘ ⨾ G.(ar_int)⁺ ⨾ ⦗W⦘ ⊆ (obs' ∪ dob ∪ aob ∪ boba')⁺ .
Proof.
unfold ar_int.
 rewrite (ppo_alt WF rmw_in_deps RMW_CTRL_FAIL' DEPS_RMW_FAIL) at 1.
transitivity (⦗R⦘ ⨾  ((obs'⁺∩ sb) ∪ dob ∪ aob ∪ boba' ∪ sb ⨾ ⦗F^ld⦘)⁺ ⨾ ⦗W⦘).
- arewrite (detour ⊆ detour ∩ sb).
  rewrite W_ex_acq_sb_in_boba1, bob_in_boba, ppo_in_dob_helper, detour_in_obs.
  hahn_frame.
  apply inclusion_t_t2.
  apply_unionL_once.
  apply_unionL_once.
  apply_unionL_once.
  apply_unionL_once.
  apply_unionL_once.
  * rewrite <- ct_step; basic_solver.
  * rewrite <- ct_step; rewrite <- ct_step; unfold Arm.obs'; ie_unfolder; basic_solver 12.
  * rewrite <- ct_step; basic_solver.
  * apply inclusion_t_t; basic_solver 12.
  * by unfolder; ins; econs; eauto.
  * apply inclusion_t_t; basic_solver 12.
- rewrite path_union.
  relsf; unionL.
  * arewrite_id ⦗R⦘; arewrite_id ⦗W⦘.
    rels.
    arewrite (obs'⁺ ∩ sb ⊆ obs'⁺).
    apply inclusion_t_t2.
    apply_unionL_once.
    apply_unionL_once.
    apply_unionL_once.
    + apply inclusion_t_t; basic_solver.
    + rewrite <- ct_step; basic_solver.
    + rewrite <- ct_step; basic_solver.
    + rewrite <- ct_step; basic_solver.
  * rewrite (dob_in_sb WF) at 1 2.
    rewrite (aob_in_sb WF) at 1 2.
    rewrite (bob'_in_sb WF) at 1 2.
    arewrite (obs'⁺ ∩ sb ⊆ sb).
    rewrite ct_begin.
    arewrite_id ⦗F^ld⦘ at 2.
    generalize (@sb_trans G); ins; relsf.
    arewrite (⦗F^ld⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗F^ld⦘ ⨾ sb) by type_solver.
    unfold Arm.bob', Arm.bob; rewrite <- ct_step; basic_solver 21.
Qed.

Lemma C_EXT: acyc_ext G.
Proof.
apply (acyc_ext_helper WF).
rewrite ar_int_in_ord, psc_in_ord.
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
