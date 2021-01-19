(******************************************************************************)
(** * Compilation correctness from the IMM memory model to the POWER model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Power_fences.
Require Import Power_ppo.
Require Import Power.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm.

Set Implicit Arguments.

Section immToPower.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'acts'" := (acts G).
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
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).


(* imm *)
Notation "'sw'" := (sw G).
Notation "'release'" := (release G).
Notation "'rs'" := (rs G).
Notation "'hb'" := (hb G).
Notation "'ppo'" := (ppo G).
Notation "'psc'" := (psc G).
Notation "'bob'" := (bob G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* power *)
Notation "'ctrli'" := (ctrli G).
Notation "'sync'" := (sync G).
Notation "'lwsync'" := (lwsync G).
Notation "'fence'" := (fence G).
Notation "'ppop'" := (Power_ppo.ppo G).
Notation "'hbp'" := (Power.hb G).
Notation "'S'" := (S G).
Notation "'detour'" := (detour G).

Notation "'F^isync'" := (F ∩₁ (fun a => is_true (is_rlx lab a))).
Notation "'F^lwsync'" := (F ∩₁ (fun a => is_true (is_ra lab a))).
Notation "'F^sync'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

Hypothesis SC_F: Sc ⊆₁ F∩₁Sc.
Hypothesis NO_W_REL : W∩₁Rel ≡₁ ∅.
Hypothesis R_ACQ_SB : ⦗R∩₁Acq⦘ ⨾ sb ⊆ rmw ∪ ctrl ⨾ ⦗F^isync⦘ ⨾ sb^? ∪ sb ⨾ ⦗F^lwsync⦘ ⨾ sb^?.
Hypothesis RMW_DEPS : rmw ⊆ ctrl ∪ data.
Hypothesis RMW_CTRL_FAIL : ⦗R_ex⦘ ⨾ sb ⊆ ctrl.
Hypothesis DATA_RMW : data ⨾ ⦗W_ex⦘ ⨾ sb ⊆ ctrl.
Hypothesis DEPS_RMW_FAIL : rmw_dep ⨾ (rmw ∪ ctrl) ⊆ ctrl.

Hypothesis CON: PowerConsistent G.

Lemma WF : Wf G.
Proof using CON. apply CON. Qed.

(******************************************************************************)
(** * extension of sw  *)
(******************************************************************************)
Definition rs_big := ⦗W⦘ ⨾ (rf ⨾ rmw ∪ sb ∩ same_loc)＊ ⨾ ⦗W⦘.

Lemma rs_big_alt: rs_big ⊆ 
 ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘)＊.
Proof using CON.
unfold rs_big.
hahn_frame.
rewrite rtE; relsf; unionL; [basic_solver 12|].
eapply ct_ind_left with (P:= fun r => r ⨾ ⦗W⦘).
 by eauto with hahn.
relsf; unionL.

erewrite <- inclusion_step_rt; [|edone].
rewrite (dom_l (wf_rfD WF)) at 1.
basic_solver 21.
basic_solver 21.
ins; rewrite !seqA, H.
generalize (@sb_same_loc_trans G); ins; relsf.
unionL; [|basic_solver 12].


rewrite (dom_l (wf_rfD WF)) at 1.
rewrite !seqA.
arewrite (⦗W⦘ ⨾ rf ⊆ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ rf).
basic_solver 12.
hahn_frame.
rewrite <- !seqA.
rewrite <- ct_begin.
basic_solver.
Qed.

Lemma wf_rs_bigD : rs_big ≡ ⦗W⦘ ⨾ rs_big ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold rs_big.
basic_solver 42.
Qed.

Lemma rs_in_rs_big: rs ⊆ rs_big.
Proof using CON.
unfold imm_hb.rs, rs_big.
relsf; unionL.
rewrite rtE, <- ct_step; basic_solver.
rewrite rtE; relsf; unionL; [basic_solver 12|].
rewrite (dom_r (wf_rmwD WF)) at 1.
rewrite <- !seqA, inclusion_ct_seq_eqv_r.
hahn_frame.
arewrite ((sb ∩ same_loc)^? ⊆ (rf ⨾ rmw ∪ sb ∩ same_loc)＊).
arewrite (rf ⨾ rmw ⊆ (rf ⨾ rmw ∪ sb ∩ same_loc)＊) at 2.
relsf.
Qed.

Definition sw_big := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs_big ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.


Lemma sw_in_sw_big : sw ⊆ sw_big.
Proof using CON.
unfold imm_hb.sw, imm_hb.release, sw_big.
rewrite rs_in_rs_big.
relsf; unionL.
by arewrite (rfi ⊆ rf).
unfold rs_big.
rewrite (dom_l (wf_rfeD WF)) at 1.
arewrite ((sb ∩ same_loc)^? ⊆ (rf ⨾ rmw ∪ sb ∩ same_loc)＊).
arewrite_id ⦗W⦘ at 2; rels.
by arewrite (rfe ⊆ rf).
Qed.


(******************************************************************************)
(** * Simplifications due to NO_W_REL   *)
(******************************************************************************)

Lemma no_w_rel : 
  ⦗Rel⦘ ⨾ ⦗W⦘ ⊆ ∅₂.
Proof using NO_W_REL.
unfolder; ins; desf; eapply NO_W_REL; basic_solver.
Qed.

Lemma sw_no_w_rel : 
  sw ⊆ ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ rs_big ⨾ rf ⨾ (⦗R ∩₁ Acq⦘ ∪ sb ⨾ ⦗F ∩₁ Acq⦘).
Proof using CON NO_W_REL.
rewrite sw_in_sw_big.
unfold  sw_big, imm_hb.release.
rewrite (dom_l (wf_rs_bigD)).
case_refl (⦗F⦘ ⨾ sb) at 1.
by sin_rewrite no_w_rel; basic_solver.
by rewrite (dom_r (wf_rfD WF)) at 1; basic_solver 22.
Qed.

(* Lemma detour_ppo_w_no_w_rel : 
  (coe ⨾ rfe) ∩ sb ⨾ ppo ⨾ ⦗W⦘ ⊆ 
 (coe ⨾ rfe) ∩ sb ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ (coe ⨾ rfe) ∩ sb ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘.
Proof using.
rewrite (detour_ppo_w WF).
arewrite_false (⦗W ∩₁ Rel⦘).
  by generalize no_w_rel; basic_solver.
basic_solver 12.
Qed.*)

Lemma bob_no_w_rel : 
  bob ⊆ ⦗R ∩₁ Acq⦘ ⨾ sb ∪ sb ⨾ ⦗F^lwsync⦘ ∪ ⦗F^lwsync⦘ ⨾ sb.
Proof using NO_W_REL.
unfold imm_bob.bob, imm_bob.fwbob.
sin_rewrite !NO_W_REL.
basic_solver 21.
Qed.

(******************************************************************************)
(** * consequences of the compilation scheme  *)
(******************************************************************************)

Lemma rmw_sb_in_ctrl: rmw ⨾ sb ⊆ ctrl.
Proof using CON DATA_RMW RMW_DEPS.
  rewrite rmw_W_ex. rewrite seqA.
  rewrite RMW_DEPS. rewrite !seq_union_l.
  unionL; auto.
  arewrite_id ⦗W_ex⦘. rewrite seq_id_l. apply WF.
Qed.

Lemma rmw_in_deps: rmw ⊆ deps.
Proof using RMW_DEPS.
rewrite RMW_DEPS. unfold Execution.deps. eauto with hahn.
Qed.

Lemma rmw_sb_in_deps: rmw ⨾ sb^? ⊆ deps.
Proof using CON DATA_RMW RMW_DEPS.
case_refl _.
apply rmw_in_deps.
rewrite rmw_sb_in_ctrl; vauto.
Qed.

Lemma RMW_CTRL_FAIL' : ⦗R_ex⦘ ⨾ sb ⊆ rmw ∪ ctrl.
Proof using RMW_CTRL_FAIL.
rewrite RMW_CTRL_FAIL; basic_solver.
Qed.

Lemma rmw_sb_W_in_ppo: rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppop.
Proof using CON DATA_RMW RMW_DEPS.
sin_rewrite rmw_sb_in_deps.
by sin_rewrite (deps_in_ppo WF).
Qed.

Lemma r_acq_sb: ⦗R∩₁Acq⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ rmw ∪ ctrli ⨾ ⦗RW⦘ ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘.
Proof using CON NO_W_REL RMW_CTRL_FAIL R_ACQ_SB SC_F.
  arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R⦘ ⨾ ⦗R ∩₁ Acq⦘) by basic_solver.
  sin_rewrite R_ACQ_SB.
  unfold Power_ppo.ctrli.
  rewrite (wf_ctrlD WF) at 1.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  arewrite (⦗F^isync⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ⦗F^isync⦘ ⨾ sb ⨾ ⦗RW⦘) by type_solver 21.
  arewrite (⦗F^lwsync⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘) by type_solver 21.
  unionL; [| |done]; basic_solver 12.
Qed.

(*Lemma ppo_alt: ppo ⊆ ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘.
Proof using.
rewrite (ppo_alt WF RMW_CTRL_FAIL).
rewrite path_ut_first; relsf; unionL.
- hahn_frame.
  apply inclusion_t_t.
  rewrite rmw_sb_in_deps.
  basic_solver.
- arewrite (deps ∪ rfi ∪ rmw ⨾ sb^? ∪ rmw_dep ⊆ sb).
  { rewrite (deps_in_sb WF).
    arewrite (rfi ⊆ sb).
    rewrite (rmw_in_sb WF).
    rewrite (rmw_dep_in_sb WF).
    generalize (@sb_trans G); ins; relsf. }
  generalize (@sb_trans G); ins; relsf.
  rewrite (dom_r (wf_rmw_depD WF)), !seqA.
  rewrite crE at 2; relsf; unionL.
  by rewrite R_ex_in_R; type_solver.
  hahn_frame.
  sin_rewrite RMW_CTRL_FAIL.
  relsf.
  rewrite (failed_rmw_fail WF).
  rels.
  sin_rewrite DEPS_RMW_FAIL.
  arewrite (ctrl ⊆ deps).
  rewrite rmw_sb_in_deps.
  rewrite ct_end.
  arewrite (deps ∪ rfi ∪ deps ⊆ deps ∪ rfi).
  basic_solver 21.
Qed.
*)

(******************************************************************************)
(** * imm.hb in terms of Power relations *)
(******************************************************************************)

Lemma external_helper : 
 ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ (rf ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊ ⨾ rf ⨾ (⦗R ∩₁ Acq⦘ ∪ sb ⨾ ⦗F ∩₁ Acq⦘) \ sb ⊆
 ⦗F ∩₁ Rel⦘ ⨾ sb ⨾  ((rf ⨾ rmw⨾  sb^? ⨾ ⦗W⦘)＊ ⨾ rf \ sb) ⨾ (⦗R ∩₁ Acq⦘ ∪ sb ⨾ ⦗F ∩₁ Acq⦘).
Proof using.
generalize (@sb_trans G).
basic_solver 22.
Qed.

Lemma sb_sw_in_S: sb^? ⨾ (sw \ sb) ⊆ S.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite sw_no_w_rel.
unfold Power.S.
rewrite (rs_big_alt).
arewrite (sb ∩ same_loc ⊆ sb).
arewrite (sb ⨾ ⦗W⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ sb) by generalize (@sb_trans G); basic_solver.
rewrite external_helper.
rewrite (rf_rmw_sb_rt_rf WF), (rmw_rf_rt_1 WF).
rewrite rmw_sb_W_in_ppo.
arewrite ((ppop ∪ rfe)＊ ⊆ hbp＊).
ie_unfolder.
rewrite rf_in_eco at 2.
arewrite (⦗F ∩₁ Rel⦘ ⊆ ⦗F^lwsync⦘) by mode_solver.
arewrite (⦗F ∩₁ Acq⦘ ⊆ ⦗F^lwsync⦘) by mode_solver.
arewrite (sb ⨾ sb^? ⊆ sb).
generalize (@sb_trans G); basic_solver.
hahn_frame.
generalize (@sb_trans G); basic_solver 42.
Qed. 

Lemma sw_sb_in_S: sb^? ⨾ (sw \ sb) ⨾ sb ⨾ ⦗RW⦘ ⊆ S.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
  rewrite sw_no_w_rel.
  unfold Power.S.
  rewrite (rs_big_alt).
  arewrite (sb ∩ same_loc ⊆ sb).
  arewrite (sb ⨾ ⦗W⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ sb) by generalize (@sb_trans G); basic_solver.
  rewrite external_helper.
  rewrite (rf_rmw_sb_rt_rf WF).
  rewrite (dom_r (wf_rfeD WF)) at 1.
  rewrite !seqA.
  arewrite (sb ⨾ sb^? ⊆ sb).
  by generalize (@sb_trans G); basic_solver.
  rewrite (rmw_rf_rt_1 WF).
  arewrite (⦗F ∩₁ Rel⦘ ⊆ ⦗F^lwsync⦘) by mode_solver.
  arewrite (⦗F ∩₁ Acq⦘ ⊆ ⦗F^lwsync⦘) by mode_solver.
  hahn_frame.
  arewrite (⦗R⦘ ⨾ (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊ ⨾ rfi^? ⊆ 
    (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊ ⨾ rmw ⨾ sb^? ∪ (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊ ⨾ ⦗R⦘).
  { rewrite rtE at 1; relsf; unionL.
    by rewrite (dom_l (wf_rfiD WF)) at 1; type_solver 12.
    rewrite ct_end; relsf; unionL; rewrite !seqA.
    arewrite (rfi ⊆ sb).
    generalize (@sb_trans G); basic_solver 12.
    arewrite (rfe ⨾ rfi^? ⊆ rfe).
    by rewrite (dom_l (wf_rfiD WF)); rewrite (dom_r (wf_rfeD WF)); type_solver.
    rewrite (dom_r (wf_rfeD WF)) at 2.
    arewrite (rfe ⊆ (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊) at 2.
    relsf; unionR right; hahn_frame; basic_solver 12. }
  arewrite ((rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊ ⊆ hbp＊).
  { rewrite rmw_sb_W_in_ppo.
    arewrite (ppop ⊆ hbp).
    arewrite (rfe ⊆ hbp).
    relsf. }
  relsf; unionL; rewrite ?seqA.
- sin_rewrite r_acq_sb.
  relsf.
  arewrite (sb^? ⨾ ⦗R⦘ ⨾ sb ⊆ sb).
  { generalize (@sb_trans G); basic_solver. }
  rewrite (dom_r (wf_rmwD WF)) at 2.
  rewrite (rmw_in_sb WF) at 2.
  generalize (@sb_trans G); ins; relsf.
  arewrite (sb ⊆ sb^?) at 1.
  sin_rewrite rmw_sb_W_in_ppo.
  rewrite (wf_ctrliD) at 1.
  rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite !seqA.
  arewrite (⦗W⦘ ⨾ sb^? ⨾ ⦗R⦘ ⊆ sb) by type_solver 12.
  sin_rewrite rmw_sb_in_ctrl.
  rewrite (ctrl_ctrli_RW_in_ppo WF).
  arewrite (rmw ⨾ sb ⊆ ⦗R⦘ ⨾ sb).
  { rewrite (dom_l (wf_rmwD WF)), (rmw_in_sb WF).
    generalize (@sb_trans G). type_solver. }
  rewrite R_sb_F_sb_RW_in_fence.
  arewrite (ppop ⊆ hbp＊).
  arewrite (fence ⊆ hbp＊).
  relsf; basic_solver 12.
- rewrite (dom_l (wf_rmwD WF)) at 1.
  rewrite (rmw_in_sb WF); rewrite !seqA.
  generalize (@sb_trans G); ins; relsf.
  sin_rewrite (@R_sb_F_sb_RW_in_fence G).
  arewrite (fence ⊆ hbp＊); relsf; basic_solver 12.
- sin_rewrite r_acq_sb.
  rewrite (dom_r (wf_rmwD WF)) at 1.
  rewrite rmw_in_deps, (deps_in_ppo WF).
  relsf.
  rewrite (ctrli_RW_in_ppo WF).
  arewrite !(⦗R⦘ ⨾ ppop ⊆ hbp＊).
  rewrite R_sb_F_sb_RW_in_fence.
  arewrite (fence ⊆ hbp＊).
  relsf; basic_solver 12.
- sin_rewrite (@R_sb_F_sb_RW_in_fence G).
  arewrite (fence ⊆ hbp＊); relsf; basic_solver 12.
Qed.

Lemma hb_in_S_sb : hb ⊆ sb ∪ S ⨾ sb^?.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite hb_in_sb_swe, path_union.
rewrite (ct_of_trans (@sb_trans G)), (rt_of_trans (@sb_trans G)).
rewrite sb_sw_in_S.
rewrite (ct_of_trans (S_trans WF)).
basic_solver.
Qed.

Lemma hb_rw_in_S : hb ⨾ ⦗RW⦘ ⊆ sb ∪ S.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite hb_in_sb_swe, path_union.
rewrite (ct_of_trans (@sb_trans G)), (rt_of_trans (@sb_trans G)).
case_union _ _.
unionL; [basic_solver|].
rewrite ct_end, !seqA.
arewrite (sb^? ⨾ (sw \ sb) ⨾ sb^? ⨾ ⦗RW⦘ ⊆ S).
by generalize sb_sw_in_S sw_sb_in_S; basic_solver 12.
rewrite sb_sw_in_S.
rewrite <- ct_end.
rewrite (ct_of_trans (S_trans WF)).
basic_solver.
Qed.

Lemma rw_hb_f_in_hbp : ⦗RW⦘ ⨾ hb ⨾  ⦗F^sync⦘  ⊆ sb ⨾  ⦗F^sync⦘ ∪ fence ⨾ hbp＊ ⨾ sb ⨾ ⦗F^sync⦘.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite hb_in_S_sb.
unfold Power.S.
relsf; unionL; [basic_solver|].
rewrite !seqA.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗F^lwsync⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F^lwsync⦘) by type_solver.

rewrite (dom_l (wf_rfeD WF)), !seqA.
sin_rewrite RW_sb_F_sb_W_in_fence.

arewrite ((sb ⨾ ⦗F^lwsync⦘ ∪ eco ∩ sb)^? ⨾ sb^? ⨾ ⦗F^sync⦘ ⊆  sb^? ⨾ ⦗F^sync⦘).
generalize (@sb_trans G); basic_solver 12.

arewrite (rfe ⨾ hbp＊ ⨾ sb^? ⨾ ⦗F^sync⦘ ⊆ rfe ⨾ hbp＊ ⨾ sb ⨾ ⦗F^sync⦘).
{ rewrite rtE at 1.
rewrite (dom_r (wf_rfeD WF)) at 1.
rewrite (dom_r (wf_cthbD WF)) at 1.
type_solver 12. }

arewrite (rfe ⊆ hbp).
seq_rewrite <- ct_begin.
basic_solver 12.
Qed.

(******************************************************************************)
(** * Coherence *)
(******************************************************************************)

Lemma COH: coherence G.
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
red; rewrite (dom_l (wf_ecoD WF)).
sin_rewrite hb_rw_in_S.
case_union _ _; unionL; [by apply CON| apply S_eco_irr; apply CON].
Qed.

(******************************************************************************)
(** * C_ext *)
(******************************************************************************)

Lemma acyc_psc_hbp: acyclic (sb^? ⨾ psc ⨾ sb^? ∪ hbp).
Proof using CON DATA_RMW NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite unionC.
apply acyclic_union; [by apply CON|].
rewrite !seqA.
unfold imm.psc.
rewrite (dom_r (wf_ecoD WF)), !seqA.
sin_rewrite rw_hb_f_in_hbp.
rewrite (dom_l (wf_ecoD WF)), !seqA.
sin_rewrite hb_rw_in_S.
arewrite ((sb ⨾ ⦗F^sync⦘ ∪ fence ⨾ hbp＊ ⨾ sb ⨾ ⦗F^sync⦘) ⊆ (fence ⨾ hbp＊)^? ⨾ sb ⨾ ⦗F^sync⦘).
  by rewrite rtE; basic_solver 12.
arewrite ((sb ∪ S) ⨾ eco ⊆ sb ⨾ eco ∪ S ⨾ eco).
  by basic_solver.
rewrite (dom_l (wf_ecoD WF)) at 2.
sin_rewrite (S_rw CON); rewrite !seqA.
arewrite ((eco ∩ sb)^? ⨾ eco ⊆ eco).
  by generalize (eco_trans (CON_WF CON)); type_solver.
arewrite (sb^? ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ rfe ⨾ hbp＊ ⊆ sb ⨾ hbp＊).
  by generalize (rfe_in_hb) (@sb_trans G) (ct_begin hbp); basic_solver 12.
arewrite (sb ⨾ eco ∪ sb ⨾ hbp＊ ⨾ eco ⊆ sb ⨾ hbp＊ ⨾ eco).
  by rewrite rtE; basic_solver 12.
arewrite (hbp＊ ⨾ eco ⊆ ⦗RW⦘ ⨾ hbp＊ ⨾ eco).
{ rewrite rtE at 1.
rewrite (dom_l (wf_cthbD WF)) at 1.
rewrite (dom_l (wf_ecoD WF)) at 1.
basic_solver 22. }

rotate 4.

arewrite (eco ⨾ (fence ⨾ hbp＊)^? ⊆ eco ⨾ (fence ⨾ hbp＊)^? ⨾ ⦗RW⦘).
{ rewrite rtE at 1.
rewrite (dom_r (wf_cthbD WF)) at 1.
rewrite (dom_r (wf_ecoD WF)).
rewrite (dom_r (wf_fenceD WF)). 
basic_solver 22. }

rotate 1.

arewrite (⦗F^sync⦘ ⨾ sb^? ⨾ hbp＊ ⨾ sb^? ⨾ ⦗F^sync⦘ ⊆ ⦗F^sync⦘ ⨾ sb^? ∪ ⦗F^sync⦘ ⨾  sb ⨾ hbp⁺ ⨾ sb ⨾ ⦗F^sync⦘).
{ rewrite rtE.
relsf; unionL.
by generalize (@sb_trans G); basic_solver 12.
unionR right.
rewrite (wf_cthbD WF) at 1.
type_solver 22. }

generalize (@sb_trans G); ins.
relsf; rewrite !seqA; relsf.
rewrite (wf_cthbD WF) at 1; rewrite !seqA.
arewrite !(⦗RW⦘ ⨾ sb ⨾ ⦗F^sync⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ sync).
arewrite(sync ⊆ hbp) at 3.
arewrite(hbp⁺ ⨾ hbp ⨾ hbp＊ ⊆ hbp＊).
by rewrite <- ct_begin, ct_ct; basic_solver.
relsf.
rotate 2.
eapply acyclic_mon.
apply (eco_fench_hb_acyclic CON).
basic_solver 42.
Qed.

Lemma ppo_ctrli_detour_seq_W_ex_sb_W_in_ppo_ctrli_detour :
  ((ppo ∪ ctrli ∪ detour) ⨾ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘) ⊆ ppo ∪ ctrli ∪ detour.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
  relsf; unionL.
  * rewrite (ppo_alt WF RMW_DEPS RMW_CTRL_FAIL' DATA_RMW DEPS_RMW_FAIL) at 1.
    rewrite !seqA.
    rewrite ct_end; relsf; rewrite !seqA.
    arewrite_false (rfi ⨾ ⦗W⦘).
      by rewrite (dom_r (wf_rfiD WF)); type_solver.
      rels.
      unionL.
  + arewrite_id (⦗W⦘) at 1; rels.
    sin_rewrite DATA_RMW.
    unionR left -> left.
    unfold imm_ppo.ppo.
    hahn_frame.
    rewrite ct_end.
    apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42.
  + arewrite (ctrl ⨾ ⦗W⦘ ⨾ ⦗W_ex⦘ ⨾ sb ⊆ ctrl).
      by generalize (ctrl_sb WF); basic_solver.
      unionR left -> left.
      unfold imm_ppo.ppo.
      hahn_frame.
      rewrite ct_end.
      apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42.
  + arewrite_id (⦗W⦘ ⨾ ⦗W_ex⦘).
    basic_solver.
    generalize (@sb_trans G); ins; relsf.
    unionR left -> left.
    unfold imm_ppo.ppo.
    hahn_frame.
    rewrite ct_end.
    apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42.
    * arewrite_id (⦗W_ex⦘) at 1.
      rels.
      sin_rewrite ctrli_sb.
      basic_solver.
    * rewrite (W_ex_in_W WF).
      rewrite (dom_r (wf_detourD WF)).
      type_solver.
Qed.

Lemma C_EXT_helper0: 
  ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆ ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour)⁺.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite path_union2.
relsf; unionL.
- done.
- rewrite ct_begin.
  rewrite (W_ex_in_W WF), !seqA.
  arewrite_false (⦗R⦘ ⨾ ⦗W⦘). 
  type_solver.
  rels.
- arewrite (⦗R⦘ ⨾ (⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⊆ ⦗R⦘).
  rewrite (W_ex_in_W WF).
  rewrite rtE, ct_begin; type_solver 16.
  assert (transitive (⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)).
  { apply transitiveI; rewrite !seqA.
    arewrite_id (⦗W⦘ ⨾ ⦗W_ex⦘).
    basic_solver.
    relsf.
    arewrite (sb ⨾ sb ⊆ sb).
    apply transitiveI, (@sb_trans G).
    done. }
  relsf.
  rewrite (ct_end (ppo ∪ ctrli ∪ detour)) at 1; rewrite !seqA.
  rewrite ppo_ctrli_detour_seq_W_ex_sb_W_in_ppo_ctrli_detour.
  rewrite <- ct_end; relsf.
Qed.

Lemma C_EXT_helper05: 
  ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆
  ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
rewrite path_union2.
relsf; unionL.
- done.
- rewrite ct_begin.
  rewrite (W_ex_in_W WF) at 1. rewrite !seqA.
  arewrite_false (⦗R⦘ ⨾ ⦗W⦘). 
  type_solver.
  rels.
- arewrite (⦗R⦘ ⨾ (⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⊆ ⦗R⦘).
  { rewrite (W_ex_in_W WF).
    rewrite rtE, ct_begin; type_solver 16. }
  assert (transitive (⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘)).
  { apply transitiveI; rewrite !seqA.
    arewrite_id (⦗W⦘ ⨾ ⦗W_ex⦘).
    basic_solver.
    relsf.
    arewrite (sb ⨾ sb ⊆ sb).
    apply transitiveI, (@sb_trans G).
    done. }
  relsf.
  rewrite (ct_end (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)) at 1; rewrite !seqA.
  arewrite (((ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ⨾ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘) ⊆
             ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘).
  { rewrite seq_union_l.
    rewrite ppo_ctrli_detour_seq_W_ex_sb_W_in_ppo_ctrli_detour.
    rewrite !seqA. arewrite_false (⦗R ∩₁ Acq⦘ ⨾ ⦗W_ex⦘).
    { rewrite (W_ex_in_W WF). type_solver. }
    basic_solver. }
  rewrite <- ct_end; relsf.
Qed.

Lemma R_W_ex_rfi_R_Acq_in_R : ⦗R⦘ ⨾ (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)＊ ⊆ ⦗R⦘.
Proof using CON NO_W_REL RMW_CTRL_FAIL R_ACQ_SB SC_F.
  rewrite (W_ex_in_W WF).
  rewrite rtE, ct_begin; type_solver 16.
Qed.

Lemma W_ex_rfi_R_Acq_ct_step : (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⊆ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘.
Proof using CON NO_W_REL RMW_CTRL_FAIL R_ACQ_SB SC_F.
  rewrite ct_begin. rewrite rtE, seq_union_r, seq_id_r. unionL; [done|].
  rewrite ct_begin. rewrite !seqA.
  arewrite_false (⦗R ∩₁ Acq⦘ ⨾ ⦗W_ex⦘).
  { rewrite (W_ex_in_W WF). type_solver. }
  basic_solver.
Qed.

(* Lemma C_EXT_helper07:  *)
(*   ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⊆ *)
(*   ⦗R⦘ ⨾ (ppo ∪ ctrli ∪ detour)⁺. *)
(* Proof using. *)
(* rewrite path_union2. *)
(* relsf; unionL. *)
(* - done. *)
(* - rewrite ct_begin. *)
(*   rewrite (W_ex_in_W WF) at 1. rewrite !seqA. *)
(*   arewrite_false (⦗R⦘ ⨾ ⦗W⦘).  *)
(*   type_solver. *)
(*   rels. *)
(* - sin_rewrite AA. *)
(*   rewrite (ct_end (ppo ∪ ctrli ∪ detour)) at 1; rewrite !seqA. *)
(*   arewrite (((ppo ∪ ctrli ∪ detour) ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ⊆ *)
(*              ppo ∪ ctrli ∪ detour). *)
(*   { rewrite !seq_union_l. unionL. *)
(*     { *)


(*     rewrite ppo_ctrli_detour_seq_W_ex_sb_W_in_ppo_ctrli_detour. *)
(*     rewrite !seqA. arewrite_false (⦗R ∩₁ Acq⦘ ⨾ ⦗W_ex⦘). *)
(*     { rewrite (W_ex_in_W WF). type_solver. } *)
(*     basic_solver. } *)
(*   rewrite <- ct_end; relsf. *)
(* Qed. *)

Lemma C_EXT_helper08 : ⦗R⦘ ⨾ (ppop ∪ ctrli ∪ detour)⁺ ⨾ ⦗RW⦘ ⊆ hbp.
Proof using CON. rewrite (r_ct_ppo_detour_ppo WF); vauto. Qed.

Lemma C_EXT_helper1 : 
  ⦗R⦘ ⨾ (bob ∪ ppo ∪ detour ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⨾ ⦗W⦘ ⊆ hbp.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
assert (⦗R⦘ ⨾ (ppop ∪ ctrli ∪ detour)⁺ ⨾ ⦗W⦘ ⊆ hbp) as PCDINHB.
{ arewrite (W ⊆₁ RW).
  rewrite (r_ct_ppo_detour_ppo WF); vauto. }

rewrite bob_no_w_rel. 
transitivity (⦗R⦘⨾ (⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ sb ⨾ ⦗F^lwsync⦘ ∪ ⦗F^lwsync⦘ ⨾ sb ∪ ppo ∪ detour
   ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⨾ ⦗W⦘).
arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ∪ sb ⨾ ⦗F^lwsync⦘ ∪ ⦗F^lwsync⦘ ⨾ sb ∪ ppo ∪ detour
   ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘
⊆ sb ⨾ ⦗F^lwsync⦘ ∪ ⦗F^lwsync⦘ ⨾ sb ∪ ppo ∪ detour
   ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪ ⦗R ∩₁ Acq⦘ ⨾ sb).
basic_solver 12.
rewrite path_absorb_rt.
2: by right; arewrite (rfi ⊆ sb); rewrite (ppo_in_sb WF), detour_in_sb; generalize (@sb_trans G); basic_solver 22.
2: by apply transitiveI; generalize (@sb_trans G); basic_solver 22.
relsf; unionL; rewrite ?seqA.
hahn_frame; apply inclusion_t_t; basic_solver 12.
arewrite (⦗W⦘ ⊆ ⦗W⦘ ⨾ ⦗W⦘) at 2 by basic_solver.
hahn_frame.
rewrite ct_end.
apply seq_mori.
apply inclusion_rt_rt; basic_solver 12.
basic_solver 22.
rewrite r_acq_sb, (rmw_in_ppo WF).
arewrite_id ⦗RW⦘ at 1; rels.
arewrite (ppo ∪ ctrli ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ sb ⨾ ⦗F^lwsync⦘ ∪ ⦗F^lwsync⦘ ⨾ sb ∪ ppo ∪ detour ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘
⊆ ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪ sb^? ⨾ ⦗F^lwsync⦘ ⨾ sb^?).
basic_solver 12.
rewrite path_union.
relsf; unionL.
- arewrite
    (ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆
     ppo ∪ ctrli ∪ detour ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪ ⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘).
  { basic_solver 10. }
  sin_rewrite C_EXT_helper05. rewrite !seqA.
  rewrite path_union2.
  rewrite !seq_union_l, !seq_union_r. unionL.
  { rewrite (ppo_alt WF RMW_DEPS RMW_CTRL_FAIL' DATA_RMW DEPS_RMW_FAIL).
      by rewrite !(r_deps_rfi WF). }
  { rewrite (ppo_alt WF RMW_DEPS RMW_CTRL_FAIL' DATA_RMW DEPS_RMW_FAIL).
    rewrite ct_begin. rewrite !seqA. 
    rewrite (W_ex_in_W WF). type_solver. }
  rewrite !seqA.
  sin_rewrite R_W_ex_rfi_R_Acq_in_R.
  sin_rewrite W_ex_rfi_R_Acq_ct_step.
  arewrite_id ⦗R ∩₁ Acq⦘. rewrite seq_id_r.
  arewrite (rfi ⊆ sb).
  assert ((ppo ∪ ctrli ∪ detour)⁺ ⊆ sb) as AA.
  { rewrite (ctrli_in_sb WF), detour_in_sb. 
    rewrite (ppo_in_sb WF).
    generalize (@sb_trans G). relsf. }
  arewrite ((ppo ∪ ctrli ∪ detour)＊ ⊆ sb^?).
  { rewrite rtE. rewrite AA. basic_solver. }
  rewrite ct_begin.
  rewrite !seqA.
  arewrite (sb ⨾ ((ppo ∪ ctrli ∪ detour)⁺ ⨾ ⦗W_ex⦘ ⨾ sb)＊ ⨾ sb^? ⊆ sb).
  { rewrite AA. arewrite (sb ⨾ ⦗W_ex⦘ ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). basic_solver 20. }
    relsf. rewrite <- ct_begin.
    generalize (@sb_trans G). relsf. }
  rewrite ct_end, !seqA.
  arewrite (⦗W⦘ ⊆ ⦗W⦘ ;; ⦗W⦘).
  { basic_solver. }
  sin_rewrite ppo_ctrli_detour_seq_W_ex_sb_W_in_ppo_ctrli_detour.
  arewrite ((ppo ∪ ctrli ∪ detour)＊ ⨾ (ppo ∪ ctrli ∪ detour) ⊆ (ppo ∪ ctrli ∪ detour)⁺).
  rewrite (ppo_alt WF RMW_DEPS RMW_CTRL_FAIL' DATA_RMW DEPS_RMW_FAIL).
  rewrite !(r_deps_rfi WF).
  arewrite (W ⊆₁ RW).
  rewrite (r_ct_ppo_detour_ppo WF); vauto.
- rewrite (ppo_alt WF RMW_DEPS RMW_CTRL_FAIL' DATA_RMW DEPS_RMW_FAIL).
  rewrite !(r_deps_rfi WF).
  rewrite (Power_ppo.ppo_in_sb WF), (ctrli_in_sb WF), detour_in_sb.
  arewrite (⦗W_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ sb) by basic_solver.
  rels.
  rewrite ct_end.
  arewrite_id ⦗F^lwsync⦘ at 1.
  rels.
  arewrite (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ sb).
  { arewrite (rfi ⊆ sb). basic_solver. }
  generalize (@sb_trans G); ins; relsf.
  case_refl _; [type_solver 21|].
  case_refl _; [type_solver 21|].
  arewrite (W ⊆₁ RW).
  rewrite (@R_sb_F_sb_RW_in_fence G).
  vauto.
Qed.

Lemma C_EXT: acyc_ext G.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
apply (acyc_ext_helper WF).
unfold ar_int.
arewrite (⦗W_ex ∩₁ (fun a : actid => is_xacq lab a)⦘ ⊆ ⦗W_ex⦘) by basic_solver.
rewrite C_EXT_helper1.
arewrite (rfe ⊆ hbp).
rewrite !unionA; rels.
apply acyc_psc_hbp.
Qed.

Lemma IMM_consistent : imm_consistent G.
Proof using CON DATA_RMW DEPS_RMW_FAIL NO_W_REL RMW_CTRL_FAIL RMW_DEPS R_ACQ_SB SC_F.
  cdes CON.
  assert (acyc_ext G) as AC by apply C_EXT.
  red; splits; eauto.
  { apply COH. }
  rewrite psc_base_in_psc_f; auto.
  rewrite unionK.
  arewrite (psc_f G ⊆ (ar G)⁺).
  2: { red. by rewrite ct_of_ct. }
  unfold psc_f, imm.psc. rewrite crE.
  rewrite !seq_union_l, !seq_union_r, seq_id_l, !seqA.
  unionL.
  { by apply f_sc_hb_f_sc_in_ar. }
  arewrite (⦗F^sync⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F^sync⦘ ⊆ psc).
  rewrite <- ct_step. unfold ar. eauto with hahn.
Qed.

End immToPower.
