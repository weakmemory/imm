(******************************************************************************)
(** * Weakening redundant release writes in IMM *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events Execution Execution_eco.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm.

Set Implicit Arguments.

Section Rel_opt.

Variable G : execution.

Definition relax_release_labels (l: label) : label :=
  match l with
  | Astore xm Orel x v => Astore xm Orlx x v
  | Astore xm Oacqrel x v => Astore xm Orlx x v
  | Astore xm Osc x v => Astore xm Orlx x v
  | _ => l
  end.

Definition G' : execution :=
  {|  acts_set   := (acts_set G);
      lab    := (fun a => relax_release_labels ((lab G) a));
      rmw    := (rmw G);
      data   := (data G);
      addr   := (addr G);
      ctrl   := (ctrl G);
      rmw_dep := (rmw_dep G);
      rf     := (rf G);
      co     := (co G)
  |}.

Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'deps''" := (deps G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'fre''" := (fre G').
Notation "'rfe''" := (rfe G').
Notation "'coe''" := (coe G').
Notation "'rfi''" := (rfi G').
Notation "'fri''" := (fri G').
Notation "'coi''" := (coi G').
Notation "'fr''" := (fr G').
Notation "'eco''" := (eco G').
Notation "'detour''" := (detour G').

Notation "'R''" := (fun a => is_true (is_r lab' a)).
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'F''" := (fun a => is_true (is_f lab' a)).
Notation "'R_ex''" := (fun a => is_true (R_ex lab' a)).
Notation "'RW''" := (R' ∪₁ W').
Notation "'FR''" := (F' ∪₁ R').
Notation "'FW''" := (F' ∪₁ W').
Notation "'W_ex''" := (W_ex G').
Notation "'W_ex_acq''" := (W_ex' ∩₁ (fun a => is_true (is_xacq lab' a))).

Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'mod''" := (mod lab').
Notation "'same_loc''" := (same_loc lab').

Notation "'sw''" := (sw G').
Notation "'release''" := (release G').
Notation "'rs''" := (rs G').
Notation "'hb''" := (hb G').
Notation "'sprop''" := (sprop G').
Notation "'ppo''" := (ppo G').
Notation "'psc''" := (psc G').
Notation "'psc_f''" := (psc_f G').
Notation "'psc_base''" := (psc_base G').
Notation "'bob''" := (bob G').

Notation "'Pln''" := (fun a => is_true (is_only_pln lab' a)).
Notation "'Rlx''" := (fun a => is_true (is_rlx lab' a)).
Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).
Notation "'Acqrel''" := (fun a => is_true (is_acqrel lab' a)).
Notation "'Acq/Rel''" := (fun a => is_true (is_ra lab' a)).
Notation "'Sc''" := (fun a => is_true (is_sc lab' a)).

Implicit Type WFp : Wf G'.
Implicit Type COMPp : complete G'.
Implicit Type COHp : coherence G'.
Implicit Type SC_PER_LOCp : sc_per_loc G'.

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
Notation "'detour'" := (detour G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'sw'" := (sw G).
Notation "'release'" := (release G).
Notation "'rs'" := (rs G).
Notation "'hb'" := (hb G).
Notation "'sprop'" := (sprop G).
Notation "'ppo'" := (ppo G).
Notation "'psc'" := (psc G).
Notation "'psc_f'" := (psc_f G).
Notation "'psc_base'" := (psc_base G).
Notation "'bob'" := (bob G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type COH : coherence G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Hypothesis SC_F : Sc ⊆₁ F∩₁Sc.
Hypothesis W_REL : sb ⨾ ⦗W∩₁Rel⦘ ⊆ sb^? ⨾ ⦗F∩₁Rel⦘ ⨾ sb ∪ rmw.

Lemma non_rmw_w_rel : (sb \ rmw) ⨾ ⦗W ∩₁ Rel⦘ ⊆ sb^? ⨾ ⦗F∩₁Rel⦘ ⨾ sb.
Proof using W_REL.
unfolder; ins; desc.
assert( (sb^? ⨾ ⦗F∩₁Rel⦘ ⨾ sb ∪ rmw) x y).
apply W_REL; basic_solver.
clear W_REL.
unfolder in *; desf; eauto 10.
Qed.


Lemma Rel_eq : Rel' ≡₁  Rel \₁ W∩₁Rel.
Proof using. 
unfold G', relax_release_labels, is_rel, is_w, Events.mod; ins.
unfolder; splits; ins; desf.
all: try (split; eauto; intro; desf; eauto).
all: tauto.
Qed.

Lemma F_eq : F' ≡₁ F.
Proof using SC_F W_REL. unfold G', relax_release_labels; type_solver 22. Qed.
Lemma W_eq : W' ≡₁ W.
Proof using SC_F W_REL. unfold G', relax_release_labels; type_solver 22. Qed.
Lemma W_ex_acq_eq : W_ex_acq' ≡₁ W_ex_acq.
Proof using SC_F W_REL.
  unfold G', relax_release_labels.
  unfold Execution.W_ex; mode_unfolder; ins; unfold xmod; basic_solver 22.
Qed.
Lemma R_ex_eq : R_ex' ≡₁ R_ex.
Proof using SC_F W_REL. unfold G', relax_release_labels; type_solver. Qed.
Lemma R_eq : R' ≡₁ R.
Proof using SC_F W_REL. unfold G', relax_release_labels; type_solver 22. Qed.
Lemma R_Acq_eq: R ∩₁ Acq' ≡₁ R ∩₁ Acq.
Proof using.
  unfold G', relax_release_labels; ins.
  unfolder; ins; split; ins; desf; splits; eauto.
  all: type_unfolder; mode_unfolder; unfold Events.mod in *.
  all: by destruct (lab x); eauto; exfalso.
Qed.

Lemma FR_Acq_eq: FR ∩₁ Acq' ≡₁ FR ∩₁ Acq.
Proof using.
  unfold G', relax_release_labels; ins.
  all: unfolder; ins; split; ins; desf; splits; eauto.
  all: type_unfolder; mode_unfolder; unfold Events.mod in *.
  all: by destruct (lab x); eauto; exfalso.
Qed.

Lemma F_AcqRel_eq : F ∩₁ Acq/Rel' ≡₁  F ∩₁ Acq/Rel.
Proof using.
  unfold G', relax_release_labels, is_f, is_ra, is_rel, is_acq, Events.mod; ins.
  unfolder; ins; split; ins; desf; splits; eauto.
Qed.

Lemma F_Rel_eq : F'∩₁Rel' ≡₁ F∩₁Rel.
Proof using SC_F W_REL.
  rewrite Rel_eq. rewrite F_eq.
  split; [basic_solver|].
  unfolder. ins. desf. splits; auto. intros HH. type_solver.
Qed.

Lemma FR_Rel_eq : FR'∩₁Rel' ≡₁ FR∩₁Rel.
Proof using SC_F W_REL.
  rewrite Rel_eq. rewrite F_eq, R_eq.
  split; [basic_solver|].
  unfolder. ins. desf; splits; auto.
  all: intros HH; type_solver.
Qed.

Lemma F_Sc_eq : F'∩₁Sc' ≡₁  F∩₁Sc.
Proof using.
  unfold G', relax_release_labels, is_f, is_sc, Events.mod; ins.
  unfolder; ins; split; ins; desf; splits; eauto.
Qed.

Lemma Acq_or_W_eq : Acq'∪₁W' ≡₁ Acq∪₁W.
Proof using SC_F W_REL.
  arewrite (Acq'∪₁W' ≡₁ (FR'∩₁Acq')∪₁W').
  { split; [|basic_solver].
    unionL; [|eauto with hahn].
    type_solver 10. }
  arewrite (Acq∪₁W ≡₁ (FR∩₁Acq)∪₁W).
  { split; [|basic_solver].
    unionL; [|eauto with hahn].
    type_solver 10. }
  rewrite <- FR_Acq_eq, <- R_eq, <- F_eq, <- W_eq.
  done.
Qed.

Lemma same_loc_eq : same_loc' ≡ same_loc.
Proof using. unfold G', relax_release_labels, Events.same_loc, Events.loc; ins.
type_solver 22.
Qed.
Lemma E_eq : E' ≡₁ E.
Proof using. unfold G'; unfold acts_set; ins; basic_solver. Qed.
Lemma sb_eq : sb' ≡ sb.
Proof using. by unfold G'; ins. Qed.
Lemma rf_eq : rf' ≡ rf.
Proof using. by unfold G'; ins. Qed.
Lemma rmw_eq : rmw' ≡ rmw.
Proof using. by unfold G'; ins. Qed.
Lemma co_eq : co' ≡ co.
Proof using. by unfold G'; ins. Qed.
Lemma fr_eq : fr' ≡ fr.
Proof using. by unfold G'; ins. Qed.
Lemma eco_eq : eco' ≡ eco.
Proof using. by unfold G'; ins. Qed.
Lemma data_eq : data' ≡ data.
Proof using. by unfold G'; ins. Qed.
Lemma addr_eq : addr' ≡ addr.
Proof using. by unfold G'; ins. Qed.
Lemma ctrl_eq : ctrl' ≡ ctrl.
Proof using. by unfold G'; ins. Qed.
Lemma rfe_eq : rfe' ≡ rfe.
Proof using. by unfold G'; ins. Qed.
Lemma rfi_eq : rfi' ≡ rfi.
Proof using. by unfold G'; ins. Qed.
Lemma W_ex_eq : W_ex' ≡₁ W_ex.
Proof using. unfold G', relax_release_labels; type_solver 22. Qed.

Lemma bob_eq : bob ⊆ bob'⁺ ∪ rmw' ∪ ⦗W ∩₁ Rel⦘ ⨾ sb' ∩ same_loc' ⨾ ⦗W'⦘.
Proof using SC_F W_REL.
unfold imm_bob.bob, imm_bob.fwbob.
rewrite F_eq, R_eq, W_eq, Rel_eq, sb_eq, F_AcqRel_eq, R_Acq_eq, same_loc_eq.
unionL.
- rewrite W_REL; unionL.
* arewrite (⦗F ∩₁ Rel⦘ ⊆ ⦗F ∩₁ Acq/Rel⦘) by mode_solver.
case_refl _.
by unionR left -> left; unfolder; econs; eauto.
unionR left -> left.
unfolder; ins; desf; eapply t_trans; eapply t_step; eauto 20.
*
rewrite rmw_eq; basic_solver.
- basic_solver 12.
- unionR left -> left; unfolder; ins; eapply t_step; basic_solver 12.
- unionR left -> left; unfolder; ins; eapply t_step; basic_solver 12.
- unionR left -> left; unfolder; ins; eapply t_step; basic_solver 12.
Qed.

Lemma ppo_eq: ppo' ≡ ppo.
Proof using SC_F W_REL.
unfold imm_ppo.ppo, Execution.rfi.
by rewrite W_eq, R_eq, sb_eq, data_eq, addr_eq, ctrl_eq, rf_eq, R_ex_eq.
Qed.

Lemma detour_eq: detour' ≡ detour.
Proof using.
unfold Execution.detour; ie_unfolder.
by rewrite sb_eq, rf_eq, co_eq.
Qed.

Lemma rs_eq : rs' ≡ rs.
Proof using SC_F W_REL.
by unfold imm_hb.rs; rewrite W_eq, same_loc_eq, sb_eq, rf_eq, rmw_eq.
Qed.

Lemma rmw_release_eq WF WFp: rmw ⨾ release ⊆ rmw' ⨾ rs'.
Proof using SC_F W_REL.
unfold imm_hb.release.
rewrite (dom_r (wf_rmwD WF)), !seqA.
arewrite_id (⦗W⦘ ⨾ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?).
by type_solver.
rewrite rmw_eq.
rewrite rs_eq.
basic_solver.
Qed.


Lemma non_rmw_release_eq WF WFp: (sb \ rmw) ⨾ release ⊆ sb'^? ⨾ release'.
Proof using SC_F W_REL.
rewrite (dom_l (wf_releaseD WF)).
rewrite (dom_l (wf_releaseD WFp)). 

unfold imm_hb.release; rewrite sb_eq, rs_eq, F_eq, Rel_eq, W_eq.
arewrite (⦗FW ∩₁ Rel⦘ ⨾ ⦗Rel⦘ ≡ ⦗F ∩₁ Rel⦘ ∪ ⦗W ∩₁ Rel⦘) by basic_solver 12.

arewrite (⦗FW ∩₁ (Rel \₁ W ∩₁ Rel)⦘ ⨾ ⦗Rel \₁ W ∩₁ Rel⦘ ≡ ⦗F ∩₁ Rel⦘).
{
unfolder; split; ins; desf; splits; eauto.
tauto.
intro; unfold is_w, is_f in *; desf.
intro; unfold is_w, is_f in *; desf.
}

relsf.
arewrite (⦗W ∩₁ Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⊆ ⦗W ∩₁ Rel⦘) by type_solver 12.
sin_rewrite non_rmw_w_rel; basic_solver 22.
Qed.

Lemma F_release_eq WF: ⦗F⦘ ⨾ release ⊆ release'.
Proof using SC_F W_REL.
unfold imm_hb.release; rewrite sb_eq, rs_eq, F_eq, Rel_eq.
rewrite (dom_l (wf_rsD WF)).
case_refl _; [type_solver 12|].
arewrite (⦗F⦘ ⨾ ⦗Rel⦘ ⊆ ⦗Rel \₁ W ∩₁ Rel⦘).
by unfolder; ins; desf; splits; eauto; intro; desf; type_solver.
basic_solver 12.
Qed.

Lemma sw_eq_helper WF: 
  (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ 
  ⊆ (rfi' ∪ (sb' ∩ same_loc')^? ⨾ rfe') ⨾  (sb' ⨾ ⦗F'⦘)^? ⨾ ⦗Acq'⦘.
Proof using SC_F W_REL.
rewrite sb_eq, rfi_eq, rfe_eq, F_eq, same_loc_eq.
arewrite ((rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⊆ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ ⦗R⦘).
rewrite (dom_r (wf_rfeD WF)) at 1.
rewrite (dom_r (wf_rfiD WF)) at 1.
basic_solver 12.
arewrite (⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ ⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾  ⦗FR∩₁Acq⦘) by basic_solver 21.
rewrite <- FR_Acq_eq; basic_solver 42.
Qed.

Lemma F_sw_eq WF: ⦗F⦘ ⨾ sw ⊆ sw'.
Proof using SC_F W_REL.
unfold imm_hb.sw.
sin_rewrite (F_release_eq WF).
by sin_rewrite (sw_eq_helper WF).
Qed.

Lemma rmw_sw_eq WF WFp: rmw ⨾ sw ⊆ rmw' ⨾ rs' ⨾  (rfi' ∪ (sb' ∩ same_loc')^? ⨾ rfe') ⨾ (sb' ⨾ ⦗F'⦘)^? ⨾ ⦗Acq'⦘.
Proof using SC_F W_REL.
unfold imm_hb.sw.
sin_rewrite !(rmw_release_eq WF WFp).
sin_rewrite (sw_eq_helper WF).
by relsf; rewrite !seqA.
Qed.

Lemma non_rmw_sw_eq WF WFp: (sb \ rmw) ⨾ sw ⊆ sb'^? ⨾ sw'.
Proof using SC_F W_REL.
unfold imm_hb.sw.
sin_rewrite !(non_rmw_release_eq WF WFp).
sin_rewrite (sw_eq_helper WF).
by relsf; rewrite !seqA.
Qed.

Lemma hb_eq1 WF WFp: 
  hb ⊆ hb' ∪ (⦗W⦘ ∪ rmw) ⨾ sw ⨾ hb'^?.
Proof using SC_F W_REL.
unfold imm_hb.hb at 1.
apply inclusion_t_ind_left.
unionL.
- rewrite <- sb_eq.
unfold imm_hb.hb.
rewrite <- ct_step.
basic_solver.
- rewrite (dom_l (wf_swD WF)) at 1.
unfold imm_hb.hb.
rewrite <- ct_step.
generalize (F_sw_eq WF).
basic_solver 21.
- relsf; unionL.
* rewrite <- sb_eq, sb_in_hb; generalize (@hb_trans G'); basic_solver 12.
* rewrite (dom_l (wf_swD WF)) at 1.
generalize (F_sw_eq WF), (@sw_in_hb G'), (@hb_trans G'); basic_solver 12.
* 
arewrite (sb ⊆ rmw ∪ (sb \ rmw)) by unfolder; ins; tauto.
relsf; unionL.
basic_solver 12.
arewrite_id ⦗W⦘; rels.
sin_rewrite (non_rmw_sw_eq WF WFp).
rewrite sb_in_hb, sw_in_hb; generalize (@hb_trans G'); basic_solver 12.
* arewrite (sb ⨾ rmw ⊆ (sb \ rmw)).
rewrite (rmw_in_sb WF) at 1.
unfolder; ins; desc; splits.
eapply (@sb_trans G); eauto.
intro A; apply (wf_rmwi WF) in A.
by red in A; desc; eapply (A0 z).

sin_rewrite (non_rmw_sw_eq WF WFp).
rewrite sb_in_hb, sw_in_hb; generalize (@hb_trans G'); basic_solver 12.
*
 by rewrite (dom_r (wf_swD WF)) at 1; type_solver 12.
* sin_rewrite (sw_rmw_sw WF).
rewrite <- sb_eq, sb_in_hb.
rewrite (dom_l (wf_swD WF)) at 1.
generalize (F_sw_eq WF), (@sw_in_hb G'), (@hb_trans G'); basic_solver 12.
Qed.


(*
Lemma hb_eq WF WFp: 
  hb ⊆ hb' ∪ ⦗W⦘ ⨾ sw ⨾ hb'^? ∪ rmw' ⨾ rs' ⨾  (rfi' ∪ (sb' ∩ same_loc')^? ⨾ rfe') ⨾ (sb' ⨾ ⦗F'⦘)^? ⨾ ⦗Acq'⦘ ⨾ hb'^?.
Proof using.
rewrite (hb_alt2 WF), (F_sw_eq WF), (non_rmw_sw_eq WF WFp), (rmw_sw_eq WF WFp).
arewrite (sb ∪ sw' ∪ sb'^? ⨾ sw' ⊆ hb').
by rewrite <- sb_eq, sb_in_hb, sw_in_hb; unfold imm_hb.hb; relsf.
generalize (@hb_trans G'); ins; relsf; basic_solver 42.
Qed.
*)
Lemma psc_eq WF WFp SC_PER_LOC COMP COHp COMPp: 
  psc ⊆ psc'.
Proof using SC_F W_REL.
  unfold imm.psc.
  rewrite (hb_eq1 WF WFp) at 1 2.

  arewrite (⦗F ∩₁ Sc⦘ ⨾ (hb' ∪ (⦗W⦘ ∪ rmw) ⨾ sw ⨾ hb'^?) ⊆ ⦗F ∩₁ Sc⦘ ⨾ hb').
  { rewrite (dom_l (wf_rmwD WFp)). type_solver 12. }

  set (X:= ⦗W⦘ ∪ rmw).
  rewrite F_Sc_eq.
  relsf; unionL; [by rewrite eco_eq|].
  unfold X; clear X.

  (*arewrite (rfi' ∪ (sb' ∩ same_loc')^? ⨾ rfe' ⊆ (rfi' ∪ (sb' ∩ same_loc')^? ⨾ rfe') ⨾ ⦗R'⦘).
rewrite (dom_r (wf_rfiD WFp)) at 1.
rewrite (dom_r (wf_rfeD WFp)) at 1.
basic_solver 12.
   *)
  sin_rewrite !(sw_in_sb_eco_sb WF SC_PER_LOC).
  rewrite !seqA.


  arewrite ((⦗W⦘ ∪ rmw)  ⨾ (⦗F ∩₁ Rel⦘ ⨾ sb)^? ⊆ ⦗W⦘ ∪ rmw).
  { rewrite (dom_r (wf_rmwD WF)). type_solver 12. }

  arewrite ((sb ⨾ ⦗F ∩₁ Acq⦘)^? ⨾ hb'^? ⊆ hb'^?).
  rewrite <- sb_eq.
  unfold imm_hb.hb.
  arewrite (sb' ⊆ (sb' ∪ sw')) at 1; rels.

  arewrite_id ⦗F ∩₁ Acq⦘.
  relsf.

  arewrite ((⦗W⦘ ∪ rmw) ⊆ eco^?).
  { rewrite (rmw_in_fr WF SC_PER_LOC COMP), fr_in_eco. basic_solver. }

  generalize (eco_trans WF); ins; relsf.
  arewrite (eco ⨾ hb'^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ eco ⨾ hb' ⨾ ⦗F ∩₁ Sc⦘).
  2: done.
  rewrite (dom_r (wf_ecoD WF)) at 1. type_solver 12.
Qed.

Lemma psc_f_eq WF WFp SC_PER_LOC COMP COHp COMPp: 
  psc_f ⊆ psc_f'.
Proof using SC_F W_REL.
  unfold imm.psc_f at 1.
  rewrite crE.
  rewrite !seq_union_l, !seq_union_r, seq_id_l, !seqA.
  unionL.
  2: { assert (psc' ⊆ psc_f') as HH.
       2: { rewrite <- HH. by apply psc_eq. }
       unfold imm.psc_f, imm.psc.
       assert (eco' ⨾ hb' ⊆ (eco' ⨾ hb')^?) as HH.
       2: by sin_rewrite HH.
       eauto with hahn. }

  rewrite (hb_eq1 WF WFp).

  arewrite (⦗F ∩₁ Sc⦘ ⨾ (hb' ∪ (⦗W⦘ ∪ rmw) ⨾ sw ⨾ hb'^?) ⊆ ⦗F ∩₁ Sc⦘ ⨾ hb').
  { rewrite (dom_l (wf_rmwD WFp)). type_solver 12. }
  unfold imm.psc_f.
  rewrite F_Sc_eq. basic_solver 10.
Qed.

Lemma wf_eq: Wf G' -> Wf G.
Proof using SC_F W_REL.
intros WF.
destruct WF.
eexists; rewrite <- ?sb_eq, <- ?W_eq, <- ?R_eq, <- ?same_loc_eq, <- ?R_ex_eq; try done.
- clear -wf_rfv.
  unfold G', relax_release_labels, Events.val, funeq in *; intros a b H.
  apply wf_rfv in H; destruct a,b; ins; desf.
- ins.
  rewrite <- W_eq, <- E_eq.
  arewrite ((fun x : actid => loc x = ol) ⊆₁ (fun x : actid => loc' x = ol)).
  unfolder; ins.
  unfold relax_release_labels, Events.loc in *; ins; destruct x; desf.
  done.
- clear -wf_init.
  intros l B; specialize (wf_init l); desc.
  apply wf_init; eexists; splits; eauto.
  unfold G', relax_release_labels, Events.loc in *; ins; destruct b; ins; desf.
- clear -wf_init_lab.
  intros l; specialize (wf_init_lab l).
  unfold G', relax_release_labels in *; ins; desf.
Qed.

Lemma complete_eq: complete G' -> complete G.
Proof using SC_F W_REL.
by unfold complete; rewrite E_eq, R_eq, rf_eq.
Qed.

Lemma sc_per_loc_eq: sc_per_loc G' -> sc_per_loc G.
Proof using.
by unfold sc_per_loc; rewrite sb_eq, eco_eq.
Qed.

Lemma coherence_eq WF SC_PER_LOC COMP WFp COMPp: coherence G' -> coherence G.
Proof using SC_F W_REL.
unfold coherence; intro COHp.
rewrite <- eco_eq.
rewrite (hb_eq1 WF WFp), (rmw_in_fr WFp (coherence_sc_per_loc COHp) COMPp).
sin_rewrite !(sw_in_sb_eco_sb WF SC_PER_LOC).
rewrite fr_in_eco.
rewrite !seqA.
  arewrite ((sb ⨾ ⦗F ∩₁ Acq⦘)^? ⨾ hb'^? ⊆ hb'^?).
rewrite <- sb_eq, sb_in_hb; generalize (@hb_trans G'); basic_solver 12.

arewrite (((⦗W⦘ ∪ eco') ⨾ (⦗F ∩₁ Rel⦘ ⨾ sb)^? ⨾ eco ⨾ hb'^?) ⊆ (⦗W⦘ ∪ eco') ⨾ eco ⨾ hb'^?).
by rewrite (dom_r (wf_ecoD WFp)) at 1; type_solver 12.

generalize (eco_trans WFp); intro.
relsf; unionL; try done.

-
  rewrite <- !eco_eq.

rewrite !seqA.
arewrite_id ⦗W⦘.
rotate 2.
relsf.
rewrite crE at 1; relsf; apply irreflexive_union.
eauto using eco_irr.

-
rewrite !seqA.
rotate 1.

relsf.
rotate 1.
rewrite crE at 1; relsf; apply irreflexive_union.
eauto using eco_irr.
Qed.

Lemma acyc_ext_eq WF WFp SC_PER_LOC COMP COHp COMPp: acyc_ext G' -> acyc_ext G.
Proof using SC_F W_REL.
unfold acyc_ext.
intros HH.
unfold ar, ar_int in *.
rewrite (psc_eq WF WFp SC_PER_LOC COMP COHp COMPp).
rewrite <- ppo_eq.
rewrite <- rfe_eq.
rewrite <- detour_eq.
rewrite bob_eq.
rewrite <- sb_eq.
rewrite <- W_ex_acq_eq.
rewrite <- W_eq at 2.
rewrite <- rfi_eq.
rewrite <- W_ex_eq.
rewrite <- R_Acq_eq.
rewrite <- R_eq.

rewrite (rmw_in_ppo WFp) at 1.

apply acyclic_mon with (r:= psc' ∪ ppo' ∪ rfe' ∪ detour' 
 ∪ ⦗W_ex_acq'⦘ ⨾ sb' ⨾ ⦗W'⦘ ∪ ⦗W_ex'⦘ ⨾ rfi' ⨾ ⦗R' ∩₁ Acq'⦘ 
 ∪ bob'⁺ ∪ ⦗W ∩₁ Rel⦘ ⨾ sb' ∩ same_loc' ⨾ ⦗W'⦘).
2: basic_solver 30.

apply acyclic_union1.
-

red.
rewrite ct_of_union_ct_r; eapply acyclic_mon; [edone|].
basic_solver 12.
-
apply acyclic_mon with (r:=sb').
red; generalize (@sb_trans G'); ins; relsf; apply (@sb_irr G').
basic_solver.
-

arewrite (sb' ∩ same_loc' ⊆ sb').

assert (transitive (⦗W ∩₁ Rel⦘ ⨾ sb' ⨾ ⦗W'⦘)).
{
apply transitiveI; rewrite !seqA.
arewrite_id (⦗W'⦘ ⨾ ⦗W ∩₁ Rel⦘).
basic_solver.
relsf.
arewrite (sb' ⨾ sb' ⊆ sb').
apply transitiveI, (@sb_trans G').
done.
}

relsf.
rewrite ct_of_union_ct_r.



rewrite ct_end, !seqA.
arewrite ((psc' ∪ ppo' ∪ rfe' ∪ detour' ∪ 
  ⦗W_ex_acq'⦘ ⨾ sb' ⨾ ⦗W'⦘ ∪ 
  ⦗W_ex'⦘ ⨾ rfi' ⨾ ⦗R' ∩₁ Acq'⦘ ∪ bob') ⨾ ⦗W ∩₁ Rel⦘ ⊆ sb' ⨾ ⦗W ∩₁ Rel⦘).
{
relsf; unionL.
- rewrite (dom_r (@wf_pscD G')).
rewrite F_Sc_eq; type_solver 21.
- by rewrite (ppo_in_sb WFp).
- rewrite (dom_r (wf_rfeD WFp)).
rewrite R_eq; type_solver 21.
- by rewrite detour_in_sb.
- by basic_solver.
- unfold Execution.rfi; basic_solver.
- by rewrite bob_in_sb.
}

rewrite sb_eq at 1.
sin_rewrite W_REL.


rewrite <- sb_eq, <- rmw_eq.
arewrite (⦗F ∩₁ Rel⦘ ⊆ ⦗F ∩₁ Acq/Rel⦘) by mode_solver.
rewrite <- F_AcqRel_eq, <- F_eq.

arewrite ((sb'^? ⨾ ⦗F' ∩₁ Acq/Rel'⦘ ⨾ sb' ∪ rmw') ⨾ sb' ⨾ ⦗W'⦘ ⊆ (psc' ∪ ppo' ∪ rfe' ∪ detour' ∪ ⦗W_ex_acq'⦘ ⨾ sb' ⨾ ⦗W'⦘ ∪ bob')⁺).
{

relsf; unionL.

-
rewrite !seqA.
arewrite (sb' ⨾ sb' ⨾ ⦗W'⦘ ⊆ sb').
by generalize (@sb_trans G'); basic_solver.
unfold imm_bob.bob, imm_bob.fwbob.

case_refl _.
unfolder; ins; eapply t_step; basic_solver 21.

unfolder; ins; desf; eapply t_trans; eapply t_step; basic_solver 21.
- rewrite rmw_sb_W_in_ppo; auto.
by red; ins; eapply t_step; basic_solver 12.
}
arewrite (psc' ∪ ppo' ∪ rfe' ∪ detour' ∪ ⦗W_ex_acq'⦘ ⨾ sb' ⨾ ⦗W'⦘ ∪ bob' ⊆
          psc' ∪ ppo' ∪ rfe' ∪ detour' ∪ ⦗W_ex_acq'⦘ ⨾ sb' ⨾ ⦗W'⦘ ∪
          ⦗W_ex'⦘ ⨾ rfi' ⨾ ⦗R' ∩₁ Acq'⦘ ∪ bob').
relsf.

red; rels.
eapply acyclic_mon; [edone|].
basic_solver 12.
Qed.


Lemma rmw_atomicity_eq: rmw_atomicity G' -> rmw_atomicity G.
Proof using.
by unfold rmw_atomicity; rewrite rmw_eq, fr_eq, sb_eq, co_eq.
Qed.

Lemma rel_opt WFp COMPp  (CONSp: imm_consistent G'): imm_consistent G.
Proof using SC_F W_REL.
  cdes CONSp.
  assert (Wf G) as WF by (by apply wf_eq).
  assert (complete G) as COM by (by apply complete_eq).
  assert (sc_per_loc G) as SPL.
  { apply sc_per_loc_eq. by apply coherence_sc_per_loc. }
  assert (coherence G) as COH by (by apply coherence_eq).
  assert (acyc_ext G) as CextG by (by apply acyc_ext_eq).

  red. splits; auto.
  rewrite psc_base_in_psc_f; auto.
  rewrite unionK.
  rewrite psc_f_eq; auto.
  arewrite (psc_f' ⊆ psc_f' ∪ psc_base').
  done.
Qed.

End Rel_opt.
