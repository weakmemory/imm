(******************************************************************************)
(** * Compilation correctness from the IMM memory model to the TSO model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import TSO.
Require Import imm_common.
Require Import imm_hb.
Require Import imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section immToTSO.

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
Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).
Notation "'rs'" := G.(rs).
Notation "'hb'" := G.(hb).
Notation "'ppo'" := G.(ppo).
Notation "'psc'" := G.(psc).
Notation "'psc_f'" := G.(psc_f).
Notation "'psc_base'" := G.(psc_base).
Notation "'scb'" := G.(scb).
Notation "'bob'" := G.(bob).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* tso *)
Notation "'ppot'" := G.(TSO.ppo).
Notation "'fence'" := G.(fence).
Notation "'implied_fence'" := G.(implied_fence).
Notation "'hbt'" := G.(TSO.hb).
Notation "'MFENCE'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

Hypothesis CON: TSOConsistent G.

Lemma WF : Wf G.
Proof. apply CON. Qed.

(******************************************************************************)
(** * coherence   *)
(******************************************************************************)

Lemma release_in : release ⊆ sb^? ⨾ ⦗W⦘ ⨾ (ppot ∪ rfe)＊.
Proof.
unfold imm_hb.release, imm_hb.rs.
arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⊆ sb^?) by basic_solver.
arewrite (⦗W⦘ ⊆ ⦗W⦘ ⨾ ⦗W⦘) at 1. 
by basic_solver.
hahn_frame; relsf; unionL.
rewrite rt_begin; rewrite TSO.ppo_alt; basic_solver 12.
rewrite (dom_r (wf_rmwD WF)).
rewrite <- !seqA.
rewrite <- rt_seq_swap.
arewrite_id ⦗W⦘ at 2; rels.
rewrite <- (rt_of_rt (ppot ∪ rfe)).
apply inclusion_rt_rt.
rewrite rfi_union_rfe; relsf; unionL.
- arewrite (rfi ⊆ sb).
  rewrite (dom_r (wf_rmwD WF)).
  rewrite (rmw_in_sb WF).
  generalize (@sb_trans G).
  rewrite rt_begin; rewrite TSO.ppo_alt; basic_solver 21.
- rewrite (wf_rfeD WF).
  rewrite (dom_r (wf_rmwD WF)).
  rewrite rt_begin.
  rewrite rt_begin.
  rewrite rt_begin.
  rewrite (rmw_in_sb WF).
  rewrite TSO.ppo_alt; basic_solver 42.
Qed.

Lemma sw_in : sw ⊆ sb ∪ sb^? ⨾ ⦗W⦘ ⨾ (ppot ∪ rfe)⁺ ⨾ ⦗R⦘ ⨾ sb^?.
Proof.
generalize (@sb_trans G); ins.
unfold imm_hb.sw.
rewrite (dom_r (wf_releaseD WF)).
rewrite release_in.
arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ sb^?) by basic_solver.
relsf; unionL.
- rewrite rtE; relsf; unionL.
by arewrite (rfi ⊆ sb); basic_solver 12.
rewrite path_ut_last at 1; relsf; unionL.
rewrite TSO.ppo_in_sb at 1.
arewrite (rfi ⊆ sb); relsf; basic_solver 21.
rewrite TSO.ppo_in_sb at 2.
rewrite (dom_r (wf_rfiD WF)); rewrite (dom_r (wf_rfeD WF)) at 2; rewrite !seqA.
arewrite (rfi ⊆ sb).
arewrite_id ⦗W⦘ at 2.
relsf.
arewrite (⦗R⦘ ⊆ ⦗R⦘ ⨾ ⦗R⦘) at 2.
basic_solver.
arewrite (⦗R⦘ ⨾ sb ⨾ ⦗R⦘ ⊆ ppot).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot ⊆ (ppot ∪ rfe)＊) at 2.
arewrite (rfe ⊆ (ppot ∪ rfe)⁺) at 2.
relsf.
- rewrite (wf_rfeD WF) at 2; rewrite !seqA.
arewrite (⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot ⊆ (ppot ∪ rfe)＊) at 2.
arewrite (rfe ⊆ (ppot ∪ rfe)⁺) at 3.
relsf.
Qed.

Lemma hb_in : hb ⊆ sb ∪ sb^? ⨾ ⦗W⦘ ⨾ (ppot ∪ rfe)⁺ ⨾ ⦗R⦘ ⨾ sb^?.
Proof.
generalize (@sb_trans G); ins.
unfold imm_hb.hb.
rewrite sw_in, <- !unionA; rels.
apply inclusion_t_ind_right.
basic_solver.

relsf; rewrite !seqA; relsf; unionL.
1,2,3: basic_solver 21.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot).
case_refl _; [type_solver| rewrite TSO.ppo_alt; basic_solver 21].
arewrite (ppot ⊆ (ppot ∪ rfe)＊) at 2.
arewrite ((ppot ∪ rfe)⁺ ⊆ (ppot ∪ rfe)＊) at 1.
relsf.
Qed.

Lemma Coherence : coherence G.
Proof.
generalize (@sb_trans G); ins.
generalize (eco_trans WF); ins.
cdes CON; unfold TSO.hb in *.
apply coherence_alt.
rewrite hb_in; relsf; unionL.
- apply sb_irr.
- rotate 2; relsf.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)＊) at 1.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); apply SC_PER_LOC.
- rewrite (wf_rfeD WF) at 2; rewrite !seqA; rotate 1.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)＊).
arewrite (rfe ⊆ (ppot ∪ rfe)＊) at 4.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); rewrite (co_in_eco); relsf.
- arewrite (co ⨾ rfe^? ⊆ co ⨾ rfe^? ⨾ ⦗RW⦘).
rewrite (dom_r (wf_rfeD WF)).
rewrite (dom_r (wf_coD WF)).
basic_solver 12.
rewrite (dom_l (wf_coD WF)).
rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
rotate 1.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)＊).
arewrite (rfe ⊆ (ppot ∪ rfe)＊) at 4.
rotate 1; relsf.
arewrite (ppot ∪ rfe ⊆ (ppot ∪ rfe ∪ co)).
arewrite (co ⊆ (ppot ∪ rfe ∪ co)＊) at 2.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); rewrite (fr_in_eco); relsf.
- arewrite (fr ⨾ rfe^? ⊆ fr ⨾ rfe^? ⨾ ⦗RW⦘).
rewrite (dom_r (wf_rfeD WF)).
rewrite (dom_r (wf_frD WF)).
basic_solver 12.
rewrite (dom_l (wf_frD WF)).
rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗R⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
rotate 1.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)＊).
arewrite (rfe ⊆ (ppot ∪ rfe)＊) at 4.
rotate 1; relsf.
arewrite (ppot ∪ rfe ⊆ (ppot ∪ rfe ∪ fr)).
arewrite (fr ⊆ (ppot ∪ rfe ∪ fr)＊) at 2.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
Qed.

Lemma hb_rel_co_acyc : acyclic (hb ∪ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ co).
Proof.
  assert (Wf G) as WF by apply CON.
  assert (coherence G) as COH by apply Coherence.
  assert (transitive hb) by apply hb_trans.
  assert (⦗W⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ hbt) as WWHB.
  { unfold TSO.hb, TSO.ppo.
    repeat unionR left.
    unfolder. ins. desf. splits; auto. intros HH. desf. type_solver. }
  assert (⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ hbt) as RWHB.
  { unfold TSO.hb, TSO.ppo.
    repeat unionR left.
    unfolder. ins. desf. splits; auto. intros HH. desf. type_solver. }
  arewrite_id ⦗Rel⦘. rewrite seq_id_l.
  apply acyclic_utt; auto.
  { by apply sb_co_trans. }
  splits.
  { apply hb_irr; auto. apply CON. }
  { by apply sb_co_irr. }
  arewrite_id ⦗F⦘. rewrite !seq_id_l.
  rewrite sb_in_hb. 
  sin_rewrite rewrite_trans_seq_cr_r; auto.
  rewrite WF.(wf_coD), <- !seqA.
  apply acyclic_seqC. rewrite !seqA.
  arewrite (⦗W⦘ ⨾ hb ⨾ ⦗W⦘ ⊆ hbt⁺).
  { rewrite hb_in. rewrite seq_union_l, seq_union_r, !seqA.
    unionL.
    { by rewrite <- ct_step. }
    arewrite (⦗W⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ hbt^?).
    { rewrite crE, seq_union_l, seq_union_r. rewrite WWHB.
      basic_solver. }
    arewrite (ppot ⊆ hbt).
    { unfold TSO.hb. eauto with hahn. }
    arewrite (rfe ⊆ hbt).
    rewrite unionK.
    arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ hbt^?).
    { rewrite crE, seq_union_l, seq_union_r. rewrite RWHB.
      basic_solver. }
      by rewrite ct_cr, cr_ct. }
  arewrite (co ⊆ hbt).
  rewrite ct_unit.
  red. rewrite ct_of_ct. apply CON.
Qed.

(******************************************************************************)
(** * global acyclicity condition   *)
(******************************************************************************)

Lemma eco_in : eco ⊆ sb ∪ hbt⁺ ⨾ sb^?.
Proof.
unfold Execution_eco.eco.
rewrite rfi_union_rfe.
arewrite (rfi ⊆ sb).
rewrite ct_begin.
rewrite rt_begin.
unfold TSO.hb.
basic_solver 40.
Qed.

Lemma psct : psc ⊆ sb ∪ sb ⨾ hbt⁺ ⨾ sb.
Proof.
generalize (@sb_trans G); ins.
unfold imm.psc.
rewrite (wf_ecoD WF), !seqA.
rewrite eco_in.
rewrite hb_in.
arewrite (ppot ∪ rfe ⊆ hbt).
unfold TSO.hb; basic_solver 12.
relsf; unionL.
1: by unionR left; basic_solver 21.
all: unionR right.
- type_solver 21.
- basic_solver 21.
- rewrite !seqA.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊) at 1.
relsf; type_solver 21.

- type_solver 21.
- rewrite !seqA.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite_id !⦗RW⦘; rels.
arewrite (⦗R⦘ ⨾ sb^? ⨾ sb ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊) at 1.
relsf; type_solver 21.
- rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊) at 1.
relsf; type_solver 21.
- rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊) at 1.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊) at 1.
relsf; type_solver 21.
Qed.

Lemma ct_pscXt X (XX : X ⊆ sb ∪ sb ⨾ hbt⁺ ⨾ sb)
      (XD : X ⊆ ⦗ MFENCE ⦘ ⨾ X ⨾ ⦗ MFENCE ⦘) : 
  (sb^? ⨾ X ⨾ sb^?)⁺ ⊆ 
       sb^? ⨾ ⦗MFENCE⦘ ⨾ (sb ∪ sb ⨾ hbt⁺ ⨾ sb) ⨾ ⦗MFENCE⦘ ⨾ sb^?.
Proof.
generalize (@sb_trans G); ins.
rewrite XD, XX.
apply inclusion_t_ind_right.
basic_solver 21.
relsf; rewrite !seqA.
unionL.
1: unionR left; basic_solver 21.
all: unionR right.
1,2: basic_solver 42.
rewrite (dom_r (wf_ct_hbD WF)) at 1.
rewrite (dom_l (wf_ct_hbD WF)) at 2.
rewrite !seqA; relsf.
arewrite_id  ⦗MFENCE⦘ at 2.
relsf.
arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt⁺ ⊆ hbt＊ ) at 1.
relsf; basic_solver 21.
Qed.

Lemma ct_psct : 
  (sb^? ⨾ psc ⨾ sb^?)⁺ ⊆ 
       sb^? ⨾ ⦗MFENCE⦘ ⨾ (sb ∪ sb ⨾ hbt⁺ ⨾ sb) ⨾ ⦗MFENCE⦘ ⨾ sb^?.
Proof. apply (ct_pscXt psct). by rewrite (@wf_pscD G) at 1. Qed.

Lemma psc_ft : psc_f ⊆ sb ∪ sb ⨾ hbt⁺ ⨾ sb.
Proof.
  unfold imm.psc_f.
  rewrite crE.
  rewrite !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  2: by apply psct.
  rewrite hb_in.
  rewrite !seq_union_l, !seq_union_r.
  unionL; [basic_solver|].
  rewrite !seqA.
  arewrite (⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗W⦘) by type_solver. 
  arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⊆ ⦗R⦘ ⨾ sb ⨾ ⦗MFENCE⦘) by type_solver. 
  unionR right.
  arewrite (ppot ∪ rfe ⊆ hbt).
  { unfold TSO.hb. basic_solver 10. }
  basic_solver 10.
Qed.

Lemma ct_psc_ft : 
  (sb^? ⨾ psc_f ⨾ sb^?)⁺ ⊆ 
       sb^? ⨾ ⦗MFENCE⦘ ⨾ (sb ∪ sb ⨾ hbt⁺ ⨾ sb) ⨾ ⦗MFENCE⦘ ⨾ sb^?.
Proof.
  apply (ct_pscXt psc_ft).
  unfold imm.psc_f. rewrite !seqA.
  basic_solver 10.
Qed.

(* Lemma psc_baset : psc_base ⊆ sb ∪ sb^? ⨾ hbt⁺ ⨾ sb^?. *)
(* Proof. *)
(*   unfold imm.psc_base. *)
(*   unfold imm.scb. *)
(*   arewrite (sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪ hb ∩ same_loc ⊆ *)
(*                hb). *)
(*   { rewrite sb_in_hb. *)
(*     generalize (@hb_trans G). *)
(*     basic_solver 10. } *)
(*   rewrite unionA. *)
(*   arewrite (co ∪ fr ⊆ ⦗RW⦘ ⨾ hbt ⨾ ⦗W⦘). *)
(*   { rewrite wf_coD; [|by apply CON]. *)
(*     rewrite wf_frD; [|by apply CON]. *)
(*     unfold TSO.hb. basic_solver 10. } *)
(*   rewrite hb_in. *)
(*   arewrite (ppot ∪ rfe ⊆ hbt). *)
(*   { unfold TSO.hb. basic_solver 10. } *)
(*   rewrite crE with (r:=⦗F⦘ ⨾ (sb ∪ sb^? ⨾ ⦗W⦘ ⨾ hbt⁺ ⨾ ⦗R⦘ ⨾ sb^?)). *)
(*   rewrite crE with (r:=(sb ∪ sb^? ⨾ ⦗W⦘ ⨾ hbt⁺ ⨾ ⦗R⦘ ⨾ sb^?) ⨾ ⦗F⦘). *)
(*   rewrite !seq_union_r, !seq_union_l, !seq_id_l, !seqA. *)
(*   rewrite !seq_union_r. *)
(*   assert (sb ⨾ sb^? ⊆ sb) as SBT1. *)
(*   { generalize (@sb_trans G). basic_solver 10. } *)
(*   sin_rewrite !SBT1. *)
(*   assert (sb ⨾ sb ⊆ sb) as SBT2. *)
(*   { generalize (@sb_trans G). basic_solver 10. } *)
(*   sin_rewrite !SBT2. *)
(*   assert (sb^? ⨾ sb ⊆ sb) as SBT3. *)
(*   { generalize (@sb_trans G). basic_solver 10. } *)
(*   sin_rewrite !SBT3. *)
(*   assert (sb^? ⨾ sb^? ⊆ sb^?) as SBT4. *)
(*   { generalize (@sb_trans G). basic_solver 10. } *)
(*   sin_rewrite !SBT4. *)
(*   assert (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ sb ⨾ ⦗W⦘) as RsbpW. *)
(*   { rewrite crE, seq_union_l, seq_union_r. *)
(*     unionL; type_solver. } *)
(*   sin_rewrite !RsbpW. *)
(*   assert (⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ hbt) as RsbW. *)
(*   { arewrite (⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot). *)
(*     2: unfold TSO.hb; basic_solver 10. *)
(*     unfold TSO.ppo. *)
(*     unfolder. ins. desf. splits; auto. *)
(*     intros HH. desf. *)
(*     type_solver. } *)
(*   sin_rewrite !RsbW. *)
(*   assert (⦗W⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ hbt^?) as WsbW. *)
(*   { rewrite crE, seq_union_l, seq_union_r. *)
(*     unionL. *)
(*     { basic_solver. } *)
(*     arewrite (⦗W⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot). *)
(*     2: unfold TSO.hb; basic_solver 10. *)
(*     unfold TSO.ppo. *)
(*     unfolder. ins. desf. splits; auto. *)
(*     intros HH. desf. *)
(*     type_solver. } *)
(*   sin_rewrite !WsbW. *)
(*   assert (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ hbt^?) as RsbRW. *)
(*   { rewrite crE, seq_union_l, seq_union_r. *)
(*     unionL. *)
(*     { basic_solver. } *)
(*     arewrite (⦗R⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ ppot). *)
(*     2: unfold TSO.hb; basic_solver 10. *)
(*     unfold TSO.ppo. *)
(*     unfolder. ins. desf; splits; auto. *)
(*     all: intros HH; desf. *)
(*     all: type_solver. } *)
(*   sin_rewrite !RsbRW. *)
(*   repeat arewrite (hbt⁺ ⨾ hbt^? ⊆ hbt⁺). *)
(*   repeat arewrite (hbt^? ⨾ hbt⁺ ⊆ hbt⁺). *)
(*   assert (hbt ⨾ hbt⁺ ⊆ hbt⁺) as HBHBT. *)
(*   { rewrite ct_step with (r:=hbt) at 1. *)
(*     apply transitiveI. apply transitive_ct. } *)
(*   sin_rewrite !HBHBT. *)
(*   sin_rewrite !ct_unit. *)
(*   sin_rewrite !ct_ct. *)
(*   unionL. *)
(*   all: basic_solver 10. *)
(* Qed. *)

Lemma C_EXT : acyc_ext G.
Proof.
  generalize (@sb_trans G); ins.
  apply (acyc_ext_helper WF).
  arewrite (rfe ⊆ hbt⁺).
  rewrite (ar_int_in_sb WF); relsf.
  arewrite (⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot).
  { rewrite TSO.ppo_alt. basic_solver 21. }
  arewrite (ppot ⊆ hbt⁺).
  { unfold TSO.hb. rewrite <- ct_step. basic_solver 12. }
  rewrite unionA; rels.
  apply acyclic_union1.
  2: { red; rels; eapply CON. }
  { red.
    rewrite ct_psct; relsf; unionL.
    { generalize sb_irr. basic_solver 21. }
    rewrite (wf_ct_hbD WF); rotate 4.
    arewrite_id ⦗MFENCE⦘ at 1.
    relsf.
    arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
    arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
    rels.
    red; rels; eapply CON. }
  rewrite ct_psct; relsf.
  rewrite !seqA.
  rewrite (dom_r (wf_ct_hbD WF)) at 2.
  rewrite (dom_l (wf_ct_hbD WF)) at 3.
  rewrite !seqA; relsf.
  arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ fence).
  case_refl _; [type_solver|vauto].
  arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
  arewrite (hbt⁺ ⊆ hbt＊ ) at 2.
  relsf.
  arewrite (sb^? ⨾ ⦗MFENCE⦘ ⨾ sb ⊆ sb^?).
  basic_solver.
  arewrite (⦗MFENCE⦘ ⨾ sb^? ⨾ hbt⁺ ⊆ ⦗MFENCE⦘ ⨾ sb ⨾ hbt⁺).
  rewrite (dom_l (wf_ct_hbD WF)) at 1; type_solver 12.
  rels.
  rewrite (wf_ct_hbD WF); rotate 1.
  arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
  case_refl _; [type_solver|vauto].
  arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
  rels.
  red; rels; eapply CON.
Qed.

Lemma wf_psc_baseD : psc_base ≡ ⦗Sc⦘ ⨾ psc_base ⨾ ⦗Sc⦘.
Proof.
  split; [|basic_solver].
  unfold imm.psc_base.
  basic_solver 42.
Qed.

Lemma wf_psc_fD : psc_f ≡ ⦗Sc⦘ ⨾ psc_f ⨾ ⦗Sc⦘.
Proof.
  split; [|basic_solver].
  unfold imm.psc_f.
  basic_solver 42.
Qed.

Definition ehbt := 
  hbt ∪ sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb.

Lemma ehbt_ac : acyclic ehbt.
Proof.
  unfold ehbt.
  rewrite unionA.
  rewrite unionC.
  apply acyclic_union.
  { arewrite (sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb ⊆ sb).
    apply trans_irr_acyclic.
    { apply sb_irr. }
    apply sb_trans. }
  rewrite WF.(wf_hbD). rewrite !seqA.
  apply acyclic_seqC. rewrite !seqA.
  arewrite (⦗RW⦘ ⨾ (sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb)＊ ⨾ ⦗RW⦘ ⊆
            ⦗RW⦘ ⨾ (sb ⨾ ⦗MFENCE⦘ ⨾ sb)^? ⨾ ⦗RW⦘).
  2: { arewrite (⦗RW⦘ ⨾ (sb ⨾ ⦗MFENCE⦘ ⨾ sb)^? ⨾ ⦗RW⦘ ⊆ hbt^?).
       { rewrite crE. rewrite seq_union_l, seq_union_r.
         unionL; [basic_solver|].
         rewrite crE. unionR right. rewrite !seqA.
         unfold TSO.hb, TSO.fence. eauto with hahn. }
       rewrite ct_step with (r:=hbt) at 1.
       rewrite ct_cr. red. rewrite ct_of_ct.
       apply CON. }
  rewrite rtE, crE.
  rewrite !seq_union_l, !seq_union_r. apply union_mori; [done|].
  rewrite ct_begin, !seqA.
  arewrite (⦗RW⦘ ⨾ (sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb) ⊆
            ⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘).
  { rewrite seq_union_r. unionL; [done|].
    unfolder. type_solver. }
  rewrite rtE.
  rewrite !seq_union_l, !seq_union_r, seq_id_l.
  arewrite (⦗MFENCE⦘ ⨾ ⦗RW⦘ ⊆ ∅₂).
  { unfolder. type_solver. }
  unionL; [basic_solver|].
  rewrite ct_end, !seqA.
  arewrite ((sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb) ⨾ ⦗RW⦘ ⊆ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘).
  { rewrite seq_union_l, !seqA. unionL; [|done].
    unfolder. type_solver. }
  arewrite (sb ⨾ ⦗MFENCE⦘ ∪ ⦗MFENCE⦘ ⨾ sb ⊆ sb).
  arewrite (sb＊ ⨾ ⦗MFENCE⦘ ⨾ sb ⊆ sb).
  2: done.
  arewrite_id ⦗MFENCE⦘. rewrite seq_id_l.
  rewrite <- ct_end. apply ct_of_trans.
  apply sb_trans.
Qed.

Lemma fsc_hb_rw_in_ehbt : ⦗MFENCE⦘ ⨾ hb ⨾ ⦗RW⦘ ⊆ ehbt⁺.
Proof.
  assert (ppot ∪ rfe ⊆ hbt) as EE.
  { unfold TSO.hb. unionL; eauto 10 with hahn. }
  assert (⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗MFENCE⦘ ⨾ sb) as AA
    by type_solver 10.
  assert (⦗R⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⊆ sb ⨾ ⦗MFENCE⦘) as BB
    by type_solver 10.
  rewrite hb_in.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite <- ct_step.
    unfold ehbt. eauto with hahn hahn_full. }
  rewrite !seqA. sin_rewrite AA.
  arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ hbt^?).
  { rewrite !crE.
    rewrite !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver|].
    unfold TSO.hb. repeat (unionR left).
    unfold TSO.ppo. unfolder. ins. desf.
    all: splits; auto; intros HH; desf.
    all: type_solver. }
  arewrite (⦗MFENCE⦘ ⨾ sb ⊆ ehbt).
  rewrite EE.
  arewrite (hbt ⊆ ehbt).
  rewrite ct_cr.
  rewrite ct_step with (r:=ehbt) at 1.
  apply ct_ct.
Qed.

Lemma rw_hb_fsc_in_ehbt : ⦗RW⦘ ⨾ hb ⨾ ⦗MFENCE⦘ ⊆ ehbt⁺.
Proof.
  assert (ppot ∪ rfe ⊆ hbt) as EE.
  { unfold TSO.hb. unionL; eauto 10 with hahn. }
  assert (⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗MFENCE⦘ ⨾ sb) as AA
    by type_solver 10.
  assert (⦗R⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⊆ sb ⨾ ⦗MFENCE⦘) as BB
    by type_solver 10.
  rewrite hb_in.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { arewrite (sb ⨾ ⦗MFENCE⦘ ⊆ ehbt).
    rewrite <- ct_step. basic_solver. }
  arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ hbt^?).
  { rewrite !crE.
    rewrite !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver|].
    arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot).
    2: { unfold TSO.hb. eauto with hahn. }
    unfold TSO.ppo.
    unfolder. ins. desf.
    all: splits; auto.
    all: intros HH; type_solver. }
  rewrite EE. sin_rewrite BB.
  arewrite (sb ⨾ ⦗MFENCE⦘ ⊆ ehbt).
  arewrite (hbt ⊆ ehbt).
  rewrite ct_unit.
  apply cr_ct.
Qed.

Lemma fsc_hb_fsc_in_ehbt : ⦗MFENCE⦘ ⨾ hb ⨾ ⦗MFENCE⦘ ⊆ ehbt⁺.
Proof.
  assert (ppot ∪ rfe ⊆ hbt) as EE.
  { unfold TSO.hb. unionL; eauto 10 with hahn. }
  assert (⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗MFENCE⦘ ⨾ sb) as AA
    by type_solver 10.
  assert (⦗R⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⊆ sb ⨾ ⦗MFENCE⦘) as BB
    by type_solver 10.
  rewrite hb_in.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { arewrite (sb ⨾ ⦗MFENCE⦘ ⊆ ehbt).
    rewrite <- ct_step. basic_solver. }
  sin_rewrite AA. sin_rewrite BB.
  arewrite (sb ⨾ ⦗MFENCE⦘ ⊆ ehbt).
  arewrite (⦗MFENCE⦘ ⨾ sb ⊆ ehbt).
  rewrite EE.
  arewrite (hbt ⊆ ehbt).
  rewrite ct_unit.
  arewrite (ehbt ⊆ ehbt⁺).
  apply ct_ct.
Qed.

Lemma psc_f_in_ehbt : psc_f ⊆ ehbt⁺.
Proof.
  assert (ppot ∪ rfe ⊆ hbt) as EE.
  { unfold TSO.hb. unionL; eauto 10 with hahn. }
  assert (⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ⦗MFENCE⦘ ⨾ sb) as AA
    by type_solver 10.
  assert (⦗R⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⊆ sb ⨾ ⦗MFENCE⦘) as BB
    by type_solver 10.
  assert (hbt ⨾ ⦗RW⦘ ⊆ (hbt ⨾ ⦗RW⦘)＊) as FF.
  { red. ins. apply rt_step; eauto. }
  unfold imm.psc_f.
  rewrite crE.
  rewrite !seq_union_l, !seq_union_r, seq_id_l, !seqA.
  unionL.
  { apply fsc_hb_fsc_in_ehbt. }
  rewrite (dom_l WF.(wf_ecoD)). rewrite !seqA.
  sin_rewrite fsc_hb_rw_in_ehbt.
  arewrite (eco ⊆ (hbt)＊ ⨾ ⦗ RW ⦘ ⨾ rfi^?).
  { rewrite WF.(eco_alt).
    rewrite (dom_r WF.(wf_coD)).
    rewrite (dom_r WF.(wf_frD)).
    arewrite (co ⊆ hbt).
    arewrite (fr ⊆ hbt).
    rewrite !unionK.
    rewrite rfi_union_rfe.
    rewrite (dom_r WF.(wf_rfeD)).
    arewrite (rfe ⊆ hbt).
    rewrite seq_union_r.
    unionL.
    { arewrite (hbt ⊆ hbt＊). basic_solver 10. }
    2: { arewrite_id ⦗W⦘. rewrite seq_id_r.
         arewrite (hbt ⊆ hbt＊) at 2.
         arewrite (hbt^? ⨾ hbt＊ ⊆ hbt＊).
         basic_solver 10. }
    arewrite_id ⦗W⦘. rewrite seq_id_r.
    arewrite (hbt^? ⊆ hbt＊).
    rewrite (dom_l WF.(wf_rfiD)).
    basic_solver 10. }
  arewrite (rfi^? ⊆ sb^?).
  rewrite sb_in_hb.
  sin_rewrite rewrite_trans_seq_cr_l.
  2: { unfold imm_hb.hb. apply transitive_ct. }
  rewrite rw_hb_fsc_in_ehbt.
  arewrite (hbt ⊆ ehbt).
  rewrite rt_ct. apply ct_ct.
Qed.

Lemma sc_hb_fsc_in_ehbt : ⦗Sc⦘ ⨾ hb ⨾ ⦗MFENCE⦘ ⊆ ehbt⁺.
Proof.
  arewrite (hb ⊆ ⦗F ∪₁ RW⦘ ⨾ hb) by type_solver 10.
  rewrite id_union, !seq_union_l, !seq_union_r.
  arewrite (⦗Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗MFENCE⦘) by basic_solver.
  rewrite fsc_hb_fsc_in_ehbt.
  rewrite rw_hb_fsc_in_ehbt.
  basic_solver.
Qed.

Lemma fsc_hb_sc_in_ehbt : ⦗MFENCE⦘ ⨾ hb ⨾ ⦗Sc⦘ ⊆ ehbt⁺.
Proof.
  arewrite (hb ⊆ hb ⨾ ⦗F ∪₁ RW⦘) by type_solver 10.
  rewrite id_union, !seq_union_l, !seq_union_r.
  arewrite (⦗F⦘ ⨾ ⦗Sc⦘ ⊆ ⦗MFENCE⦘) by basic_solver.
  rewrite fsc_hb_fsc_in_ehbt.
  sin_rewrite fsc_hb_rw_in_ehbt.
  basic_solver.
Qed.

Lemma ppot_in_ehbt : ppot ⊆ ehbt.
Proof.
  arewrite (ppot ⊆ hbt).
  { unfold TSO.hb. eauto with hahn. }
  unfold ehbt. basic_solver.
Qed.

Lemma psc_base_in_ehbt
      (SCF : ⦗ W∩₁Sc ⦘ ⨾ sb ⨾ ⦗ R∩₁Sc⦘ ⊆
                sb ⨾ ⦗MFENCE⦘ ⨾ sb) :
  psc_base ⊆ ehbt⁺.
Proof.
  assert (⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘ ⊆ ehbt⁺) as SCSB.
  { arewrite (sb ⊆ ⦗F ∪₁ RW⦘ ⨾ sb) by type_solver 10.
    rewrite id_union.
    rewrite !seq_union_l, !seq_union_r.
    arewrite (⦗Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗MFENCE⦘) by basic_solver.
    unionL.
    { rewrite <- ct_step. unfold ehbt. basic_solver. }
    arewrite (sb ⊆ sb ⨾ ⦗F ∪₁ RW⦘) by type_solver 10.
    rewrite id_union with (s:=F).
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { rewrite <- ct_step. unfold ehbt. basic_solver 10. }
    arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ ppot ∪ ⦗W⦘ ⨾ sb ⨾ ⦗R⦘).
    { unfold TSO.ppo.
      unfolder. ins. desf.
      2: { right. splits; auto. }
      all: left; splits; auto.
      all: intros HH; type_solver 10. }
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { rewrite ppot_in_ehbt. rewrite <- ct_step.
      basic_solver. }
    rewrite !seqA.
    arewrite (⦗Sc⦘ ⨾ ⦗W⦘ ⊆ ⦗W∩₁Sc⦘) by basic_solver.
    arewrite (⦗R⦘ ⨾ ⦗Sc⦘ ⊆ ⦗R∩₁Sc⦘) by basic_solver.
    rewrite SCF.
    rewrite <- seq_eqvK, !seqA.
    arewrite (sb ⨾ ⦗MFENCE⦘ ⊆ ehbt⁺).
    arewrite (⦗MFENCE⦘ ⨾ sb ⊆ ehbt⁺).
    apply ct_ct. }
  
  assert (⦗Sc⦘ ⨾ hb ⨾ ⦗Sc⦘ ⊆ ehbt⁺) as SCHB.
  { rewrite hb_in.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    unionL; auto.
    arewrite (⦗Sc⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ehbt^?).
    { rewrite !crE.
      rewrite !seq_union_l, !seq_union_r.
      apply union_mori; [basic_solver|].
      arewrite (sb ⊆ ⦗F ∪₁ RW⦘ ⨾ sb) by type_solver 10.
      rewrite id_union.
      rewrite !seq_union_l, !seq_union_r.
      arewrite (⦗Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗MFENCE⦘) by basic_solver.
      unionL.
      { unfold ehbt. basic_solver. }
      arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot).
      2: rewrite ppot_in_ehbt; basic_solver.
      unfold TSO.ppo. unfolder. ins. desf; splits; auto.
      all: intros HH; type_solver 10. }
    arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗Sc⦘ ⊆ ehbt^?).
    { rewrite !crE.
      rewrite !seq_union_l, !seq_union_r.
      apply union_mori; [basic_solver|].
      arewrite (sb ⊆ sb ⨾ ⦗F ∪₁ RW⦘) by type_solver 10.
      rewrite id_union.
      rewrite !seq_union_l, !seq_union_r.
      arewrite (⦗F⦘ ⨾ ⦗Sc⦘ ⊆ ⦗MFENCE⦘) by basic_solver.
      unionL.
      { unfold ehbt. basic_solver 10. }
      arewrite (⦗R⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ ppot).
      2: rewrite ppot_in_ehbt; basic_solver.
      unfold TSO.ppo. unfolder. ins. desf; splits; auto.
      all: intros HH; type_solver 10. }
    arewrite (ppot ∪ rfe ⊆ ehbt).
    { unfold ehbt, TSO.hb. eauto 10 with hahn. }
    rewrite ct_cr. by rewrite cr_ct. }
  assert (hb ⨾ hb ⨾ hb ⊆ hb) as HBA.
  { generalize (@hb_trans G). basic_solver. }
  assert (scb ⊆ hb ∪ co ∪ fr) as HBB.
  { unfold imm.scb.
    arewrite (sb \ same_loc ⊆ sb).
    rewrite sb_in_hb.
    rewrite HBA.
    unionL; eauto with hahn. }
  assert (scb ⊆ hb ∪ eco) as HBECO.
  { rewrite HBB. rewrite co_in_eco, fr_in_eco. eauto with hahn. }
  unfold imm.psc_base.
  rewrite !crE.
  rewrite !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  assert (⦗Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗MFENCE⦘) as SCFM by basic_solver.
  sin_rewrite !SCFM.
  assert (⦗F⦘ ⨾ ⦗Sc⦘ ⊆ ⦗MFENCE⦘) as FSC by basic_solver.
  sin_rewrite !FSC.
  unionL.
  4: { rewrite HBECO.
       arewrite (hb ⨾ (hb ∪ eco) ⨾ hb ⊆ hb ⨾ (eco ⨾ hb)^?).
       { rewrite !seq_union_l, !seq_union_r.
         rewrite HBA. basic_solver 10. }
       apply psc_f_in_ehbt. }
  { unfold imm.scb.
    rewrite !seq_union_l, !seq_union_r.
    unionL; auto.
    { arewrite (sb \ same_loc ⊆ sb).
      rewrite sb_in_hb. sin_rewrite HBA. auto. }
    { by arewrite (hb ∩ same_loc ⊆ hb). }
    arewrite (co ⊆ hbt).
    2: arewrite (fr ⊆ hbt). 
    all: arewrite (hbt ⊆ ehbt); rewrite <- ct_step; basic_solver. }
  { rewrite HBB.
    rewrite unionA.
    arewrite (co ∪ fr ⊆ hbt ⨾ ⦗ W ⦘).
    { rewrite (dom_r WF.(wf_coD)).
      rewrite (dom_r WF.(wf_frD)).
      arewrite (co ⊆ hbt).
      arewrite (fr ⊆ hbt). eauto with hahn. }
    rewrite !seq_union_l, !seq_union_r, !seqA.
    arewrite (hb ⨾ hb ⊆ hb).
    unionL.
    { apply sc_hb_fsc_in_ehbt. }
    arewrite (W ⊆₁ RW) at 1.
    rewrite rw_hb_fsc_in_ehbt.
    arewrite (hbt ⊆ ehbt⁺).
    rewrite ct_ct. basic_solver. }
  rewrite HBB.
  rewrite unionA.
  arewrite (co ∪ fr ⊆ ⦗ RW ⦘ ⨾ hbt).
  { rewrite (dom_l WF.(wf_coD)).
    rewrite (dom_l WF.(wf_frD)).
    arewrite (co ⊆ hbt).
    arewrite (fr ⊆ hbt). basic_solver. }
  rewrite !seq_union_l, !seq_union_r, !seqA.
  arewrite (hb ⨾ hb ⊆ hb).
  unionL.
  { apply fsc_hb_sc_in_ehbt. }
  sin_rewrite fsc_hb_rw_in_ehbt.
  arewrite (hbt ⊆ ehbt⁺).
  sin_rewrite ct_ct. basic_solver.
Qed.

Lemma C_SC (SCF : ⦗ W∩₁Sc ⦘ ⨾ sb ⨾ ⦗ R∩₁Sc⦘ ⊆
                  sb ⨾ ⦗MFENCE⦘ ⨾ sb) :
  acyclic (psc_f ∪ psc_base).
Proof.
  rewrite psc_f_in_ehbt.
  rewrite psc_base_in_ehbt; auto.
  rewrite unionK.
  red. rewrite ct_of_ct.
  apply ehbt_ac.
Qed.

(******************************************************************************)
(** * Final corollary   *)
(******************************************************************************)

Lemma IMM_consistent
      (SCF : ⦗ W∩₁Sc ⦘ ⨾ sb ⨾ ⦗ R∩₁Sc⦘ ⊆ sb ⨾ ⦗MFENCE⦘ ⨾ sb):
  imm_consistent G.
Proof.
cdes CON.
red; splits; eauto.
apply Coherence.
apply C_EXT.
by apply C_SC.
Qed.

End immToTSO.
