(******************************************************************************)
(** * Definition of happens-before in the IMM memory model (similar to C11) *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.

Section IMM_hb.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).

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
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type SC_PER_LOC : sc_per_loc G.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* release sequence *)
Definition rs := ⦗W⦘ ⨾  ((sb ∩ same_loc) ⨾ ⦗W⦘ ∪ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊).

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

(* happens-before *)
Definition hb := (sb ∪ sw)⁺.

(* simplified prop *)
Definition sprop :=
  ⦗W⦘ ⨾ rfe^? ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq ∪₁ W⦘ ⨾ hb ⨾ ⦗Rel⦘.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma hb_trans : transitive hb.
Proof using. vauto. Qed.

Lemma sb_in_hb : sb ⊆ hb.
Proof using. vauto. Qed.

Lemma sw_in_hb : sw ⊆ hb.
Proof using. vauto. Qed.

Lemma cr_hb_hb : hb^? ⨾ hb ≡ hb.
Proof using. generalize hb_trans; basic_solver. Qed.

Lemma cr_hb_cr_hb : hb^? ⨾ hb^? ≡ hb^?.
Proof using. generalize hb_trans; basic_solver 20. Qed.

Lemma hb_sb_sw : hb ≡ hb^? ⨾ (sb ∪ sw).
Proof using.
unfold hb; rewrite ct_end at 1; rels.
Qed.

Lemma sprop_trans WF : transitive sprop.
Proof using.
  apply transitiveI.
  unfold sprop at 1 2. rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ rfe^? ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq ∪₁ W⦘ ⊆ hb^?).
  { rewrite crE at 1. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
    unionL.
    { rewrite sb_in_hb. basic_solver. }
    rewrite <- sw_in_hb.
    unfold sw.
    arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⊆ release).
    { unfold release, rs. 
      rewrite rtE. basic_solver 40. }
    rewrite (dom_r (wf_rfeD WF)) at 1. rewrite !seqA.
    arewrite (⦗R⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq ∪₁ W⦘ ⊆ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘).
    { unfolder. ins. desf; eauto 10.
      all: type_solver. }
    basic_solver 40. }
  arewrite (hb ⨾ hb^? ⨾ hb ⊆ hb).
  2: done.
  rewrite cr_hb_hb.
  apply transitiveI. 
  apply hb_trans.
Qed.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma loceq_rs WF : funeq loc rs.
Proof using. destruct WF; unfold rs; desf; eauto 10 with hahn. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_rsE WF : rs ≡ ⦗W⦘ ∪ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof using.
unfold rs.
split; [|basic_solver].
rewrite rtE; relsf; unionL.
rewrite wf_sbE; basic_solver 21.
basic_solver 21.
unionR right -> right -> right.
rewrite (dom_r (wf_rmwE WF)) at 1.
rewrite <- !seqA.
sin_rewrite inclusion_ct_seq_eqv_r.
rewrite !seqA.
arewrite (⦗E⦘ ⨾ ⦗W⦘ ≡ ⦗W⦘ ⨾ ⦗E⦘) by basic_solver.
hahn_frame.
rewrite ct_begin.
rewrite (dom_l (@wf_sbE G)) at 1.
rewrite (dom_l (wf_rfE WF)) at 1.
basic_solver 21.
Qed.

Lemma wf_releaseE WF : release ≡ ⦗W ∩₁ Rel⦘ ∪ ⦗E⦘ ⨾ release ⨾ ⦗E⦘.
Proof using.
unfold release.
rewrite (wf_rsE WF).
rewrite (@wf_sbE G) at 1.
basic_solver 42.
Qed.

Lemma wf_swE_right WF : sw ≡ sw ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold sw.
rewrite wf_sbE at 1 2.
rewrite (wf_rfiE WF) at 1.
rewrite (wf_rfeE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swE WF : sw ≡ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_swE_right WF) at 1.
hahn_frame.
unfold sw.
rewrite (wf_releaseE WF).
rewrite (dom_l (wf_rfiE WF)).
rewrite (dom_l (@wf_sbE G)).
rewrite (dom_l (wf_rfeE WF)).
basic_solver 40.
Qed.

Lemma wf_hbE WF : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold hb.
rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
apply inclusion_t_t.
rewrite wf_sbE at 1.
rewrite (wf_swE WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_rsD WF : rs ≡ ⦗W⦘ ⨾ rs ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold rs.
relsf; unionL; [basic_solver 12|].
rewrite rtE; relsf; unionL; [basic_solver|].
rewrite (dom_r (wf_rmwD WF)) at 1.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r.
basic_solver 42.
Qed.

Lemma wf_releaseD WF : release ≡ ⦗FW∩₁Rel⦘ ⨾ release ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold release.
rewrite (wf_rsD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swD WF : sw ≡ ⦗FW∩₁Rel⦘ ⨾ sw ⨾ ⦗FR∩₁Acq⦘.
Proof using.
split; [|basic_solver].
unfold sw.
rewrite (wf_releaseD WF) at 1.
rewrite (wf_rfiD WF) at 1.
rewrite (wf_rfeD WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma no_sw_to_init WF : sw ≡ sw ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_swD WF) at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma no_hb_to_init WF : hb ≡ hb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
split; [|basic_solver].
unfold hb.
rewrite ct_end.
rewrite (no_sw_to_init WF) at 2.
rewrite no_sb_to_init at 2.
basic_solver 42.
Qed.

(******************************************************************************)
(** more properties **   *)
(******************************************************************************)

Lemma sw_alt WF: 
  sw ≡ release ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾  ⦗R ∩₁ Acq⦘ 
     ∪ release ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾  sb ⨾ ⦗F ∩₁ Acq⦘.
Proof using.
unfold sw.
rewrite (dom_r (wf_rfiD WF)).
rewrite (dom_r (wf_rfeD WF)).
basic_solver 42.
Qed.

Lemma rel_rf_in_sw WF: release ⨾ rf ⨾ ⦗Acq⦘ ⊆ sw.
Proof using.
rewrite (wf_rfD WF), rfi_union_rfe. 
unfold sw; basic_solver 42.
Qed.

Lemma sw_in_rel_rf WF: 
  sw ⨾ ⦗R⦘ ⊆ release ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ ⦗Acq⦘.
Proof using.
unfold sw; rewrite !seqA.
arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗R⦘ ⊆ ⦗Acq⦘) by type_solver 42.
Qed.

Lemma rs_in_co WF SC_PER_LOC : rs ⊆ ⦗W⦘ ⨾ co^?.
Proof using.
unfold rs.

assert (A: ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ co^?).
{ arewrite (⦗W⦘ ⊆ ⦗W⦘ ⨾ ⦗W⦘) at 1 by basic_solver.
  rewrite crE; relsf; unionL; [basic_solver|].
  sin_rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC).
  sin_rewrite (dom_l (wf_coiD WF)).
  ie_unfolder; basic_solver. }

relsf; unionL.
arewrite (sb ∩ same_loc ⊆ (sb ∩ same_loc)^?).
by rewrite A.

rewrite rtE; relsf; unionL; [basic_solver|].
sin_rewrite !(rf_rmw_in_co WF SC_PER_LOC).
sin_rewrite (dom_r (wf_coD WF)).


arewrite (⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ co ⨾ ⦗W⦘)⁺ ⊆ (⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ co)⁺).
rewrite <- seqA.
rewrite <- ct_seq_swap.
arewrite_id ⦗W⦘ at 2.
by rels.

sin_rewrite (dom_l (wf_coD WF)).
sin_rewrite A.
rewrite !seqA.
rewrite inclusion_ct_seq_eqv_l.
generalize (co_trans WF); ins; relsf.
Qed.

Lemma rs_in_eco WF SC_PER_LOC : rs ⊆ eco^?.
Proof using.
  rewrite rs_in_co, co_in_eco; try done; basic_solver.
Qed.

Lemma rs_sb_loc WF SC_PER_LOC : rs ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ co^?.
Proof using.
  rewrite rs_in_co; auto. rewrite !seqA.
  apply co_sb_loc; auto. 
Qed.


Lemma rs_rfi WF SC_PER_LOC :
  rs ⨾ rfi ⊆ sb ∩ same_loc ⨾ ⦗R⦘ ∪ co^? ⨾ rfe ⨾ ⦗R⦘ ⨾ sb.
Proof using.
  generalize (@sb_same_loc_trans G); ins.
  assert (SB: (sb ∩ same_loc)^? ⨾ rfi ⨾ rmw ⊆ sb ∩ same_loc).
  { rewrite (rfi_in_sbloc' WF).
    arewrite (rmw ⊆ rmw ∩ rmw).
    rewrite (rmw_in_sb WF) at 1; rewrite (wf_rmwl WF).
    relsf. }
  unfold rs.
  rewrite rtE; relsf; unionL.
  { rewrite (dom_r (wf_rfiD WF)), (rfi_in_sbloc' WF).
    generalize (@sb_same_loc_trans G). basic_solver 12. }
  { rewrite (dom_r (wf_rfiD WF)); rewrite (rfi_in_sbloc' WF). basic_solver 12. }
  rewrite rfi_union_rfe; relsf.
  rewrite path_ut_last; relsf; unionL.
  { rewrite (dom_r (wf_rfiD WF)) at 2; rewrite (rfi_in_sbloc' WF) at 2.
    sin_rewrite SB. rewrite !seqA. relsf. basic_solver. }
  arewrite (⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ rfi ⨾ rmw ∪ (sb ∩ same_loc)^? ⨾ rfe ⨾ rmw)＊ ⊆ rs).
  { unfold rs. rewrite rfi_union_rfe. relsf. }
  rewrite (dom_l (wf_rfeD WF)) at 1. rewrite !seqA.
  sin_rewrite (rs_sb_loc WF SC_PER_LOC).
  rewrite (dom_l (wf_rmwD WF)).
  arewrite (rfi ⊆ sb); rewrite (rmw_in_sb WF).
  arewrite ((sb ∩ same_loc)^? ⊆ sb^?).
  arewrite_id ⦗R⦘ at 2. rewrite seq_id_l.
  arewrite (sb ⨾ (sb^? ⨾ sb ⨾ sb)＊ ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). ins. relsf. }
  eauto with hahn.
Qed.

Lemma release_in_co WF SC_PER_LOC : ⦗W⦘ ⨾ release ⊆ co^?.
Proof using.
unfold release; rewrite rs_in_co; try done.
type_solver.
Qed.

Lemma sw_in_eco_helper WF SC_PER_LOC  :
 rs ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⊆ eco.
Proof using.
rewrite (dom_l (wf_rsD WF)).
rewrite rs_in_co; try done.
arewrite (rfi ⊆ rf).
arewrite (rfe ⊆ rf).
relsf; unionL.
- rewrite co_in_eco, rf_in_eco; try done.
  generalize (eco_trans WF); type_solver 42.
- rewrite (dom_r (wf_coD WF)), (dom_l (wf_rfD WF)).
  arewrite (⦗W⦘ ⨾ (co ⨾ ⦗W⦘)^? ⊆ co^? ⨾ ⦗W⦘).
  basic_solver.
  arewrite !(⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ co^?).
  rewrite crE; relsf; unionL; [basic_solver|].
  sin_rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC).
  ie_unfolder; basic_solver.
  rewrite co_in_eco, rf_in_eco; try done.
  generalize (eco_trans WF); type_solver 42.
Qed.

Lemma sw_in_eco WF SC_PER_LOC : ⦗W⦘ ⨾ sw ⨾ ⦗R⦘ ⊆ eco.
Proof using.
unfold sw; rewrite !seqA.
unfold release; rewrite !seqA.
arewrite_id (⦗W⦘ ⨾ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?).
by type_solver.
rels.
sin_rewrite (sw_in_eco_helper WF SC_PER_LOC).
generalize (eco_trans WF); type_solver 42.
Qed.

Lemma sw_in_eco_sb WF SC_PER_LOC : ⦗W⦘ ⨾ sw ⨾ ⦗F⦘ ⊆ eco ⨾ sb ⨾ ⦗F⦘.
Proof using.
unfold sw; rewrite !seqA.
unfold release; rewrite !seqA.
arewrite_id (⦗W⦘ ⨾ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?).
by type_solver.
rels.
sin_rewrite (sw_in_eco_helper WF SC_PER_LOC).
rewrite (wf_ecoD WF) at 1.
generalize (eco_trans WF); type_solver 42.
Qed.

Lemma sw_in_sb_eco_sb WF SC_PER_LOC :
    sw ⊆ (⦗F ∩₁ Rel⦘ ⨾ sb)^? ⨾ eco ⨾ (sb ⨾ ⦗F ∩₁ Acq⦘)^?.
Proof using.
unfold sw.
unfold release; rewrite !seqA.
sin_rewrite sw_in_eco_helper; try done.
basic_solver 42.
Qed.

Lemma eco_sw_helper WF SC_PER_LOC 
  x y z (ECO: eco x y) (SW: sw y z) (NECO: ~ eco y z) :
  exists k, eco x k /\ sb k z /\ ~ rmw k z.
Proof using.
assert (Wy: W y).
  apply (wf_ecoD WF) in ECO; try edone.
  apply (wf_swD WF) in SW; try edone.
  by unfolder in *; type_solver.
assert (SW1 := SW).
apply (wf_swD WF) in SW1; try edone.
unfolder in SW1; desc.
destruct SW2.
- exploit sw_in_eco_sb; eauto.
  unfolder; splits; eauto.
  by desf.
  unfold eqv_rel, seq; ins; desc.
  exists z0; splits; eauto using (eco_trans WF); subst.
  done.
  intro A; eapply (wf_rmwD WF) in A; unfolder in *; type_solver.
- exfalso; apply NECO.
  apply sw_in_eco; try done.
  unfolder; ins; desf.
Qed.

Lemma eco_sw WF SC_PER_LOC :
eco ⨾ (sw \ eco) ⊆ eco ⨾ (sb \ rmw).
Proof using.
unfold seq, minus_rel, inclusion; ins; desc.
eapply eco_sw_helper; eauto.
Qed.

Lemma eco_sw_1 WF SC_PER_LOC :
eco ⨾ sw ⊆ eco ∪ eco ⨾ (sb \ rmw).
Proof using.
unfolder; ins; desf.
destruct (classic (eco z y)).
by generalize (eco_trans WF); basic_solver.
right; eapply eco_sw_helper; eauto.
Qed.

Lemma eco_seq_hb WF SC_PER_LOC COMP : 
  eco ⨾ hb ⊆ eco ∪ eco ⨾ (sb \ rmw) ⨾ hb^?.
Proof using.
unfold hb; rewrite seq_ct_absorb_lt, cr_of_ct; eauto using eco_trans.
rewrite minus_union_l.
relsf; unionL; eauto with hahn.
rewrite rmw_in_fr, fr_in_eco; auto with hahn.
sin_rewrite eco_sw; auto.
rewrite !seqA; auto with hahn.
Qed.

Lemma release_in_hb_co WF SC_PER_LOC: release ⊆ (hb^? ⨾ co^?).
Proof using.
unfold release; rewrite rs_in_co; try done.
rewrite sb_in_hb; basic_solver 10.
Qed.

Lemma hb_alt WF: 
  hb ⊆ ⦗W⦘ ⨾ sw ∪ (⦗W⦘ ⨾ sw)^? ⨾ ((sb \ rmw) ∪ rmw ∪ ⦗F⦘ ⨾ sw ∪ (sb \ rmw) ⨾ sw ∪ rmw ⨾ sw)⁺.
Proof using.
unfold hb.
rewrite (dom_l (wf_swD WF)) at 1.
arewrite (⦗FW ∩₁ Rel⦘ ⊆ ⦗F⦘ ∪ ⦗W⦘) by type_solver 12.
relsf; rewrite <- !unionA.
arewrite (sb ⊆ (sb \ rmw) ∪ rmw) at 1 by unfolder; ins; tauto.
rewrite path_union1.
assert (TRANS: transitive (⦗W⦘ ⨾ sw)).
by apply transitiveI; rewrite (dom_r (wf_swD WF)) at 1; type_solver.
relsf.
unionL; [by vauto|].
rewrite !seqA.
arewrite_false (sw ⨾ ⦗W⦘).
by rewrite (dom_r (wf_swD WF)) at 1; type_solver.
unionR right.
hahn_frame.
apply inclusion_t_t.
basic_solver 42.
Qed.

Lemma rs_rf_rmw WF: 
  rs ⨾ (rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ rmw ⊆ rs.
Proof using.
unfold rs; rewrite !seqA.
arewrite ((rfi ∪ (sb ∩ same_loc)^? ⨾ rfe) ⨾ rmw ⊆ (sb ∩ same_loc)^? ⨾ rf ⨾ rmw).
rewrite rfi_union_rfe; basic_solver 12.
relsf; unionL.
rewrite !seqA.
arewrite ( sb ∩ same_loc ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ sb ∩ same_loc).
by arewrite_id ⦗W⦘; generalize (@sb_same_loc_trans G); ins; relsf.
rewrite (dom_l (wf_rfD WF)).
rewrite rtE.
rewrite <- ct_step.
basic_solver 21.
unionR right.
hahn_frame.
rewrite <- ct_end.
basic_solver.
Qed.

Lemma sw_rmw_sw WF: sw ⨾ rmw ⨾ sw ⊆ sw ⨾ sb^?.
Proof using.
unfold sw at 2.
unfold release; rewrite !seqA.
arewrite (rmw ⨾ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⊆ rmw).
by rewrite (dom_r (wf_rmwD WF)); type_solver.
unfold rs.
relsf.
rewrite !unionA.
apply inclusion_union_l.
- arewrite (rfi ⊆ sb).
  rewrite (rmw_in_sb WF).
  generalize (@sb_trans G); basic_solver 21.
- unfold sw, release.
  rewrite !seqA.
  arewrite !((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ rmw ⊆ rmw).
  by rewrite (dom_l (wf_rmwD WF)); type_solver.
  sin_rewrite !(rs_rf_rmw WF).
  arewrite !((⦗W⦘ ⨾ (sb ∩ same_loc ⨾ ⦗W⦘ ∪ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊))
    ⨾ ⦗W⦘ ⨾ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊ ⊆⦗W⦘ ⨾ (sb ∩ same_loc ⨾ ⦗W⦘ ∪ ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊)).
  relsf; unionL; [|by arewrite_id ⦗W⦘ at 2; relsf].
  rewrite rtE at 1; relsf; unionL; [basic_solver 12|unionR right].
  rewrite ct_begin, !seqA; rels.
  arewrite (sb ∩ same_loc ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ (sb ∩ same_loc)^?).
  generalize (@sb_same_loc_trans G); basic_solver 21.
  hahn_frame_l; rewrite <- !seqA; rewrite <- ct_begin; rels.
  unionL.
  * generalize (@sb_same_loc_trans G).
    basic_solver 42.
  * unfold rs.
    hahn_frame.
    basic_solver 21.
  * unfold rs.
    hahn_frame.
    basic_solver 21.
Qed.

(******************************************************************************)
(** IMM-coherence and its consequences **   *)
(******************************************************************************)

Definition coherence := irreflexive (hb ⨾ eco).
Implicit Type COH : coherence.

Lemma coherence_sc_per_loc COH : sc_per_loc G.
Proof using. 
red; rewrite sb_in_hb. 
red in COH; unfolder in *; basic_solver 12. 
Qed.

Definition coherent_expanded :=
  ⟪ Crf   : irreflexive (rf ⨾ hb) ⟫ /\
  ⟪ Crw   : irreflexive (co ⨾ rf ⨾ hb) ⟫ /\
  ⟪ Cww   : irreflexive (co ⨾ hb) ⟫ /\
  ⟪ Cwr   : irreflexive (co ⨾ hb ⨾ rf⁻¹) ⟫ /\
  ⟪ Crr   : irreflexive (co ⨾ rf ⨾ hb ⨾ rf⁻¹) ⟫.

Lemma hb_eco_r_alt : 
  hb ⨾ eco ≡ 
    hb ⨾ rf ∪ hb ⨾ co ∪ hb ⨾ co ⨾ rf ∪ hb ⨾ fr ∪ hb ⨾ fr ⨾ rf.
Proof using. unfold Execution_eco.eco, Execution.fr; basic_solver 42. Qed.

Proposition coherence_expanded_eq :
  coherence <-> coherent_expanded.
Proof using.
  unfold coherence; rewrite hb_eco_r_alt; unfold Execution.fr.
  unfold coherent_expanded; unnw.
  split; ins.
  - rewrite !seqA in *.
    repeat (apply irreflexive_union in H; desf); splits.
    all: try by rotate 1.
    all: try by rotate 2.
  - desf.
    relsf; repeat (splits; try apply irreflexive_union).
    all: try by rotate 1.
    all: try by rotate 2.
Qed.

Proposition coherence_alt :
  irreflexive (hb ∪ hb ⨾ rfe ∪ hb ⨾ co ⨾ rfe^? ∪ hb ⨾ fr ⨾ rfe^?) -> coherence.
Proof using.
  unfold coherence; unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize hb_trans; ins; relsf.
all: try (unfolder in *; basic_solver 12).
Qed.

Lemma hb_eco_irr COH : irreflexive (hb ⨾ eco).
Proof using.
apply COH.
Qed.

Lemma hb_irr WF COH : irreflexive hb.
Proof using.
unfold hb.
rewrite path_ut_first.
relsf; repeat (splits; try apply irreflexive_union).
by rewrite (ct_of_trans (@sb_trans G)); apply sb_irr.
rewrite (sw_in_sb_eco_sb WF (coherence_sc_per_loc COH)) at 1.
rotate 2.
arewrite ((sb ⨾ ⦗F ∩₁ Acq⦘)^? ⊆ (sb ∪ sw)＊).
arewrite (sb＊ ⊆ (sb ∪ sw)＊).
arewrite ((⦗F ∩₁ Rel⦘ ⨾ sb)^? ⊆ (sb ∪ sw)＊).
relsf.
generalize (eco_irr WF).
red in COH; revert COH.
basic_solver.
Qed.

Lemma hb_acyc WF COH : acyclic hb.
Proof using.
  eapply trans_irr_acyclic.
  2: by apply hb_trans.
  apply hb_irr; auto.
Qed.

Lemma w_hb_loc_w_in_co WF COH :
  ⦗W⦘ ⨾ hb ∩ same_loc ⨾ ⦗W⦘ ⊆ co.
Proof using.
apply (w_r_loc_w_in_co WF (wf_hbE WF) (hb_irr WF COH) (hb_eco_irr COH)).
Qed.

Lemma w_hb_loc_r_in_co_rf WF COH COMP:
  ⦗W⦘ ⨾ hb ∩ same_loc ⨾ ⦗R⦘ ⊆ co^? ⨾ rf.
Proof using.
apply (w_r_loc_r_in_co_rf WF (wf_hbE WF) (hb_eco_irr COH) COMP).
Qed.

Lemma r_hb_loc_w_in_fr WF COH COMP:
  ⦗R⦘ ⨾ hb ∩ same_loc ⨾ ⦗W⦘ ⊆ fr.
Proof using.
apply (r_r_loc_w_in_fr WF (wf_hbE WF) (hb_eco_irr COH) COMP).
Qed.

Lemma r_hb_loc_r_in_fr_rf WF COH COMP:
  ⦗R⦘ ⨾ hb ∩ same_loc ⨾ ⦗R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf.
Proof using.
apply (r_r_loc_r_in_fr_rf WF (wf_hbE WF) (hb_eco_irr COH) COMP).
Qed.


Lemma hb_loc_in_eco WF COH COMP:
  ⦗RW⦘ ⨾ hb ∩ same_loc ⨾ ⦗RW⦘ ⊆ eco ∪ (sb \ rmw) ∪ (sb \ rmw) ⨾ hb ⨾ (sb \ rmw).
Proof using.
unfold restr_eq_rel, Events.same_loc.

unfolder; ins; desc.
rename H0 into HB, H2 into SAME_LOC, H into RWx, H1 into RWy.
hahn_rewrite (wf_hbE WF) in HB; unfolder in *; desc.
forward (apply eco_almost_total with (x:=x) (y:=y)); eauto.
  by intro; subst; eapply hb_irr; edone.

desf.
- ins; desf; [basic_solver | |].
  by exfalso; eapply COH; basic_solver.
  apply ct_begin in HB0.
  unfold seq in HB0; desc.
  destruct HB0 as [HB0|X]; cycle 1.
by hahn_rewrite (wf_swD WF) in X; hahn_rewrite (wf_rfD WF) in H;
 exfalso; type_unfolder; unfolder in *; desf.
  apply rtE in HB2.
  unfold eqv_rel, union in HB2; desf.
  -- destruct (classic (rmw x y)).
    by left; left; apply fr_in_eco, rmw_in_fr; auto using coherence_sc_per_loc.
    by left; right; splits; eauto.
  -- apply ct_end in HB2.
    unfold seq in HB2; desc.
    destruct HB3 as [HB3|X]; cycle 1.
    * exfalso.
      apply sw_in_sb_eco_sb in X; auto using coherence_sc_per_loc.
      unfold seq, eqv_rel, clos_refl in X; desf.
      + apply COH with (x:=x).
        exists z2; splits.

        apply ct_begin; basic_solver.
        apply eco_transp_rf_rf_in_eco; auto; basic_solver 8.
      + apply COH with (x:=x).
        exists z2; splits.
        apply ct_begin; eexists; splits; try apply rt_end; basic_solver 6.
        by apply eco_transp_rf_rf_in_eco; auto; basic_solver 8.
      + type_solver.
      + type_solver.
    * assert (~rmw x z0).
      { intro RMW_x_z0.
        apply COH with (x:=z0).
        exists y; splits.
        apply ct_end; basic_solver 6.
        apply rmw_in_fr, fr_in_eco in RMW_x_z0; auto using coherence_sc_per_loc.
        apply transp_rf_rf_eco_in_eco; auto; basic_solver 8.
      }
      assert (~rmw z1 y).
      { intro RMW_z1_y.
        apply COH with (x:=x).
        exists z1; splits.
        apply ct_begin; basic_solver 6.
        apply rmw_in_fr, fr_in_eco in RMW_z1_y; auto using coherence_sc_per_loc.
        apply eco_transp_rf_rf_in_eco; auto; basic_solver 8.
      }
      apply rtE in HB2; unfold union, eqv_rel in HB2; desf.
      + left; right; splits.
        eby eapply sb_trans.
        intro RMW_x_y.
by hahn_rewrite (wf_rmwD WF) in RMW_x_y; hahn_rewrite (wf_rfD WF) in H0;
 unfolder in *; type_solver.
      + basic_solver 8.

- ins; desf; [basic_solver | |].
  by exfalso; eapply COH; basic_solver.
 hahn_rewrite (wf_rfD WF) in H;
 exfalso; type_unfolder; unfolder in *; desf.
- ins; desf; [basic_solver | |].
  by exfalso; eapply COH; basic_solver.
 hahn_rewrite (wf_rfD WF) in H0;
 exfalso; type_unfolder; unfolder in *; desf.
- ins; desf; [basic_solver | |].
  by exfalso; eapply COH; basic_solver.
 hahn_rewrite (wf_rfD WF) in H;
 exfalso; type_unfolder; unfolder in *; desf.
Qed.

Lemma hb_in_sb_swe : hb ⊆ (sb ∪ (sw \ sb))⁺.
Proof using.
  unfold hb.
  rewrite (ri_union_re G sw) at 1.
  apply inclusion_t_t.
  basic_solver.
Qed.

Lemma sprop_irr WF COH : irreflexive sprop.
Proof using.
  unfold sprop.
  rewrite sb_in_hb.
  arewrite ((hb ⨾ ⦗F⦘)^? ⨾ ⦗Acq ∪₁ W⦘ ⨾ hb ⨾ ⦗Rel⦘ ⊆ hb^? ⨾ hb).
  { basic_solver. }
  rewrite cr_hb_hb.
  arewrite_id ⦗W⦘. rewrite seq_id_l.
  apply irreflexive_seqC.
  rewrite crE, seq_union_r, seq_id_r.
  apply irreflexive_union. split.
  { by apply hb_irr. }
  arewrite (rfe ⊆ rf). rewrite rf_in_eco.
  apply COH.
Qed.

End IMM_hb.
