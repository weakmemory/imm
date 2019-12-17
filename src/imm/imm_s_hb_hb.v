(******************************************************************************)

(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_hb.
Require Import imm_s_hb.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section S_HB_HB.

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


Notation "'s_rs'" := G.(imm_s_hb.rs).
Notation "'s_release'" := G.(imm_s_hb.release).
Notation "'s_sw'" := G.(imm_s_hb.sw).
Notation "'s_hb'" := G.(imm_s_hb.hb).


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
Notation "'R_ex'" := (R_ex G).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)
Lemma s_rs_in_rs : s_rs ⊆ rs.
Proof.
unfold imm_s_hb.rs, imm_hb.rs.
hahn_frame.
rewrite rtE at 1; relsf.
apply inclusion_union_l.
rewrite rtE at 1; relsf.
basic_solver.
unionR right.
arewrite_id ⦗W⦘; rels.
arewrite (rf ⨾ rmw ⊆ (sb ∩ same_loc)^? ⨾ rf ⨾ rmw) at 1 by basic_solver 12.
rewrite ct_begin.
generalize (@sb_same_loc_trans G); ins; rewrite !seqA; relsf.
generalize (ct_begin ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)).
basic_solver 40.
Qed.

Lemma s_release_in_release : s_release ⊆ release.
Proof.
unfold imm_s_hb.release, imm_hb.release.
by rewrite s_rs_in_rs.
Qed.

Lemma s_sw_in_sw : s_sw ⊆ sw.
Proof.
unfold imm_s_hb.sw, imm_hb.sw.
rewrite s_release_in_release.
rewrite (rfi_union_rfe).
basic_solver 21.
Qed.

Lemma s_hb_in_hb : s_hb ⊆ hb.
Proof.
unfold imm_s_hb.hb, imm_hb.hb.
by rewrite s_sw_in_sw.
Qed.

(******************************************************************************)
(** Properties **  *)
(******************************************************************************)

Lemma coherence_implies_s_coherence (WF: Wf G) (COMP: complete G) :
  imm_hb.coherence G -> imm_s_hb.coherence G.
Proof.
unfold imm_s_hb.coherence.
unfolder; ins; desf.
eapply imm_hb.hb_irr; eauto.
eapply s_hb_in_hb; edone.
unfold imm_hb.coherence in *; unfolder in *.
eapply H; eexists; split; eauto.
eapply s_hb_in_hb; edone.
Qed.

End S_HB_HB.
