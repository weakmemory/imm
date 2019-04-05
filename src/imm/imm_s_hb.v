(******************************************************************************)
(** * Definition of happens-before in the s_IMM memory model (similar to C11) *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM_hb.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).

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

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := G.(W_ex).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type SC_PER_LOC : sc_per_loc G.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* release sequence *)
Definition rs := ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊.

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ rf  ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

(* happens-before *)
Definition hb := (sb ∪ sw)⁺.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma hb_trans : transitive hb.
Proof. vauto. Qed.

Lemma sb_in_hb : sb ⊆ hb.
Proof. vauto. Qed.

Lemma sw_in_hb : sw ⊆ hb.
Proof. vauto. Qed.

Lemma cr_hb_hb : hb^? ⨾ hb ≡ hb.
Proof. generalize hb_trans; basic_solver. Qed.

Lemma cr_hb_cr_hb : hb^? ⨾ hb^? ≡ hb^?.
Proof. generalize hb_trans; basic_solver 20. Qed.

Lemma hb_sb_sw : hb ≡ hb^? ⨾ (sb ∪ sw).
Proof.
unfold hb; rewrite ct_end at 1; rels.
Qed.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma loceq_rs WF : funeq loc rs.
Proof. destruct WF; unfold rs; desf; eauto 10 with hahn. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_rsE WF : rs ≡ ⦗W⦘ ∪ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof.
unfold rs.
split; [|basic_solver 12].
rewrite rtE; relsf; unionL.
rewrite wf_sbE; basic_solver 21.
unionR right -> right.
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
Proof.
unfold release.
rewrite (wf_rsE WF).
rewrite (@wf_sbE G) at 1.
basic_solver 42.
Qed.

Lemma wf_swE_right WF : sw ≡ sw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold sw.
rewrite wf_sbE at 1 2.
rewrite (wf_rfE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swE WF : sw ≡ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
rewrite (wf_swE_right WF) at 1.
hahn_frame.
unfold sw.
rewrite (wf_releaseE WF).
rewrite (dom_l (wf_rfE WF)).
rewrite (dom_l (@wf_sbE G)).
basic_solver 40.
Qed.

Lemma wf_hbE WF : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof.
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
Proof.
split; [|basic_solver].
unfold rs.
rewrite rtE; relsf; unionL; [basic_solver 12|].
rewrite (dom_r (wf_rmwD WF)) at 1.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r.
basic_solver 42.
Qed.

Lemma wf_releaseD WF : release ≡ ⦗FW∩₁Rel⦘ ⨾ release ⨾ ⦗W⦘.
Proof.
split; [|basic_solver].
unfold release.
rewrite (wf_rsD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_swD WF : sw ≡ ⦗FW∩₁Rel⦘ ⨾ sw ⨾ ⦗FR∩₁Acq⦘.
Proof.
split; [|basic_solver].
unfold sw.
rewrite (wf_releaseD WF) at 1.
rewrite (wf_rfD WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma no_sw_to_init WF : sw ≡ sw ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite (wf_swD WF) at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma no_hb_to_init WF : hb ≡ hb ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
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

Lemma release_rf_in_sw WF: release ⨾ rf ⨾ ⦗Acq⦘ ⊆ sw.
Proof.
rewrite (wf_rfD WF); unfold sw; basic_solver 42.
Qed.

Lemma sw_in_release_rf WF: 
  sw ⨾ ⦗R⦘ ⊆ release ⨾ rf ⨾ ⦗Acq⦘.
Proof.
unfold sw; rewrite !seqA.
arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗R⦘ ⊆ ⦗Acq⦘) by type_solver 42.
Qed.


Lemma rs_in_co WF SC_PER_LOC COMP: rs ⊆ ⦗W⦘ ⨾ co^?.
Proof.
unfold rs.

assert (A: ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ co^?).
{ arewrite (⦗W⦘ ⊆ ⦗W⦘ ⨾ ⦗W⦘) at 1 by basic_solver.
  rewrite crE; relsf; unionL; [basic_solver|].
  sin_rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC).
  sin_rewrite (dom_l (wf_coiD WF)).
  ie_unfolder; basic_solver. }


rewrite rtE; relsf; unionL; [done|].
sin_rewrite !(rf_rmw_in_co WF SC_PER_LOC COMP).
sin_rewrite (dom_r (wf_coD WF)).

sin_rewrite A.
rewrite !seqA.
hahn_frame.
arewrite_id ⦗W⦘.
generalize (co_trans WF); ins; relsf.
Qed.

Lemma release_in_hb_co WF SC_PER_LOC COMP: release ⊆ (hb^? ⨾ co^?).
Proof.
unfold release; rewrite rs_in_co; try done.
rewrite sb_in_hb; basic_solver 10.
Qed.

Lemma hb_W WF : hb ⨾ ⦗ W ⦘ ⊆ (hb ⨾ ⦗FR∩₁Acq⦘)^? ⨾ sb.
Proof.
unfold hb; rewrite path_ut_last at 1.
generalize (@sb_trans G); ins; relsf; unionL.
basic_solver.
rewrite !seqA; rewrite (dom_r (wf_swD WF)) at 2.
rewrite !seqA.
arewrite (sw ⊆ (sb ∪ sw)＊) at 2.
rewrite crE; relsf; unionL.
type_solver.
basic_solver 12.
Qed.

Lemma hb_first_Rel WF : hb ⊆ sb ∪ sb^? ⨾ ⦗FW ∩₁ Rel⦘ ⨾ hb.
Proof.
unfold hb.
rewrite path_ut_first at 1.
generalize (@sb_trans G); ins; relsf; unionL.
basic_solver.
rewrite (dom_l (wf_swE WF)) at 1.
rewrite (dom_l (wf_swD WF)) at 1.
arewrite (sw ⊆ (sb ∪ sw)⁺) at 1; relsf.
basic_solver 21.
Qed.

Lemma release_int : release ⊆ release ⨾ ⦗W_ex⦘ ∪ ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ ⦗W⦘ ∪ 
  ⦗W ∩₁ Rel⦘ ⨾  (sb ∩ same_loc)^? ⨾ ⦗W⦘.
Proof.
unfold release, rs.
rewrite rtE; relsf; unionL.
generalize (@sb_trans G); basic_solver 21.
rewrite rmw_W_ex at 1.
rewrite <- !seqA, inclusion_ct_seq_eqv_r, !seqA.
basic_solver 21.
Qed.

(******************************************************************************)
(** ... **   *)
(******************************************************************************)

Definition coherence := irreflexive (hb ⨾ eco^?).

Implicit Type COH : coherence.

Lemma coherence_sc_per_loc COH : sc_per_loc G.
Proof. 
red; rewrite sb_in_hb. 
red in COH; unfolder in *; basic_solver 12. 
Qed.

Lemma hb_irr WF COH : irreflexive hb.
Proof.
red in COH.
unfolder in *; eauto 20.
Qed.

Proposition coherence_alt :
  irreflexive (hb ∪ hb ⨾ rfe ∪ hb ⨾ co ∪ hb ⨾ co ⨾ rfe ∪ hb ⨾ fr ∪ hb ⨾ fr ⨾ rfe) -> coherence.
Proof.
  unfold coherence; unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize hb_trans; ins; relsf.
all: try (unfolder in *; basic_solver 12).
Qed.

End IMM_hb.