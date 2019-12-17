(******************************************************************************)
(** * Definition of the common part of IMM and s_IMM  *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

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
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
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
(** ** Derived relations  *)
(******************************************************************************)

Definition fwbob := sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
                         sb ⨾ ⦗F∩₁Acq/Rel⦘ ∪ ⦗F∩₁Acq/Rel⦘ ⨾ sb.

Definition bob := fwbob ∪ ⦗R∩₁Acq⦘ ⨾ sb.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_to_w_rel_in_fwbob : sb ⨾ ⦗W∩₁Rel⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_from_w_rel_in_fwbob : ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_to_f_in_fwbob : sb ⨾ ⦗F∩₁Acq/Rel⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_from_f_in_fwbob : ⦗F∩₁Acq/Rel⦘ ⨾ sb  ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma fwbob_in_bob : fwbob ⊆ bob.
Proof. unfold bob. basic_solver 12. Qed.

Lemma sb_to_w_rel_in_bob : sb ⨾ ⦗W∩₁Rel⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_to_w_rel_in_fwbob.
Qed.

Lemma sb_from_w_rel_in_bob : ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_from_w_rel_in_fwbob.
Qed.

Lemma sb_to_f_in_bob : sb ⨾ ⦗F∩₁Acq/Rel⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_to_f_in_fwbob.
Qed.

Lemma sb_from_f_in_bob : ⦗F∩₁Acq/Rel⦘ ⨾ sb  ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_from_f_in_fwbob.
Qed.

Lemma sb_from_r_acq_in_bob : ⦗R∩₁Acq⦘ ⨾ sb  ⊆ bob.
Proof. unfold bob. basic_solver 10. Qed.

Lemma fwbob_in_sb : fwbob ⊆ sb.
Proof.
  unfold fwbob.
  basic_solver 12.
Qed.

Lemma sb_fwbob_in_fwbob : sb ⨾ fwbob ⊆ fwbob⁺.
Proof.
unfold fwbob.
generalize (@sb_trans G); ins.
relsf; unionL.
1,3: rewrite <- ct_step; basic_solver 42.
1,2: rewrite ct_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 16.
Qed.

Lemma bob_in_sb : bob ⊆ sb.
Proof.
unfold bob; rewrite fwbob_in_sb; basic_solver.
Qed.


(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_fwbobE WF : fwbob ≡ ⦗E⦘ ⨾ fwbob ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold fwbob.
rewrite wf_sbE.
basic_solver 42.
Qed.

Lemma wf_bobE WF : bob ≡ ⦗E⦘ ⨾ bob ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold bob.
rewrite (wf_fwbobE WF), wf_sbE.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma fwbob_r_sb: fwbob ⨾ ⦗ R ⦘ ⨾ sb ⊆ fwbob.
Proof.
unfold fwbob; relsf; unionL.
all: try by type_solver.
all: generalize (@sb_trans G); basic_solver 21.
Qed.

Lemma bob_r_sb: bob ⨾ ⦗ R ⦘ ⨾ sb ⊆ bob.
Proof.
unfold bob; relsf; rewrite fwbob_r_sb.
generalize (@sb_trans G); basic_solver 21.
Qed.

Lemma bob_sb :
  (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+ ⨾ ⦗W⦘ ⊆ 
  bob^+ ⨾ (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘.
Proof.
apply ct_ind_left with (P:= fun r =>  r ⨾ ⦗W⦘).
by auto with hahn.
by arewrite (bob ⊆ bob⁺); basic_solver 12.
intros k H.
rewrite !seqA; rewrite H; clear k H.
relsf; unionL.
- arewrite(bob ⊆ bob^*) at 1; relsf.
- sin_rewrite bob_in_sb.
generalize (@sb_trans G); ins; relsf.
basic_solver 12.
- arewrite (bob ⊆ bob⁺); basic_solver 12.
- generalize (@sb_trans G); basic_solver 12.
Qed.

Lemma tc_bob :
  bob^+ ⊆ fwbob^+ ∪ ⦗R ∩₁ Acq⦘ ⨾ sb.
Proof.
unfold bob.
apply ct_ind_left with (P:= fun r =>  r).
by auto with hahn.
by arewrite (fwbob ⊆ fwbob⁺); basic_solver 12.
intros k H.
rewrite H; clear k H.
relsf; unionL.
- by arewrite (fwbob ⊆ fwbob^*); relsf; basic_solver 12.
- sin_rewrite (fwbob_in_sb).
  generalize (@sb_trans G); ins; relsf; basic_solver 12.
- arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R⦘). basic_solver.
  sin_rewrite fwbob_r_sb.
  by arewrite (fwbob ⊆ fwbob^+); basic_solver 21.
- generalize (@sb_trans G); basic_solver 12.
Qed.

End IMM.
