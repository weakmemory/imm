(******************************************************************************)
(** * Weaker IMM model for Promise->IMM    *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_common.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

Variable G : execution.
Variable sc : relation actid.

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
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'bob'" := G.(bob).
Notation "'ppo'" := G.(ppo).
Notation "'ar_int'" := G.(ar_int).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
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

(* Definition psc := ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘. *)

Definition scb := sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪
                     (hb ∩ same_loc) ∪ co ∪ fr.
Definition psc_base := ⦗ Sc ⦘ ⨾ (⦗ F ⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗ F ⦘)^? ⨾ ⦗ Sc ⦘.
Definition psc_f    := ⦗F∩₁Sc⦘ ⨾  hb ⨾ (eco ⨾ hb)^? ⨾ ⦗F∩₁Sc⦘.

Definition ar := sc ∪ rfe ∪ ar_int.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Record wf_sc :=
  { wf_scE : sc ≡ ⦗E⦘ ⨾ sc ⨾ ⦗E⦘ ;
    wf_scD : sc ≡ ⦗F∩₁Sc⦘ ⨾ sc ⨾ ⦗F∩₁Sc⦘ ;
    sc_trans : transitive sc ;
    wf_sc_total : is_total (E ∩₁ F ∩₁ Sc) sc ;
    sc_irr : irreflexive sc ;
  }.

Definition acyc_ext := acyclic ar.

Definition coh_sc := irreflexive (sc ⨾ hb ⨾ (eco ⨾ hb)^?).

Definition imm_consistent := 
  ⟪ Wf_sc : wf_sc ⟫ /\
  ⟪ Csc   : coh_sc ⟫ /\
  ⟪ Comp  : complete G ⟫ /\
  ⟪ Cint  : coherence G ⟫ /\
  ⟪ Cext  : acyc_ext ⟫ /\
  ⟪ Cat   : rmw_atomicity G ⟫.

Definition imm_psc_consistent :=
  ⟪ IC   : imm_consistent ⟫ /\
  ⟪ Cpsc : acyclic (psc_f ∪ psc_base) ⟫.

Implicit Type WF : Wf G.
Implicit Type WF_SC : wf_sc.
Implicit Type IMMCON : imm_consistent.
Implicit Type CSC : coh_sc.
Implicit Type COMP : complete G.
Implicit Type COH : coherence G.
Implicit Type ACYC_EXT : acyc_ext.
Implicit Type AT : rmw_atomicity G.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

(* Lemma wf_pscE WF : psc ≡ ⦗E⦘ ⨾ psc ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold psc; rewrite (wf_hbE WF) at 1 2.
basic_solver 42.
Qed. *)

Lemma wf_arE WF WF_SC : ar ≡ ⦗E⦘ ⨾ ar ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ar.
rewrite (wf_scE WF_SC), (wf_ar_intE WF), (wf_rfeE WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

(* Lemma wf_pscD : psc ≡ ⦗F∩₁Sc⦘ ⨾ psc ⨾ ⦗F∩₁Sc⦘.
Proof.
split; [|basic_solver].
unfold psc; basic_solver 42.
Qed. *)

(******************************************************************************)
(** ** init *)
(******************************************************************************)

(* Lemma no_psc_to_init WF : psc ≡ psc ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite wf_pscD at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed. *)

Lemma no_sc_to_init WF WF_SC :
 sc ≡ sc ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite wf_scD at 1; try done.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma F_sc_ar_F_sc WF WF_SC ACYC_EXT:
  ⦗F ∩₁ Sc⦘ ⨾ ar⁺ ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof.
rewrite wf_arE; try done.
rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
unfold ar.
destruct WF_SC.
unfolder; ins; desf.
eapply tot_ex; eauto; try basic_solver.
intro; eapply ACYC_EXT.
eapply t_trans; unfold ar; [basic_solver| apply t_step; basic_solver].
intro; eapply ACYC_EXT; unfold ar; basic_solver.
Qed.

Lemma sw_in_ar WF : 
  sw ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^? ∪ sb.
Proof.
unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
rewrite (s_sw_in_ar_helper WF).
rewrite rfi_union_rfe.
generalize (@sb_trans G); ins.
generalize (@sb_same_loc_trans G); ins.
assert (BB: (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ ar^?).
{ arewrite (⦗Acq⦘ ⊆ ⦗Acq/Rel⦘) by mode_solver.
by unfold ar, imm_common.ar_int, imm_common.bob, imm_common.fwbob; basic_solver 21. }
assert (CC: rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar).
{ unfold ar, imm_common.ar_int, imm_common.ppo.
  rewrite <- ct_step, (dom_l (wf_rmwD WF)), (rmw_in_sb WF) at 1.
  generalize (@sb_trans G) (R_ex_in_R); basic_solver 21. }
rewrite (dom_l (wf_rfeD WF)).
rewrite !seqA, inclusion_ct_seq_eqv_l.
arewrite (rfe ⊆ ar).
arewrite (rfi ⊆ sb).
relsf; unionL.
- unionR right; basic_solver 21.
- arewrite_id ⦗W⦘ at 2.
  relsf.
  rewrite BB.
  arewrite (ar ⊆ ar⁺) at 1.
  arewrite (ar ⊆ ar⁺) at 2.
  relsf.
arewrite (⦗Rel⦘
⨾ (⦗F⦘ ⨾ sb)^?
  ⨾ ⦗W⦘
    ⨾ (sb ∩ same_loc)^? ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⊆ sb^?).
basic_solver 21.
  basic_solver 40.
- rewrite ct_end.
  rewrite CC at 1; rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ sb^?) by basic_solver 21.
  arewrite (ar ⊆ ar＊) at 1.
  arewrite (ar ⊆ ar⁺) at 2.
  arewrite (ar ⊆ ar⁺) at 3.
  relsf.
arewrite (sb^?
⨾ ⦗W⦘
  ⨾ (sb ∩ same_loc)^? ⊆ sb^?).
  basic_solver 21.
  basic_solver 21.
- rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ sb^?) by basic_solver 21.
  rewrite ct_end, !seqA.
  arewrite(sb^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ sb^?) by basic_solver.
  sin_rewrite !CC.
  rewrite BB.
  arewrite (ar ⊆ ar＊) at 1.
  arewrite (ar ⊆ ar⁺) at 2.
  arewrite (ar ⊆ ar⁺) at 3.
  arewrite (ar ⊆ ar＊) at 4.
  arewrite (ar ⊆ ar＊) at 5.
  arewrite (ar ⊆ ar＊) at 6.
arewrite_id ⦗W⦘ at 2.
  relsf.
  basic_solver 12.
Qed.

Lemma f_sc_hb_f_sc_in_ar WF : 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar⁺.
Proof.
unfold imm_s_hb.hb.
rewrite (dom_r (wf_swD WF)).
rewrite (sw_in_ar WF); relsf.
arewrite ((sb ∪ ((sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^?) ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘
      ∪ sb ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘)) ⊆ sb ∪ sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^? ⨾ ⦗FR ∩₁ Acq⦘).
by basic_solver 21.
rewrite path_union.
generalize (@sb_trans G); ins; relsf; unionL.
by rewrite <- ct_step; unfold ar, imm_common.ar_int, imm_common.bob,  imm_common.fwbob; mode_solver 21.
rewrite ct_seq_swap, !seqA.
rewrite ct_rotl, !seqA.
arewrite ((rmw ⨾ sb^?)^? ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar^?).
{ case_refl (rmw ⨾ sb^?).
  - arewrite (⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ∪ ⦗F ∩₁ Acq/Rel⦘) by mode_solver.
    unfold ar, imm_common.ar_int, imm_common.bob, imm_common.fwbob; basic_solver 15.
  - unfold ar, imm_common.ar_int, imm_common.ppo.
    rewrite <- ct_step.
    arewrite_id ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘; relsf.
    rewrite (dom_l (wf_rmwD WF)) at 1.
    rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1.
    rewrite (rmw_in_sb WF).
    generalize (@sb_trans G); basic_solver 21. }
arewrite ((rmw ⨾ sb^?)^? ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⨾ sb^? ⊆ sb^?).
by rewrite (rmw_in_sb WF); basic_solver.
arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar^?).
by unfold ar, imm_common.ar_int, imm_common.bob, imm_common.fwbob; mode_solver 21.
arewrite (⦗F ∩₁ Sc⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar^?).
by unfold ar, imm_common.ar_int, imm_common.bob, imm_common.fwbob; mode_solver 21.
arewrite (ar ⊆ ar⁺) at 1.
arewrite (ar ⊆ ar⁺) at 2.
arewrite (ar ⊆ ar⁺) at 3.
arewrite (ar ⊆ ar⁺) at 4.
arewrite (ar ⊆ ar⁺) at 5.
relsf.
Qed.

Lemma f_sc_hb_f_sc_in_sc WF WF_SC ACYC_EXT: 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof.
arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗F ∩₁ Sc⦘) by basic_solver.
sin_rewrite (f_sc_hb_f_sc_in_ar WF).
apply F_sc_ar_F_sc; done.
Qed.

Lemma wf_ar WF IMMCON : well_founded ar.
Proof.
  eapply wf_finite; auto.
  { cdes IMMCON. apply Cext. }
  rewrite wf_arE; auto.
  2: by apply IMMCON.
  apply doma_eqv.
Qed.

Lemma wf_ar_tc WF IMMCON : well_founded (ar⁺).
Proof.
  eapply wf_finite; auto.
  { cdes IMMCON. unfold acyclic. rewrite ct_of_ct.
    apply Cext. }
  rewrite wf_arE; auto.
  2: by apply IMMCON.
  apply ct_doma. apply doma_eqv.
Qed.

Lemma ar_int_in_ar : ar_int ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma ppo_in_ar : ppo ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply ppo_in_ar_int.
Qed.

Lemma bob_in_ar : bob ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply bob_in_ar_int.
Qed.

Lemma detour_in_ar : detour ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply detour_in_ar_int.
Qed.

Lemma rfe_in_ar : rfe ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma sc_in_ar : sc ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma w_ex_acq_sb_w_in_ar : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply w_ex_acq_sb_w_in_ar_int.
Qed.

Lemma coh_sc_alt WF WF_SC CSC COH : ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ sc.
Proof.
rewrite (dom_l (wf_hbE WF)) at 1.
rewrite (dom_r (wf_hbE WF)) at 2.
unfolder; ins; desf.
eapply tot_ex.
apply WF_SC.
basic_solver.
basic_solver.
intro; eapply CSC; basic_solver 10.
intro; subst.
eapply COH.
eexists; splits; [ | eby right].
eapply hb_trans; eauto.
Qed.

Proposition coh_helper_alt :
  irreflexive (hb ⨾ sc^? ∪ hb ⨾ (sc ⨾ hb)^? ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ co ∪ hb ⨾ (sc ⨾ hb)^? ⨾ co ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ fr ∪ hb ⨾ (sc ⨾ hb)^? ⨾ fr ⨾ rfe) -> 
  irreflexive (hb ⨾ (sc ⨾ hb)^? ⨾ eco^?).
Proof.
unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize (@hb_trans G); ins; relsf.
all: try (unfolder in *; basic_solver 12).
all: try (unfolder in *; basic_solver 16).
Qed.

End IMM.