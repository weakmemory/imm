(******************************************************************************)
(** * Definition of the PH memory model *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events Execution Execution_eco.
Require Import ph_hb ph_common.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section PH.

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
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'ar_int'" := G.(ar_int).

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
(** ** Derived relations  *)
(******************************************************************************)

Definition psc := ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘.

Definition ar := psc ∪ rfe ∪ ar_int.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition acyc_ext := acyclic ar.

Definition ph_consistent := 
  ⟪ Comp : complete G ⟫ /\
  ⟪ Cint : coherence G ⟫ /\
  ⟪ Cext : acyc_ext ⟫ /\
  ⟪ Cat  : rmw_atomicity G ⟫.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

Implicit Type COH : coherence G.
Implicit Type PSC : acyclic psc.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma psc_hb: psc ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ psc.
Proof.
unfold psc; generalize (@hb_trans G); basic_solver 20. 
Qed.

Lemma hb_psc: ⦗F∩₁Sc⦘ ⨾ hb ⨾ psc ⊆ psc.
Proof.
unfold psc; generalize (@hb_trans G); basic_solver 20. 
Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_pscE WF : psc ≡ ⦗E⦘ ⨾ psc ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold psc; rewrite (wf_hbE WF) at 1 2.
basic_solver 42.
Qed.

Lemma wf_arE WF : ar ≡ ⦗E⦘ ⨾ ar ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ar.
rewrite (wf_pscE WF), (wf_ar_intE WF), (wf_rfeE WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_pscD : psc ≡ ⦗F∩₁Sc⦘ ⨾ psc ⨾ ⦗F∩₁Sc⦘.
Proof.
split; [|basic_solver].
unfold psc; basic_solver 42.
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma no_psc_to_init WF : psc ≡ psc ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite wf_pscD at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma CoherentPSC WF PSC: irreflexive (co ⨾ rf^? ⨾ hb ⨾ psc ⨾ hb ⨾ rf⁻¹ ^?).
Proof.
rewrite wf_pscD.
rotate 4.
arewrite ((rf⁻¹)^? ⨾ co ⨾ rf^? ⊆ eco).
  by unfold Execution_eco.eco, Execution.fr; basic_solver 42.
arewrite (⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ psc).
unfolder; ins; desf.
eby eapply PSC, t_trans; apply t_step.
Qed.

Lemma C_EXT_helper2 WF: (psc ∪ rfe)⁺ ⊆ psc⁺ ∪ rfe.
Proof.
apply ct_ind_left with (P:= fun r => r).
by eauto with hahn.
by unionL; vauto.
ins; rewrite H; relsf; unionL.
arewrite (psc ⊆ psc＊); relsf.
rewrite ct_begin.
rewrite (dom_l wf_pscD) at 1; rewrite (dom_r (wf_rfeD WF)); type_solver 12.
rewrite (dom_r wf_pscD) at 1; rewrite (dom_l (wf_rfeD WF)); type_solver 12.
rewrite (dom_r (wf_rfeD WF)) at 1; rewrite (dom_l (wf_rfeD WF)); type_solver 12.
Qed.

Lemma acyc_ext_helper WF: 
  acyclic (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘) -> acyc_ext.
Proof.
generalize (@sb_trans G); intro.
intro; red; unfold ar.
apply acyclic_mon with (r:= ar_int ∪ (psc ∪ rfe)).
2: by basic_solver 12.
apply acyclic_union1.
- by rewrite (ar_int_in_sb WF); apply sb_acyclic.
- eapply acyclic_mon; [edone|basic_solver 12].
- rewrite (C_EXT_helper2 WF); unionL.
  arewrite (psc ⊆ sb^? ⨾ psc ⨾ sb^?) by basic_solver 12.
  relsf.
  rewrite (ar_int_in_sb WF) at 1; relsf.
  rewrite ct_begin, !seqA; relsf.
  arewrite (sb ⊆ sb^?) at 1.
  rewrite <- !seqA, <- ct_begin, !seqA.
  apply acyclic_union1.
  * red; rels; eapply acyclic_mon; [edone|basic_solver 12].
  * rewrite (dom_l (wf_rfeD WF)), <- seqA, acyclic_rotl.
    rewrite (dom_r (wf_rfeD WF)), !seqA.
    apply acyc_simple_helper.
    red; rels; eapply acyclic_mon; [edone|basic_solver 12].
  * relsf.
    rewrite (ct_begin (ar_int⁺ ⨾ rfe)).
    rewrite (ar_int_in_sb WF) at 1.
    rewrite !seqA; relsf.
    arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⨾ sb ⊆ (sb^? ⨾ psc ⨾ sb^?)⁺).
    { rewrite ct_end at 1; rewrite !seqA.
      arewrite (sb^? ⨾ sb ⊆ sb^?).
      by generalize (@sb_trans G); basic_solver.
      by rewrite <- ct_end. }
    rewrite (dom_l (wf_rfeD WF)) at 2.
    arewrite (rfe ⨾ (ar_int⁺ ⨾ ⦗W⦘ ⨾ rfe)＊ ⊆ (rfe ⨾ ar_int⁺ ⨾ ⦗W⦘)＊ ⨾ rfe).
    by rewrite <- seqA; apply rt_seq_swap.
    rewrite (dom_r (wf_rfeD WF)) at 1.
    rewrite !seqA.
    arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)⁺).
    arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
    arewrite (⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 3.
    relsf.
    arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
    relsf; red; rels.
Qed.



End PH.