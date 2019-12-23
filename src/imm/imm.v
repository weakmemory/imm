(******************************************************************************)
(** * Definition of the IMM memory model *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_hb.
Require Import imm_bob.
Require Import imm_ppo.

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

Definition scb := sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪
                     (hb ∩ same_loc) ∪ co ∪ fr.
Definition psc_base := ⦗ Sc ⦘ ⨾ (⦗ F ⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗ F ⦘)^? ⨾ ⦗ Sc ⦘.
Definition psc_f    := ⦗F∩₁Sc⦘ ⨾  hb ⨾ (eco ⨾ hb)^? ⨾ ⦗F∩₁Sc⦘.

Definition psc := ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘.

Definition ar := psc ∪ rfe ∪ ar_int.

Lemma ppo_in_ar : ppo G ⊆ ar.
Proof. rewrite ppo_in_ar_int. by arewrite (ar_int ⊆ ar). Qed.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition acyc_ext := acyclic ar.

Definition imm_consistent := 
  ⟪ Comp : complete G ⟫ /\
  ⟪ Cint : coherence G ⟫ /\
  ⟪ Cext : acyc_ext ⟫ /\
  ⟪ Cpsc : acyclic (psc_f ∪ psc_base) ⟫ /\
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

Lemma wf_scbE WF : scb ≡ ⦗E⦘ ⨾ scb ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold scb.
rewrite wf_sbE at 1 2 3. rewrite WF.(wf_hbE) at 1 2.
rewrite WF.(wf_coE) at 1. rewrite WF.(wf_frE) at 1.
basic_solver 42.
Qed.

Lemma wf_psc_baseE WF : psc_base ≡ ⦗E⦘ ⨾ psc_base ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold psc_base.
rewrite WF.(wf_hbE) at 1 2.
rewrite WF.(wf_scbE) at 1.
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

Lemma wf_psc_baseD : psc_base ≡ ⦗Sc⦘ ⨾ psc_base ⨾ ⦗Sc⦘.
Proof.
split; [|basic_solver].
unfold psc_base; basic_solver 42.
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

Lemma sw_in_ar_helper_old WF:
  ((sb ∩ same_loc)^? ⨾ rf ⨾ rmw)＊ ⊆
  (sb ∩ same_loc ⨾ ⦗W⦘)^? ∪ (sb ∩ same_loc)^? ⨾ (rfe ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)⁺.
Proof.
  rewrite rtE at 1; relsf; unionL; [basic_solver 21|].
  rewrite rfi_union_rfe; relsf.
  rewrite path_union.
  unionL.
  { rewrite (dom_r (wf_rmwD WF)) at 1.
    rewrite (rfi_in_sbloc' WF) at 1.
    rewrite (rmw_in_sb_loc WF) at 1.
    generalize (@sb_same_loc_trans G), (@sb_same_loc_W_trans G); ins; relsf. }
  rewrite ct_seq_swap, !seqA.
  rewrite (dom_r (wf_rmwD WF)) at 3.
  rewrite (rfi_in_sbloc' WF) at 1 2.
  rewrite (rmw_in_sb_loc WF) at 1 3.
  generalize (@sb_same_loc_trans G); intros HH; relsf.
  arewrite ((sb ∩ same_loc) ⊆ sb) at 3.
  unionR right.
  rewrite (dom_l WF.(wf_rfeD)), !seqA.
  rewrite <- seqA with (r2:= ⦗W⦘).
  rewrite ct_rotl, !seqA.
  arewrite ((sb ∩ same_loc)^? ⨾ (sb ∩ same_loc)^? ⊆ (sb ∩ same_loc)^?).
  { generalize HH. basic_solver 10. }
  hahn_frame.
  arewrite ((sb ⨾ ⦗W⦘)＊ ⨾ (sb ∩ same_loc)^? ⊆ sb^?).
  { arewrite_id ⦗W⦘. rewrite seq_id_r. rewrite rt_of_trans.
    2: by apply sb_trans.
    generalize sb_trans.
    basic_solver 10. }
  arewrite (rmw ⨾ (sb ⨾ ⦗W⦘)＊ ⊆ rmw ⨾ sb^? ⨾ ⦗W⦘).
  2: { rewrite (dom_l WF.(wf_rfeD)) at 1 2; rewrite !seqA.
       arewrite_id ⦗W⦘ at 1. rewrite seq_id_l.
       apply ct_end. }
  rewrite rtE, seq_union_r.
  unionL.
  { rewrite (dom_r (wf_rmwD WF)) at 1. basic_solver 10. }
  rewrite ct_of_trans.
  { basic_solver 10. }
  generalize sb_trans. basic_solver.
Qed.

Lemma sw_in_ar WF :
  sw ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^? ∪ sb.
Proof.
  assert ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ ar^?) as BB.
  { arewrite (⦗Acq⦘ ⊆ ⦗Acq/Rel⦘) by mode_solver.
      unfold ar, imm_ppo.ar_int, imm_bob.bob, imm_bob.fwbob.
      basic_solver 21. }
  assert (rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar) as CC.
  { unfold ar, imm_ppo.ar_int, imm_ppo.ppo.
    rewrite <- ct_step, (dom_l (wf_rmwD WF)), (rmw_in_sb WF) at 1.
    generalize (@sb_trans G) (R_ex_in_R); basic_solver 21. }

  assert (fwbob G ⊆ ar) as EE.
  { unfold ar. unfold imm_ppo.ar_int.
    rewrite fwbob_in_bob. basic_solver 10. }

  assert (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar^?) as DD.
  { rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l.
    unionL.
    2: generalize (@sb_trans G); basic_solver 10.
    rewrite crE, seq_union_l, seq_id_l. unionR left.
    arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ fwbob G).
    { unfold fwbob. basic_solver 10. }
    rewrite EE. basic_solver. }
  
  assert (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar^?) as FF.
  { rewrite crE with (r:=sb ∩ same_loc). rewrite !seq_union_l, !seq_union_r, seq_id_l.
    rewrite DD. unionL; [|done].
    basic_solver 10. }

  assert (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ ⦗W⦘ ⨾ sb ∩ same_loc) as UU.
  { unfold Events.same_loc.
    unfolder. ins. desf; eexists; splits; eauto.
    { eapply sb_trans; eauto. }
    etransitivity; eauto. }

  assert (ar^? ⨾ ar ⨾ ar^? ⊆ ar⁺) as WW.
  { arewrite (ar ⊆ ar⁺) at 2. by rewrite ct_cr, cr_ct. }

  unfold imm_hb.sw, imm_hb.release, imm_hb.rs.
  rewrite (sw_in_ar_helper_old WF).
  
  rewrite (dom_l (wf_rfeD WF)).
  rewrite !seqA, inclusion_ct_seq_eqv_l.
  arewrite ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ ⦗W⦘).
  { basic_solver 10. }
  arewrite (rfe ⊆ ar).
  arewrite (rfi ⊆ sb).

  arewrite ((sb ∩ same_loc ⨾ ⦗W⦘)^? ∪ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ (ar ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)⁺ ⊆
          (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ (ar ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊).
  { basic_solver 10. }
  arewrite (sb ∩ same_loc ⨾ ⦗W⦘ ∪ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ (ar ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊ ⊆
               (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ (ar ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊).
  { basic_solver 10. }

  assert (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⊆
            ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘) as ZZ.
  { basic_solver 20. }

  assert (rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo G) as QQ.
  { rewrite crE, !seq_union_l, !seq_union_r.
    rewrite rmw_sb_W_in_ppo, rmw_in_ppo; auto.
    basic_solver. }

  assert (ar ⨾ ar ⊆ ar⁺) as PP.
  { arewrite (ar ⊆ ar⁺). apply ct_unit. }
  
  rewrite rtE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
  unionL.
  { unionR right. generalize (@sb_trans G). basic_solver 21. }
  { rewrite !seqA.
    arewrite ((sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆
              (sb ∩ same_loc)^? ⨾ ⦗W⦘).
    { generalize (@sb_same_loc_trans G). basic_solver 10. }
    sin_rewrite FF. rewrite !seqA.
    rewrite BB. sin_rewrite WW. basic_solver 10. }
  { sin_rewrite ZZ. sin_rewrite FF. rewrite !seqA.
    rewrite ct_end, !seqA.
    arewrite (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ sb ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆
                  rmw ⨾ sb^?).
    { generalize (@sb_trans G). basic_solver 10. }
    sin_rewrite QQ.
    rewrite ppo_in_ar.
    arewrite (ar^? ⨾ (ar ⨾ ar)＊ ⨾ ar ⊆ ar⁺).
    2: basic_solver 20.
    sin_rewrite PP.
    rewrite rt_of_ct.
    rewrite <- ct_end. apply cr_ct. }
  unionR left.
  sin_rewrite ZZ. sin_rewrite FF. rewrite !seqA.
  rewrite ct_end, !seqA. rewrite BB.
  assert (sb^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ sb^? ⨾ ⦗W⦘) as TT.
  { generalize (@sb_trans G). basic_solver 10. }
  sin_rewrite TT.
  rewrite !seqA.
  repeat sin_rewrite QQ. rewrite ppo_in_ar.
  repeat sin_rewrite PP.
  rewrite rt_of_ct. sin_rewrite ct_unit. sin_rewrite ct_cr.
  sin_rewrite rt_ct. sin_rewrite cr_ct. basic_solver 10.
Qed.

Lemma f_sc_hb_f_sc_in_ar WF : 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar⁺.
Proof.
unfold imm_hb.hb.
rewrite (dom_r (wf_swD WF)).
rewrite (sw_in_ar WF); relsf.
arewrite ((sb ∪ ((sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^?) ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘
      ∪ sb ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘)) ⊆ sb ∪ sb^? ⨾ ⦗W⦘ ⨾ ar⁺ ⨾ (rmw ⨾ sb^?)^? ⨾ ⦗FR ∩₁ Acq⦘).
by basic_solver 21.
rewrite path_union.
generalize (@sb_trans G); ins; relsf; unionL.
by rewrite <- ct_step; unfold ar, imm_ppo.ar_int, imm_bob.bob, imm_bob.fwbob; mode_solver 21.
rewrite ct_seq_swap, !seqA.
rewrite ct_rotl, !seqA.
arewrite ((rmw ⨾ sb^?)^? ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar^?).
{ case_refl (rmw ⨾ sb^?).
  - arewrite (⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ∪ ⦗F ∩₁ Acq/Rel⦘) by mode_solver.
    unfold ar, imm_ppo.ar_int, imm_bob.bob, imm_bob.fwbob; basic_solver 15.
  - unfold ar, imm_ppo.ar_int, imm_ppo.ppo.
    rewrite <- ct_step.
    arewrite_id ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘; relsf.
    rewrite (dom_l (wf_rmwD WF)) at 1.
    rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1.
    rewrite (rmw_in_sb WF).
    generalize (@sb_trans G); basic_solver 21. }
arewrite ((rmw ⨾ sb^?)^? ⨾ ⦗F ∩₁ Acq ∪₁ R ∩₁ Acq⦘ ⨾ sb^? ⊆ sb^?).
by rewrite (rmw_in_sb WF); basic_solver.
arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar^?).
by unfold ar, imm_ppo.ar_int, imm_bob.bob, imm_bob.fwbob; mode_solver 21.
arewrite (⦗F ∩₁ Sc⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ar^?).
by unfold ar, imm_ppo.ar_int, imm_bob.bob, imm_bob.fwbob; mode_solver 21.
relsf.
Qed.

Lemma acyc_ext_helper WF :
  acyclic (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘) -> acyc_ext.
Proof.
  intros AC.
  generalize (@sb_trans G); intro SBT.
  red. unfold ar.
  apply acyclic_mon with (r:= ar_int ∪ (psc ∪ rfe)).
  2: by basic_solver 12.
  apply acyclic_union1.
  { by rewrite (ar_int_in_sb WF); apply sb_acyclic. }
  { eapply acyclic_mon; [edone|basic_solver 12]. }
  rewrite (C_EXT_helper2 WF); unionL.
  arewrite (psc ⊆ sb^? ⨾ psc ⨾ sb^?) by basic_solver 12.
  relsf.
  rewrite (ar_int_in_sb WF) at 1; relsf.
  rewrite ct_begin, !seqA; relsf.
  arewrite (sb ⊆ sb^?) at 1.
  rewrite <- !seqA, <- ct_begin, !seqA.
  apply acyclic_union1.
  { red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  { rewrite (dom_l (wf_rfeD WF)), <- seqA, acyclic_rotl.
    rewrite (dom_r (wf_rfeD WF)), !seqA.
    apply acyclic_seq_from_union.
    red; rels; eapply acyclic_mon; [edone|basic_solver 12]. }
  relsf.
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
  { by rewrite <- seqA; apply rt_seq_swap. }
  rewrite (dom_r (wf_rfeD WF)) at 1.
  rewrite !seqA.
  arewrite ((sb^? ⨾ psc ⨾ sb^?)⁺ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)⁺).
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  arewrite (⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘ ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 3.
  relsf.
  arewrite (rfe ⊆ (sb^? ⨾ psc ⨾ sb^? ∪ rfe ∪ ⦗R⦘ ⨾ ar_int⁺ ⨾ ⦗W⦘)＊) at 2.
  relsf; red; rels.
Qed.

Lemma psc_base_in_psc_f WF (SC_F : Sc ⊆₁ F∩₁Sc): 
  psc_base ⊆ psc_f.
Proof.
  unfold psc_base, scb.
  arewrite (sb \ same_loc ⊆ sb).
  arewrite (sb ⊆ hb).
  arewrite (hb ⨾ hb ⨾ hb ⊆ hb).
  { unfold imm_hb.hb. by rewrite !ct_ct. }
  arewrite (hb ∪ hb ∪ hb ∩ same_loc ⊆ hb).
  rewrite co_in_eco, fr_in_eco.
  rewrite unionA, unionK.
  rewrite SC_F. 
  rewrite !seq_union_l, !seq_union_r.
  arewrite ((⦗F⦘ ⨾ hb)^? ⨾ hb ⨾ (hb ⨾ ⦗F⦘)^? ⊆ hb).
  { generalize (@hb_trans G). basic_solver 10. }
  unionL.
  { unfold psc_f. basic_solver 10. }
  rewrite WF.(wf_ecoD), !seqA.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ (⦗F⦘ ⨾ hb)^? ⨾ ⦗RW⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ hb)
    by type_solver 10.
  arewrite (⦗RW⦘ ⨾ (hb ⨾ ⦗F⦘)^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ hb ⨾ ⦗F ∩₁ Sc⦘)
    by type_solver 10.
  unfold psc_f. basic_solver 10.
Qed.

End IMM.
