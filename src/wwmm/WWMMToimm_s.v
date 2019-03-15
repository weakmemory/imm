(******************************************************************************)
(** * WWMM is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events Execution Execution_eco.
Require Import imm_common imm_s_hb imm_s WWMM.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section WWMM_TO_IMM_S.

Variable G : execution.
Hypothesis WF : Wf G.

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

Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(imm_s_hb.sw).
Notation "'hb'" := G.(imm_s_hb.hb).

Notation "'sw_ww'" := G.(WWMM.sw).
Notation "'hb_ww'" := G.(WWMM.hb).

Notation "'detour'" := G.(detour).

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ar).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Lemma sw_ww_in_sw : sw_ww ⊆ sw.
Proof.
  unfold imm_s_hb.sw, WWMM.sw.
  arewrite (Sc ⊆₁ Rel) at 1 by mode_solver.
  arewrite (Sc ⊆₁ Acq) by mode_solver.
  unfold imm_s_hb.release, imm_s_hb.rs.
  rewrite !seqA.
  assert (⦗fun _ => True⦘ ⊆ (rf ⨾ rmw)＊) as HH
      by basic_solver.
  rewrite <- HH.
  rewrite <- !inclusion_id_cr.
  rewrite !seq_id_l.
  rewrite (dom_l WF.(wf_rfD)) at 1.
  basic_solver 10.
Qed.

Lemma hb_ww_in_hb : hb_ww ⊆ hb.
Proof. unfold imm_s_hb.hb, WWMM.hb. by rewrite sw_ww_in_sw. Qed.

Lemma hb_ww_co_fr_ac :
  acyclic (hb_ww ∪ ⦗ Sc ⦘ ⨾ (fr ∪ co) ⨾ ⦗ Sc ⦘).
Proof.
(* A proof idea: *)
(* ————————————— *)
(* acyclic     (hb ∪ [SC]; (fr ∪ co); [SC])                  ⇐ *)
(* acyclic     ([SC]; (hb⁺ ∪ fr ∪ co); [SC])                 ⇐ *)
(*   (via hb transitivity) *)
(* acyclic     ([SC]; (hb ∪ fr ∪ co); [SC])                  ⇐ *)
(* acyclic     ([SC]; (po ∪ rfe ∪ fr ∪ co); [SC])            ⇐ *)
(* acyclic     ([SC]; (po ∪ hb|loc ∪ fr ∪ co); [SC])         ⇐ *)
(* acyclic     ([SC]; scb; [SC]) *)
Admitted.

Lemma s_imm_consistent_implies_wwmm_consistent sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  exists mo, wwmm_consistent G mo.
Proof.
  cdes IPC. cdes IC.
  exists (tot_ext (acts G)
                  (hb_ww ∪ ⦗ Sc ⦘ ⨾ (fr ∪ co) ⨾ ⦗ Sc ⦘)).
  red. splits.
  { apply tot_ext_total. }
  { rewrite <- tot_ext_extends. eauto with hahn. }
  { rewrite hb_ww_in_hb, rf_in_eco.
    arewrite (eco ⊆ eco^?). apply IPC. }
  { unfolder. intros w' [r [HBWR HH]].
    destruct HH as [w [RF [[HBWW AA] WW']]].
    assert (hb w w') as HB by (by apply hb_ww_in_hb).
    apply WF.(wf_hbE) in HB.
    apply seq_eqv_l in HB. destruct HB as [EW HB].
    apply seq_eqv_r in HB. destruct HB as [HB EW'].
    apply (dom_l WF.(wf_rfD)) in RF.
    apply seq_eqv_l in RF. destruct RF as [WW RF].
    assert (exists l, loc w = Some l) as [l LL].
    { admit. }
    assert (w <> w') as NEQ.
    { intros HH. subst.
      eapply hb_irr; eauto. }
    edestruct WF.(wf_co_total).
    3: by eauto.
    1,2: by unfolder; splits.
    { eapply Cint. exists r. split.
      { apply hb_ww_in_hb. eauto. }
      right. apply fr_in_eco. eexists. eauto. }
    eapply Cint. exists w'. split; eauto.
    right. by apply co_in_eco. }
  { intros w' HH.
    apply seq_eqv_l in HH. destruct HH as [WW' HH].
    destruct HH as [r [MO HH]].
    apply seq_eqv_l in HH. destruct HH as [RR HH].
    destruct HH as [w [RF HH]].
    apply seq_eqv_l in HH. destruct HH as [WW [MOWW SL]].
    admit. }
  1-2: admit.
Admitted.

End WWMM_TO_IMM_S.
