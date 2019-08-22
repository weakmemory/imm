Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_common.
Require Import CombRelations.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TraversalConfig.

  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rf'" := G.(rf).
  Notation "'co'" := G.(co).
  Notation "'coe'" := G.(coe).
  Notation "'fr'" := G.(fr).

  Notation "'eco'" := G.(eco).

  Notation "'bob'" := G.(bob).
  Notation "'fwbob'" := G.(fwbob).
  Notation "'ppo'" := G.(ppo).
  Notation "'fre'" := G.(fre).
  Notation "'rfi'" := G.(rfi).
  Notation "'rfe'" := G.(rfe).
  Notation "'deps'" := G.(deps).
  Notation "'detour'" := G.(detour).
  Notation "'release'" := G.(release).
  Notation "'sw'" := G.(sw).
  Notation "'hb'" := G.(hb).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := G.(S_tm).
  Notation "'S_tmr'" := G.(S_tmr).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

(******************************************************************************)
(** **   *)
(******************************************************************************)

  Definition next C := E ∩₁ dom_cond sb C ∩₁ set_compl C.

  Record trav_config :=
    mkTC { covered : actid -> Prop; issued : actid -> Prop; }.

  Definition same_trav_config (T T' : trav_config) :=
    covered T ≡₁ covered T' /\ issued T ≡₁ issued T'.

  Definition coverable T := E ∩₁ dom_cond sb (covered T) ∩₁ 
                              ((W ∩₁ issued T) ∪₁
                               (R ∩₁ (dom_cond rf (issued T))) ∪₁
                               (F ∩₁ (dom_cond sc (covered T)))).

  Definition issuable T := E ∩₁ W ∩₁
                           (dom_cond fwbob (covered T)) ∩₁
                           (dom_cond ((detour ∪ rfe) ⨾ (ppo ∪ bob)) (issued T)) ∩₁
                           (dom_cond (⦗W_ex_acq⦘ ⨾ sb) (issued T)).

  Definition tc_coherent (T : trav_config) :=
    ⟪ ICOV  : Init ∩₁ E ⊆₁ covered T ⟫ /\
    ⟪ CC    : covered T ⊆₁ coverable T ⟫ /\
    ⟪ II    : issued  T ⊆₁ issuable T ⟫.


  Lemma same_trav_config_refl : reflexive same_trav_config.
  Proof. split; basic_solver. Qed.

  Lemma same_trav_config_sym : symmetric same_trav_config.
  Proof. unfold same_trav_config; split; ins; desf; symmetry; auto. Qed.

  Lemma same_trav_config_trans : transitive same_trav_config.
  Proof. unfold same_trav_config; split; ins; desf; etransitivity; eauto. Qed.

   Lemma traversal_mon T T'
        (ICOV : covered T ⊆₁ covered T')
        (IISS : issued  T ⊆₁ issued  T'):
    coverable T ⊆₁ coverable T' /\
    issuable  T ⊆₁ issuable T'.
  Proof.
    split.
by unfold coverable; rewrite ICOV, IISS.
by unfold issuable; rewrite ICOV, IISS.
  Qed.

Lemma next_n_init e T (TCCOH : tc_coherent T)
      (NEXT : next (covered T) e) :
  ~ Init e.
Proof.
unfold next,tc_coherent in *; desf.
unfolder in *; basic_solver 12.
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

  Add Parametric Relation : trav_config same_trav_config
      reflexivity proved by same_trav_config_refl
      symmetry proved by same_trav_config_sym
      transitivity proved by same_trav_config_trans
        as same_tc.
  
 Add Parametric Morphism : covered with signature
      same_trav_config ==> set_equiv as covered_more.
  Proof. by unfold same_trav_config; ins; split; ins; desf; apply H. Qed.

  Add Parametric Morphism : issued with signature
      same_trav_config ==> set_equiv as issued_more.
  Proof. by unfold same_trav_config; ins; desf; apply H1. Qed.
  

  Add Parametric Morphism : coverable with signature
      same_trav_config ==> set_equiv as coverable_more.
  Proof.
    unfold coverable, same_trav_config; split; ins; desf.
    all: unnw; try first [ rewrite <- H, <- H0 | rewrite H, H0].
    all: unfold set_equiv in *; unnw; intuition; basic_solver 12.
  Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)

  Lemma issued_in_issuable T (TCCOH : tc_coherent T):
    issued T ⊆₁ issuable T.
  Proof. apply TCCOH. Qed.

  Lemma issuableE T (TCCOH : tc_coherent T):
    issuable T ⊆₁ E.
  Proof. unfold issuable; basic_solver. Qed.

  Lemma issuedE T (TCCOH : tc_coherent T):
    issued T ⊆₁ E.
  Proof.
    rewrite (issued_in_issuable TCCOH).
    by apply issuableE.
  Qed.

  Lemma issuableW T (TCCOH : tc_coherent T):
    issuable T ⊆₁ W.
  Proof. unfold issuable; basic_solver. Qed.

  Lemma issuedW T (TCCOH : tc_coherent T):
    issued T ⊆₁ W.
  Proof.
    rewrite (issued_in_issuable TCCOH).
    by apply issuableW.
  Qed.

  Lemma covered_in_coverable T (TCCOH : tc_coherent T):
    covered T ⊆₁ coverable T.
  Proof.
    apply TCCOH.
  Qed.

  Lemma coverableE T (TCCOH : tc_coherent T):
    coverable T ⊆₁ E.
  Proof.
    unfold coverable; basic_solver.
  Qed.

  Lemma coveredE T (TCCOH : tc_coherent T):
    covered T ⊆₁ E.
  Proof.
    rewrite (covered_in_coverable TCCOH).
    by apply coverableE.
  Qed.

  Lemma w_coverable_issued T (TCCOH : tc_coherent T):
    W ∩₁ coverable T ⊆₁ issued T.
  Proof.
    unfold coverable; type_solver.
  Qed.

  Lemma w_covered_issued T (TCCOH : tc_coherent T):
    W ∩₁ covered T ⊆₁ issued T.
  Proof.
    rewrite (covered_in_coverable TCCOH).
    by apply w_coverable_issued.
  Qed.

Lemma init_issued T (TCCOH : tc_coherent T): is_init ∩₁ E ⊆₁ issued T.
Proof. 
unfolder; ins; desf.
apply (w_covered_issued TCCOH).
split.
by apply (init_w WF).
cdes TCCOH; unfolder in ICOV; basic_solver 21. 
Qed.

Lemma init_covered T (TCCOH : tc_coherent T): is_init ∩₁ E ⊆₁ covered T.
Proof. 
unfolder; ins; desf.
cdes TCCOH; unfolder in ICOV; basic_solver 21. 
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

  Lemma dom_sb_coverable T (TCCOH : tc_coherent T):
    dom_rel (sb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof.
    unfold coverable, dom_cond; basic_solver 21.
  Qed.

  Lemma sb_coverable T (TCCOH : tc_coherent T):
    sb ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ sb.
 Proof.
rewrite (dom_rel_helper (dom_sb_coverable TCCOH)).
basic_solver.
  Qed.

  Lemma dom_sb_covered T (TCCOH : tc_coherent T):
    dom_rel (sb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof.
  rewrite (covered_in_coverable TCCOH) at 1.
  seq_rewrite (dom_rel_helper (dom_sb_coverable TCCOH)).
  basic_solver.
  Qed.

  Lemma sb_covered T (TCCOH : tc_coherent T):
    sb ⨾ ⦗ covered T ⦘ ≡ ⦗ covered T ⦘ ⨾ sb ⨾ ⦗ covered T ⦘.
  Proof.
  rewrite (dom_rel_helper (dom_sb_covered TCCOH)).
  basic_solver.
  Qed.

  Lemma dom_rf_coverable T (TCCOH : tc_coherent T):
    dom_rel (rf ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof.
    unfold coverable, dom_cond.
    rewrite (dom_r (wf_rfD WF)).
    type_solver 40.
  Qed.

  Lemma dom_rf_covered T (TCCOH : tc_coherent T):
    dom_rel (rf ⨾ ⦗ covered  T ⦘) ⊆₁ issued T.
  Proof.
  rewrite (covered_in_coverable TCCOH).
apply (dom_rf_coverable TCCOH).
  Qed.

  Lemma rf_coverable T (TCCOH : tc_coherent T):
    rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ issued T ⦘ ⨾ rf.
  Proof.
rewrite (dom_rel_helper (dom_rf_coverable TCCOH)).
basic_solver.
  Qed.

  Lemma rf_covered T (TCCOH : tc_coherent T):
    rf ⨾ ⦗ covered T ⦘ ≡ ⦗ issued T ⦘ ⨾ rf ⨾ ⦗ covered T ⦘.
  Proof.
rewrite (dom_rel_helper (dom_rf_covered TCCOH)).
basic_solver.
  Qed.

  Lemma sbCsbI_CsbI  T (TCCOH : tc_coherent T) :
    sb ⨾ ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⊆
    ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⨾ sb.
  Proof.
    rewrite id_union, !seq_union_r, !seq_union_l.
    apply union_mori.
    { rewrite sb_covered; eauto. basic_solver. }
    generalize (@sb_trans G). basic_solver 10.
  Qed.

  Lemma issuable_next_w T (TCCOH : tc_coherent T):
    W ∩₁ next (covered T) ⊆₁ issuable T.
  Proof.
    unfold issuable, next.
    rewrite fwbob_in_bob, bob_in_sb.
    rewrite (dom_l (wf_detourD WF)).
    rewrite (ppo_in_sb WF), detour_in_sb.
    arewrite (rfe ⊆ rf).
    rewrite (W_ex_acq_in_W WF).
    rels.
    rewrite seq_union_l, dom_cond_union, !seqA.
    generalize (@sb_trans G); ins.
    relsf; splits; try basic_solver.
    { intros x [y HH]; apply HH. }
    { unfold dom_cond; unfolder; ins; desf.
      eapply w_covered_issued; basic_solver 12. }
    { unfold dom_cond; unfolder; ins; desf.
      generalize (dom_rf_covered TCCOH); basic_solver 12. }
    unfold dom_cond; unfolder; ins; desf.
    eapply w_covered_issued; basic_solver 12.
  Qed.

  Lemma dom_rfe_ppo_issued T (TCCOH : tc_coherent T):
    dom_rel (rfe ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof.
    rewrite (issued_in_issuable TCCOH) at 1.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond ((detour ∪ rfe) ⨾ (ppo ∪ bob)) (issued T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA, dom_cond_elim1; basic_solver 21.
  Qed.

  Lemma dom_rfe_acq_sb_issued T (TCCOH : tc_coherent T):
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof.
    rewrite (issued_in_issuable TCCOH) at 1.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond ((detour ∪ rfe) ⨾ (ppo ∪ bob)) (issued T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA, dom_cond_elim1; [basic_solver 21|].
    unfold imm_common.bob; basic_solver 21.
  Qed.

  Lemma dom_wex_sb_issued T (TCCOH : tc_coherent T):
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof.
    rewrite (issued_in_issuable TCCOH) at 1.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond (⦗W_ex_acq⦘ ⨾ sb) (issued T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
      by rewrite dom_cond_elim1; [basic_solver 21|].
  Qed.

Lemma rf_rmw_issued_rfi_rmw_issued T (TCCOH : tc_coherent T): 
  (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⨾ (rf ⨾ rmw)＊.
Proof.
eapply rt_ind_left with (P:= fun r => r ⨾ ⦗issued T⦘).
by eauto with hahn.
basic_solver 12.
intros k H; rewrite !seqA.
sin_rewrite H.
rewrite rfi_union_rfe at 1; relsf; unionL.
rewrite <- seqA; seq_rewrite <- ct_begin; basic_solver 12.
rewrite rtE at 2.
relsf; unionR left.
arewrite ((rfi ⨾ rmw)＊ ⊆ (rfi ⨾ rmw)＊ ∩ (rfi ⨾ rmw)＊) at 1.
rewrite (rmw_in_sb WF) at 2; arewrite (rfi ⊆ sb) at 1.
generalize (@sb_trans G); ins; relsf.
arewrite (rfi ⊆ rf).
rewrite (dom_l (wf_rmwD WF)) at 1; rewrite !seqA.
rewrite (issued_in_issuable TCCOH) at 1.
unfold issuable.
arewrite (⦗E ∩₁ W ∩₁ dom_cond fwbob (covered T) ∩₁
             dom_cond ((detour ∪ rfe) ⨾ (ppo ∪ bob)) (issued T) ∩₁
             dom_cond (⦗W_ex_acq⦘ ⨾ sb) (issued T)⦘
⊆ ⦗W⦘ ⨾ ⦗dom_cond ((detour ∪ rfe) ⨾ (ppo ∪ bob)) (issued T)⦘).
{ rewrite seq_eqv. apply eqv_rel_mori.
  intros x HH. split; apply HH. }
rewrite <- !seqA.
sin_rewrite dom_cond_elim1.
- arewrite_id ⦗W⦘.
  arewrite (rfe ⊆ rf).
  arewrite_id ⦗R_ex⦘.
  arewrite (sb^? ∩ (rf ⨾ rmw)＊ ⊆ (rf ⨾ rmw)＊).
  relsf.
  arewrite (⦗issued T⦘ ⨾ rf ⨾ rmw ⊆ ⦗issued T⦘ ⨾ (rf ⨾ rmw)＊).
  relsf.
- arewrite (sb^? ∩ (rf ⨾ rmw)＊ ⊆ sb^?).
  unfold imm_common.ppo.
  rewrite <- ct_step.
  rewrite (rmw_in_sb WF).
  generalize (@sb_trans G) R_ex_in_R; basic_solver 21.
Qed.

Lemma wex_rfi_rfe_rmw_issuable_is_issued T (TCCOH : tc_coherent T):
  dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issuable T ⦘) ⊆₁ issued T.
Proof.
  rewrite seq_union_l. rewrite dom_union.
  apply set_subset_union_l; split.
  { rewrite seqA. rewrite WF.(rfi_in_sbloc'). rewrite WF.(rmw_in_sb).
    arewrite (sb ∩ same_loc ⨾ sb ⊆ sb).
    { generalize (@sb_trans G). basic_solver. }
    rewrite <- seqA.
    intros x [y H]. apply seq_eqv_r in H. destruct H as [H II].
    eapply II. eexists; apply seq_eqv_r; split; eauto. }
  rewrite WF.(rmw_in_ppo).
  rewrite <- seqA.
  intros x [y H]. apply seq_eqv_r in H. destruct H as [H II].
  destruct II as [II _].
  eapply II. eexists; apply seq_eqv_r; split; eauto.
  destruct H as [z [HX HY]].
  exists z; split. by right. by left.
Qed.

Lemma rf_rmw_issued T (TCCOH : tc_coherent T)
      (ACQEX : W_ex ⊆₁ W_ex_acq):
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆
    (rf ⨾ rmw ⨾ ⦗issued T⦘)＊.
Proof.
rewrite rmw_W_ex at 1.
rewrite ACQEX.
rewrite rt_begin.
relsf; unionL; [basic_solver|].
rewrite !seqA.
rewrite <- !(seqA rf rmw).
seq_rewrite <- rt_seq_swap.
arewrite_id ⦗W_ex_acq⦘ at 2; rels.
eapply rt_ind_right with (P:= fun r => rf ⨾ rmw ⨾ r ⨾ ⦗issued T⦘).
by eauto with hahn.
by rewrite rtE, <- ct_step; basic_solver 12.
intros k H.
rewrite rfi_union_rfe at 2; relsf; unionL.
* rewrite !seqA.
  arewrite (⦗W_ex_acq⦘ ⨾ rfi ⨾ rmw ⨾ ⦗issued T⦘ ⊆ ⦗issued T⦘ ⨾ rfi ⨾ rmw ⨾ ⦗issued T⦘).
  { arewrite (⦗issued T⦘ ⊆ ⦗issued T⦘ ⨾  ⦗issued T⦘) at 1.
    basic_solver.
    rewrite (issued_in_issuable TCCOH) at 1.
    unfold issuable.
    assert (A: rfi ⨾ rmw ⊆ sb).
    by arewrite (rfi ⊆ sb); rewrite (rmw_in_sb WF); generalize (@sb_trans G); ins; relsf.
    unfold dom_cond.
    revert A.
    basic_solver 40. }
  arewrite (rfi ⊆ rf).
  sin_rewrite H.
  rewrite rt_end at 2.
  basic_solver 12.
* arewrite_id ⦗W_ex_acq⦘; rels.
  arewrite (rfe ⨾ rmw ⨾ ⦗issued T⦘ ⊆ ⦗issued T⦘ ⨾ rfe ⨾ rmw ⨾ ⦗issued T⦘).
  { arewrite (⦗issued T⦘ ⊆ ⦗issued T⦘ ⨾  ⦗issued T⦘) at 1.
    basic_solver.
    rewrite (issued_in_issuable TCCOH) at 1.
    unfold issuable.
    generalize (rmw_in_ppo WF).
    unfold dom_cond.
    basic_solver 40. }
  arewrite (rfe ⊆ rf).
  sin_rewrite H.
  rewrite rt_end at 2.
  basic_solver 12.
Qed.

Lemma dom_sb_loc_issued T (TCCOH : tc_coherent T):
  dom_rel (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof.
rewrite (issued_in_issuable TCCOH).
arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
{ unfold issuable. basic_solver 10. }
rewrite <- !seqA.
rewrite dom_cond_elim1; [basic_solver 21|].
unfold imm_common.fwbob.
basic_solver 12.
Qed.

Lemma sb_loc_issued T (TCCOH : tc_coherent T) :
  ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘ ⊆ 
    ⦗covered T⦘ ⨾ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘.
Proof.
seq_rewrite (dom_rel_helper (dom_sb_loc_issued TCCOH)).
basic_solver.
Qed.

Lemma dom_F_sb_issued T (TCCOH : tc_coherent T):
  dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof.
rewrite (issued_in_issuable TCCOH).
arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
{ unfold issuable. basic_solver 10. }
rewrite <- !seqA.
rewrite dom_cond_elim1; [basic_solver 21|].
unfold imm_common.fwbob.
basic_solver 12.
Qed.

Lemma F_sb_issued T (TCCOH : tc_coherent T) :
  ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb.
Proof.
seq_rewrite (dom_rel_helper (dom_F_sb_issued TCCOH)).
basic_solver.
Qed.

Lemma dom_release_issued T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  dom_rel (release ⨾ ⦗ issued T ⦘) ⊆₁ covered T.
Proof.
unfold imm_s_hb.release, imm_s_hb.rs.
rewrite !seqA.
sin_rewrite rf_rmw_issued_rfi_rmw_issued; [|done].
rewrite (dom_r (wf_rmwD WF)) at 1.
arewrite (⦗W⦘ ⨾ (rfi ⨾ rmw ⨾ ⦗W⦘)＊ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗W⦘).
{ rewrite rtE; relsf; unionL; [basic_solver|].
  rewrite <- seqA; rewrite inclusion_ct_seq_eqv_r; basic_solver. }
rewrite (rmw_in_sb_loc WF) at 1; rewrite (rfi_in_sbloc' WF).
generalize (@sb_same_loc_trans G); ins; relsf.
rewrite !crE; relsf; unionL; splits.
- revert RELCOV; basic_solver 21.
- generalize (dom_sb_loc_issued TCCOH); basic_solver 21.
- arewrite (Rel ⊆₁ Acq/Rel) by mode_solver.
generalize (dom_F_sb_issued TCCOH);  basic_solver 40.
- arewrite (Rel ⊆₁ Acq/Rel) by mode_solver.
generalize (@sb_trans G).
generalize (dom_F_sb_issued TCCOH);  basic_solver 40.
Qed.

Lemma release_issued T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  release ⨾ ⦗ issued T ⦘ ⊆ ⦗covered T⦘ ⨾ release.
Proof.
seq_rewrite (dom_rel_helper (dom_release_issued TCCOH RELCOV)).
basic_solver.
Qed.

Lemma dom_release_rf_coverable T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  dom_rel (release ⨾ rf ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
Proof.
generalize (dom_release_issued TCCOH RELCOV).
generalize (dom_rf_coverable TCCOH).
basic_solver 21.
Qed.

Lemma release_rf_coverable T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  release ⨾ rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
Proof.
seq_rewrite (dom_rel_helper (dom_release_rf_coverable TCCOH RELCOV)).
basic_solver.
Qed.

Lemma release_rf_covered T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  release ⨾ rf ⨾ ⦗ covered T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply release_rf_coverable.
Qed.

Lemma dom_sb_W_rel_issued T (TCCOH : tc_coherent T) :
  dom_rel (sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof.
rewrite (issued_in_issuable TCCOH).
arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
{ unfold issuable. basic_solver 10. }
rewrite <- !seqA.
rewrite dom_cond_elim1; [basic_solver 21|].
unfold imm_common.fwbob.
basic_solver 12.
Qed.

Lemma sb_W_rel_issued T (TCCOH : tc_coherent T) :
  sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ sb ⨾ ⦗W ∩₁ Rel⦘.
Proof.
seq_rewrite (dom_rel_helper (dom_sb_W_rel_issued TCCOH)).
basic_solver.
Qed.

Lemma dom_sw_coverable T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  dom_rel (sw ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
Proof.
unfold imm_s_hb.sw.
generalize (dom_sb_coverable TCCOH).
generalize (dom_release_rf_coverable TCCOH RELCOV).
generalize (covered_in_coverable TCCOH).
basic_solver 21.
Qed.

Lemma sw_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  sw ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
Proof.
seq_rewrite (dom_rel_helper (dom_sw_coverable TCCOH RELCOV)).
basic_solver.
Qed.

Lemma sw_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  sw ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply sw_coverable.
Qed.

Lemma dom_sc_coverable T (TCCOH : tc_coherent T):
  dom_rel (sc ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
Proof.
  cdes IMMCON.
  rewrite (dom_r (@wf_scD G sc Wf_sc)).
  unfold coverable, dom_cond; type_solver 42.
Qed.

Lemma dom_sc_covered T (TCCOH : tc_coherent T):
  dom_rel (sc ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
Proof.
  rewrite (covered_in_coverable TCCOH) at 1.
  seq_rewrite (dom_rel_helper (dom_sc_coverable TCCOH)).
  basic_solver.
Qed.

Lemma sc_coverable  T (TCCOH : tc_coherent T):
  sc ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
Proof.
seq_rewrite (dom_rel_helper (dom_sc_coverable TCCOH)).
basic_solver.
Qed.

Lemma sc_sb_I_dom_C T (TCCOH : tc_coherent T) :
  dom_rel (sc ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof.
  cdes IMMCON.
  rewrite (dom_r Wf_sc.(wf_scD)).
  unfolder. ins. desf.
  cdes TCCOH.
  assert (covered T z) as AA.
  2: { apply CC in AA. red in AA.
       unfolder in AA. desf.
       1,2: type_solver.
       eapply AA2. eexists.
       apply seq_eqv_r. split; eauto. }
  eapply II; eauto.
  eexists. apply seq_eqv_r. split; eauto.
  apply sb_from_f_in_fwbob.
  apply seq_eqv_l. split; [split|]; auto.
  mode_solver.
Qed.

Lemma sc_covered  T (TCCOH : tc_coherent T):
  sc ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply sc_coverable.
Qed.

Lemma hb_coverable  T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  hb ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
Proof.
unfold imm_s_hb.hb.
assert (A: (sb ∪ sw) ⨾ ⦗coverable T⦘ ⊆ ⦗covered T⦘ ⨾ (sb ∪ sw)⁺).
{ relsf.
rewrite (sb_coverable TCCOH), (sw_coverable TCCOH RELCOV).
rewrite <- ct_step; basic_solver. }
unfold imm_s_hb.hb.
eapply ct_ind_left with (P:= fun r => r ⨾ ⦗coverable T⦘); eauto with hahn.
intros k H; rewrite !seqA, H.
    rewrite (covered_in_coverable TCCOH) at 1.
sin_rewrite A.
arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw)＊) at 1.
relsf.
Qed.


Lemma dom_hb_coverable T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  dom_rel (hb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
Proof.
rewrite (hb_coverable TCCOH RELCOV); basic_solver 10.
Qed.

Lemma hb_covered  T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  hb ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply hb_coverable.
Qed.

Lemma dom_urr_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  dom_rel (urr l ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
Proof.
unfold CombRelations.urr.
generalize (dom_hb_coverable TCCOH RELCOV).
generalize (dom_sc_coverable TCCOH).
generalize (dom_rf_coverable TCCOH).
generalize (covered_in_coverable TCCOH).
generalize (w_coverable_issued TCCOH).
basic_solver 21.
Qed.

Lemma urr_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  urr l ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
Proof.
seq_rewrite (dom_rel_helper (@dom_urr_coverable T TCCOH RELCOV l)).
basic_solver.
Qed.

Lemma urr_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  urr l ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply urr_coverable.
Qed.

Lemma dom_c_acq_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  dom_rel (c_acq i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
Proof.
unfold CombRelations.c_acq.
generalize (@dom_urr_coverable T TCCOH RELCOV l).
generalize (covered_in_coverable TCCOH).
generalize (dom_release_issued TCCOH RELCOV).
generalize (dom_rf_coverable TCCOH).
basic_solver 21.
Qed.

Lemma c_acq_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  c_acq i l A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
Proof.
seq_rewrite (dom_rel_helper (@dom_c_acq_coverable T TCCOH RELCOV i l A)).
basic_solver.
Qed.

Lemma c_acq_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  c_acq i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply c_acq_coverable.
Qed.


Lemma dom_c_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  dom_rel (c_cur i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
Proof.
unfold CombRelations.c_cur.
generalize (@dom_urr_coverable T TCCOH RELCOV l).
basic_solver 21.
Qed.

Lemma c_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  c_cur i l A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
Proof.
seq_rewrite (dom_rel_helper (@dom_c_cur_coverable T TCCOH RELCOV i l A)).
basic_solver.
Qed.


Lemma c_cur_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l A:
  c_cur i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply c_cur_coverable.
Qed.

Lemma dom_c_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l l' A:
  dom_rel (c_rel i l l' A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
Proof.
unfold CombRelations.c_rel.
generalize (@dom_urr_coverable T TCCOH RELCOV l).
basic_solver 21.
Qed.


Lemma c_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l l' A:
  c_rel i l l' A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
Proof.
seq_rewrite (dom_rel_helper (@dom_c_rel_coverable T TCCOH RELCOV i l l' A)).
basic_solver.
Qed.


Lemma c_rel_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      i l l' A:
  c_rel i l l' A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply c_rel_coverable.
Qed.

Lemma t_acq_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l thread:
    t_acq thread l (coverable T) ⊆₁ issued T.
Proof.
unfold CombRelations.t_acq.
rewrite (dom_r (wf_c_acqD G sc thread l (coverable T))).
arewrite (⦗(Tid_ thread ∪₁ Init) ∩₁ coverable T⦘ ⊆ ⦗coverable T⦘) by basic_solver.
rewrite (c_acq_coverable TCCOH RELCOV).
basic_solver.
Qed.

Lemma t_acq_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l thread:
    t_acq thread l (covered T) ⊆₁ issued T.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply t_acq_coverable.
Qed.

Lemma t_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l thread:
    t_cur thread l (coverable T) ⊆₁ issued T.
Proof.
  etransitivity; [by apply t_cur_in_t_acq|].
  by apply t_acq_coverable.
Qed.

Lemma t_cur_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l thread:
    t_cur thread l (covered T) ⊆₁ issued T.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply t_cur_coverable.
Qed.

Lemma t_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l l' thread:
    t_rel thread l l' (coverable T) ⊆₁ issued T.
Proof.
  etransitivity; [by apply t_rel_in_t_cur|].
  by apply t_cur_coverable.
Qed.

Lemma t_rel_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      l l' thread:
    t_rel thread l l' (covered T) ⊆₁ issued T.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply t_rel_coverable.
Qed.

Lemma S_tm_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  S_tm l (coverable T) ⊆₁ issued T.
Proof.
unfold CombRelations.S_tm, CombRelations.S_tmr.
generalize (@dom_hb_coverable T TCCOH RELCOV).
generalize (w_coverable_issued TCCOH).
generalize (covered_in_coverable TCCOH).
generalize (dom_release_issued TCCOH RELCOV).
generalize (dom_rf_coverable TCCOH).
basic_solver 21.
Qed.


Lemma S_tm_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  S_tm l (covered T) ⊆₁ issued T.
Proof.
    rewrite (covered_in_coverable TCCOH) at 1.
    by apply S_tm_coverable.
Qed.

Lemma msg_rel_issued T (TCCOH : tc_coherent T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
  dom_rel (msg_rel l ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
Proof.
unfold CombRelations.msg_rel.
generalize (dom_release_issued TCCOH RELCOV).
generalize (@dom_urr_coverable T TCCOH RELCOV l).
generalize (covered_in_coverable TCCOH).
basic_solver 21.
Qed.

Lemma exists_ncov T thread (TCCOH : tc_coherent T) :
  exists n, ~ covered T (ThreadEvent thread n).
Proof.
  destruct (exists_nE G thread) as [n HH].
  exists n. intros CC. apply HH.
  eapply coveredE; eauto.
Qed.

Section HbProps.
Variable T : trav_config.
Variable TCCOH : tc_coherent T.

Notation "'C'" := (covered T).
Notation "'I'" := (issued  T).

Lemma sw_in_Csw_sb (RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
  sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ sw ∪ sb.
Proof.
  assert (forall (s : actid -> Prop), s ∪₁ set_compl s ≡₁ fun _ => True) as AA.
  { split; [basic_solver|].
    unfolder. ins. apply classic. }
  rewrite !id_union. rewrite seq_union_r. 
  unionL.
  { rewrite sw_covered; eauto. basic_solver. }
  arewrite (sw ⊆ ⦗ C ∪₁ set_compl C ⦘ ⨾ sw) at 1.
  { rewrite AA. by rewrite seq_id_l. }
  rewrite id_union. relsf.
  apply union_mori; [basic_solver|].
  unfold imm_s_hb.sw.
  arewrite ((sb ⨾ ⦗F⦘)^? ⊆ sb ⨾ ⦗F⦘ ∪ ⦗ fun _ => True ⦘) by basic_solver.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite !seqA.
    seq_rewrite <- !id_inter. rewrite <- !set_interA.
    arewrite (sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
              ⦗ C ⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘).
    { unfolder. ins. desf; splits; auto.
      2,4: by do 2 eexists; splits; eauto.
      2: eapply TCCOH.(dom_sb_covered).
      2: eexists; apply seq_eqv_r; split; eauto.
      all: match goal with H : I _ |- _ => apply TCCOH in H; apply H end.
      all: eexists; apply seq_eqv_r; split; eauto.
      { apply sb_to_f_in_fwbob. apply seq_eqv_r. split; [|split]; auto.
        mode_solver. }
      apply sb_from_f_in_fwbob. apply seq_eqv_l. split; [split|]; auto.
      mode_solver. }
    sin_rewrite release_rf_covered; eauto.
    basic_solver. }
  rewrite seq_id_l.
  arewrite (rf ⊆ ⦗ I ∪₁ set_compl I⦘ ⨾ rf).
  { rewrite AA. basic_solver. }
  rewrite id_union. relsf.
  unionL.
  { sin_rewrite release_issued; eauto. basic_solver. }
  rewrite rfi_union_rfe. relsf.
  unionL.
  2: { arewrite (⦗set_compl I⦘ ⨾ rfe ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ ∅₂).
       2: basic_solver.
       seq_rewrite <- !id_inter.
       unfolder. ins. desf.
       { match goal with H : I _ |- _ => apply TCCOH.(issuedW) in H end.
         match goal with H : rfe _ _ |- _ =>
                         apply wf_rfeD in H; auto; (destruct_seq H as [XX YY])
         end.
         type_solver. }
       match goal with H : ~ (I _) |- _ => apply H end.
       eapply dom_rfe_acq_sb_issued; eauto.
       eexists. eexists. split; eauto.
       apply seq_eqv_l. split; [split|]; auto.
       2: { apply seq_eqv_r. split; eauto. }
       match goal with H : rfe _ _ |- _ =>
                       apply wf_rfeD in H; auto; (destruct_seq H as [XX YY]); auto
       end. }
  unfold imm_s_hb.release, rs.
  arewrite
    (⦗set_compl C⦘ ⨾ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊) ⊆
     ⦗set_compl C⦘ ⨾ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾
       (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ ⦗ set_compl I ⦘ ⨾ (⦗ set_compl I ⦘ ⨾ rf ⨾ rmw)＊)).
  { intros x y HH.
    destruct_seq_l HH as NC.
    do 4 apply seqA in HH. destruct HH as [v [HH SUF]].
    apply seq_eqv_l. split; auto.
    
    Ltac _ltt :=
      apply seqA;
      apply seqA with (r1 := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?);
      apply seqA with (r1 := (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?) ⨾ ⦗W⦘);
      apply seqA with (r1 := ((⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?) ⨾ ⦗W⦘) ⨾ (sb ∩ same_loc)^?).
    
    _ltt.
    exists v. split.
    { generalize HH. basic_solver. }
    assert (release x v) as REL.
    { unfold imm_s_hb.release, rs. _ltt.
      eexists. split; eauto. apply rt_refl. }
    apply seq_eqv_l. split.
    { intros II. apply NC. eapply dom_release_issued; eauto.
      eexists. apply seq_eqv_r. split; eauto. }
    assert (codom_rel (⦗ set_compl C ⦘ ⨾ release) v) as XX.
    { exists x. apply seq_eqv_l. split; auto. }
    assert (~ I v) as NI.
    { intros II. apply NC. eapply dom_release_issued; eauto.
      eexists. apply seq_eqv_r. split; eauto. }
    clear x NC HH REL.
    induction SUF.
    2: by apply rt_refl.
    { apply rt_step. apply seq_eqv_l. split; auto. }
    eapply rt_trans.
    { by apply IHSUF1. }
    assert (codom_rel (⦗set_compl C⦘ ⨾ release) y) as YY.
    { destruct XX as [v XX]. destruct_seq_l XX as CC.
      eexists. apply seq_eqv_l. split; eauto.
      apply release_rf_rmw_steps.
      eexists. split; eauto. }
    apply IHSUF2; auto.
    intros II.
    destruct YY as [v YY]. destruct_seq_l YY as CC. apply CC.
    eapply dom_release_issued; eauto.
    eexists. apply seq_eqv_r. split; eauto. }
  arewrite ((⦗set_compl I⦘ ⨾ rf ⨾ rmw)＊ ⨾
             ⦗set_compl I⦘ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
            sb^? ⨾ ⦗set_compl I⦘ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘).
  2: { unfold Execution.rfi.
       generalize (@sb_trans G). basic_solver. }
  intros x y [v [HH XX]].
  eexists. split; [|by eauto].
  assert (dom_rel (sb ⨾ ⦗ I ⦘) v) as VV.
  { generalize XX (@sb_trans G). unfold Execution.rfi. basic_solver 40. }
  clear y XX.
  induction HH as [x y HH| | ].
  2: by apply r_refl.
  { apply r_step.
    destruct_seq_l HH as NIX. destruct HH as [v [RF RMW]].
    apply rfi_union_rfe in RF. destruct RF as [RF|RF].
    { by eapply (@sb_trans G); [apply RF|apply rmw_in_sb]. }
    exfalso.
    destruct VV as [z VV]. destruct_seq_r VV as AZ.
    set (IZ := AZ).
    apply TCCOH in IZ.
    apply NIX. destruct IZ as [IZ _]. apply IZ.
    eexists.
    apply seq_eqv_r. split; eauto.
    eexists. split.
    { eby right. }
    left.
    apply seq_eqv_l. split; eauto.
    { apply (dom_r WF.(wf_rfeD)) in RF. apply seq_eqv_r in RF. desf. }
    apply seq_eqv_r. split; eauto.
    2: { eapply issuedW; eauto. }
    apply ct_step. left; right.
    apply seq_eqv_l. split; auto.
    { apply (dom_l WF.(wf_rmwD)) in RMW. apply seq_eqv_l in RMW. desf. }
    eapply sb_trans; eauto. by apply rmw_in_sb. }
  specialize (IHHH2 VV).
  eapply (transitive_cr (@sb_trans G) _ IHHH2); eauto.

  Unshelve.
  apply IHHH1. generalize VV (@sb_trans G) IHHH2. basic_solver 10.
Qed.

Lemma hb_in_Chb_sb (RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
  hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof.
  unfold imm_s_hb.hb.
  intros x y HH.
  destruct_seq_r HH as DOM.
  apply clos_trans_tn1 in HH.
  induction HH as [y [HH|HH]|y z AA].
  { by right. }
  { assert ((⦗C⦘ ⨾ sw ∪ sb) x y) as [ZZ|ZZ].
    3: by right.
    2: { destruct_seq_l ZZ as CX.
         left. apply seq_eqv_l. split; auto.
         apply ct_step. by right. }
    apply sw_in_Csw_sb; auto. apply seq_eqv_r. splits; auto. }
  assert (sb y z -> (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as DOMY.
  { intros SB.
    destruct DOM as [DOM|DOM].
    2: { right. generalize (@sb_trans G) SB DOM. basic_solver 10. }
    left.
    eapply dom_sb_covered; eauto. eexists.
    apply seq_eqv_r. split; eauto. }

  assert ((C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as BB.
  2: { set (CC:=BB). apply IHHH in CC.
       destruct CC as [CC|CC].
       { left.
         destruct_seq_l CC as XX.
         apply seq_eqv_l. split; auto.
         apply ct_ct. eexists. split; eauto. }
       destruct AA as [AA|AA].
       { right. eapply (@sb_trans G); eauto. }
       assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
       { apply seq_eqv_r. by split. }
       eapply sw_in_Csw_sb in DD; auto.
       destruct DD as [DD|DD].
       2: { right. eapply (@sb_trans G); eauto. }
       left.
       apply seq_eqv_l. split.
       2: { apply ct_ct. eexists.
            split; apply ct_step; [left|right]; eauto. }
       assert (C y) as CY.
       { by destruct_seq_l DD as XX. }
       eapply dom_sb_covered; eauto. eexists.
       apply seq_eqv_r. split; eauto. }
  destruct AA as [|AA]; [by intuition|].
  assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
  { apply seq_eqv_r. by split. }
  eapply sw_in_Csw_sb in DD; auto.
  destruct DD as [DD|]; [|by intuition].
  left. by destruct_seq_l DD as CY.
Qed.
End HbProps.

End TraversalConfig.
