Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_rfrmw.
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

  Notation "'ar'" := (ar G sc).

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
                           (dom_cond (<|W|> ;; ar⁺) (issued T)).

  Definition tc_coherent (T : trav_config) :=
    ⟪ ICOV  : Init ∩₁ E ⊆₁ covered T ⟫ /\
    ⟪ CC    : covered T ⊆₁ coverable T ⟫ /\
    ⟪ II    : issued  T ⊆₁ issuable T ⟫.


  Lemma same_trav_config_refl : reflexive same_trav_config.
  Proof using. split; basic_solver. Qed.

  Lemma same_trav_config_sym : symmetric same_trav_config.
  Proof using. unfold same_trav_config; split; ins; desf; symmetry; auto. Qed.

  Lemma same_trav_config_trans : transitive same_trav_config.
  Proof using. unfold same_trav_config; split; ins; desf; etransitivity; eauto. Qed.

   Lemma traversal_mon T T'
        (ICOV : covered T ⊆₁ covered T')
        (IISS : issued  T ⊆₁ issued  T'):
    coverable T ⊆₁ coverable T' /\
    issuable  T ⊆₁ issuable T'.
  Proof using.
    split.
by unfold coverable; rewrite ICOV, IISS.
by unfold issuable; rewrite ICOV, IISS.
  Qed.

Lemma next_n_init e T (TCCOH : tc_coherent T)
      (NEXT : next (covered T) e) :
  ~ Init e.
Proof using.
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
  Proof using. by unfold same_trav_config; ins; split; ins; desf; apply H. Qed.

  Add Parametric Morphism : issued with signature
      same_trav_config ==> set_equiv as issued_more.
  Proof using. by unfold same_trav_config; ins; desf; apply H1. Qed.
  

  Add Parametric Morphism : coverable with signature
      same_trav_config ==> set_equiv as coverable_more.
  Proof using.
    unfold coverable, same_trav_config; split; ins; desf.
    all: unnw; try first [ rewrite <- H, <- H0 | rewrite H, H0].
    all: unfold set_equiv in *; unnw; intuition; basic_solver 12.
  Qed.


(******************************************************************************)
(** **   *)
(******************************************************************************)

  Lemma issued_in_issuable T (TCCOH : tc_coherent T):
    issued T ⊆₁ issuable T.
  Proof using. apply TCCOH. Qed.

  Lemma issuableE T (TCCOH : tc_coherent T):
    issuable T ⊆₁ E.
  Proof using. unfold issuable; basic_solver. Qed.

  Lemma issuedE T (TCCOH : tc_coherent T):
    issued T ⊆₁ E.
  Proof using.
    rewrite (issued_in_issuable TCCOH).
    by apply issuableE.
  Qed.

  Lemma issuableW T (TCCOH : tc_coherent T):
    issuable T ⊆₁ W.
  Proof using. unfold issuable; basic_solver. Qed.

  Lemma issuedW T (TCCOH : tc_coherent T):
    issued T ⊆₁ W.
  Proof using.
    rewrite (issued_in_issuable TCCOH).
    by apply issuableW.
  Qed.

  Lemma covered_in_coverable T (TCCOH : tc_coherent T):
    covered T ⊆₁ coverable T.
  Proof using.
    apply TCCOH.
  Qed.

  Lemma coverableE T (TCCOH : tc_coherent T):
    coverable T ⊆₁ E.
  Proof using.
    unfold coverable; basic_solver.
  Qed.

  Lemma coveredE T (TCCOH : tc_coherent T):
    covered T ⊆₁ E.
  Proof using.
    rewrite (covered_in_coverable TCCOH).
    by apply coverableE.
  Qed.

  Lemma w_coverable_issued T (TCCOH : tc_coherent T):
    W ∩₁ coverable T ⊆₁ issued T.
  Proof using.
    unfold coverable; type_solver.
  Qed.

  Lemma w_covered_issued T (TCCOH : tc_coherent T):
    W ∩₁ covered T ⊆₁ issued T.
  Proof using.
    rewrite (covered_in_coverable TCCOH).
    by apply w_coverable_issued.
  Qed.

Lemma init_issued T (TCCOH : tc_coherent T): is_init ∩₁ E ⊆₁ issued T.
Proof using WF. 
unfolder; ins; desf.
apply (w_covered_issued TCCOH).
split.
by apply (init_w WF).
cdes TCCOH; unfolder in ICOV; basic_solver 21. 
Qed.

Lemma init_covered T (TCCOH : tc_coherent T): is_init ∩₁ E ⊆₁ covered T.
Proof using. 
unfolder; ins; desf.
cdes TCCOH; unfolder in ICOV; basic_solver 21. 
Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

  Lemma dom_sb_coverable T (TCCOH : tc_coherent T):
    dom_rel (sb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using.
    unfold coverable, dom_cond; basic_solver 21.
  Qed.

  Lemma sb_coverable T (TCCOH : tc_coherent T):
    sb ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ sb.
 Proof using.
rewrite (dom_rel_helper (dom_sb_coverable TCCOH)).
basic_solver.
  Qed.

  Lemma dom_sb_covered T (TCCOH : tc_coherent T):
    dom_rel (sb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using.
  rewrite (covered_in_coverable TCCOH) at 1.
  seq_rewrite (dom_rel_helper (dom_sb_coverable TCCOH)).
  basic_solver.
  Qed.

  Lemma sb_covered T (TCCOH : tc_coherent T):
    sb ⨾ ⦗ covered T ⦘ ≡ ⦗ covered T ⦘ ⨾ sb ⨾ ⦗ covered T ⦘.
  Proof using.
  rewrite (dom_rel_helper (dom_sb_covered TCCOH)).
  basic_solver.
  Qed.

  Lemma dom_rf_coverable T (TCCOH : tc_coherent T):
    dom_rel (rf ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF.
    unfold coverable, dom_cond.
    rewrite (dom_r (wf_rfD WF)).
    type_solver 40.
  Qed.

  Lemma dom_rf_covered T (TCCOH : tc_coherent T):
    dom_rel (rf ⨾ ⦗ covered  T ⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (covered_in_coverable TCCOH).
    apply (dom_rf_coverable TCCOH).
  Qed.

  Lemma rf_coverable T (TCCOH : tc_coherent T):
    rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ issued T ⦘ ⨾ rf.
  Proof using WF.
    rewrite (dom_rel_helper (dom_rf_coverable TCCOH)).
    basic_solver.
  Qed.

  Lemma rf_covered T (TCCOH : tc_coherent T):
    rf ⨾ ⦗ covered T ⦘ ≡ ⦗ issued T ⦘ ⨾ rf ⨾ ⦗ covered T ⦘.
  Proof using WF.
rewrite (dom_rel_helper (dom_rf_covered TCCOH)).
basic_solver.
  Qed.

  Lemma dom_sc_coverable T (TCCOH : tc_coherent T):
    dom_rel (sc ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using IMMCON.
    cdes IMMCON.
    rewrite (dom_r (@wf_scD G sc Wf_sc)).
    unfold coverable, dom_cond; type_solver 42.
  Qed.

  Lemma dom_sc_covered T (TCCOH : tc_coherent T):
    dom_rel (sc ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
    seq_rewrite (dom_rel_helper (dom_sc_coverable TCCOH)).
    basic_solver.
  Qed.

  Lemma sc_coverable  T (TCCOH : tc_coherent T):
    sc ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
  Proof using IMMCON.
    seq_rewrite (dom_rel_helper (dom_sc_coverable TCCOH)).
    basic_solver.
  Qed.

  Lemma sc_covered  T (TCCOH : tc_coherent T):
    sc ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
  Proof using IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply sc_coverable.
  Qed.

  Lemma ar_C_in_CI T (TCCOH : tc_coherent T) :
    dom_rel (ar ⨾ ⦗covered T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON.
    unfold imm_s.ar.
    rewrite !seq_union_l.
    rewrite WF.(ar_int_in_sb).
    arewrite (rfe ⊆ rf).
    rewrite TCCOH.(sb_covered), TCCOH.(rf_covered).
    rewrite TCCOH.(sc_covered).
    basic_solver.
  Qed.
  
  Lemma ar_ct_I_in_I T (TCCOH : tc_coherent T) :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using.
    unfolder. ins; desf.
    assert (issuable T y) as AA by (by apply issued_in_issuable).
    apply AA.
    basic_solver 10.
  Qed.

  Lemma ar_I_in_I T (TCCOH : tc_coherent T) :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using.
    rewrite ct_step with (r:=ar). by apply ar_ct_I_in_I.
  Qed.

  Lemma ar_rt_I_in_I T (TCCOH : tc_coherent T) :
    dom_rel (⦗W⦘ ⨾ ar^* ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using.
    rewrite rtE, !seq_union_l, !seq_union_r, seq_id_l, dom_union.
    unionL; [basic_solver|]. by apply ar_ct_I_in_I.
  Qed.

  Lemma ar_rt_C_in_I T (TCCOH : tc_coherent T) :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
    unfolder.
    ins. desf.
    apply clos_rt_rtn1 in H0.
    induction H0.
    { apply w_covered_issued; basic_solver. }
    apply clos_rtn1_rt in H2.
    destruct H0 as [[AA|AA]|AA].
    3: { apply ar_int_in_sb in AA; auto.
         apply IHclos_refl_trans_n1.
         eapply dom_sb_covered; basic_solver 10. }
    { apply IHclos_refl_trans_n1.
      eapply dom_sc_covered; basic_solver 10. }
    apply ar_rt_I_in_I; auto.
    exists y. unfolder; splits; auto.
    apply dom_rf_covered; auto.
    eexists. apply seq_eqv_r. by split; [apply AA|].
  Qed.

  Lemma sbCsbI_CsbI  T (TCCOH : tc_coherent T) :
    sb ⨾ ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⊆
    ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⨾ sb.
  Proof using.
    rewrite id_union, !seq_union_r, !seq_union_l.
    apply union_mori.
    { rewrite sb_covered; eauto. basic_solver. }
    generalize (@sb_trans G). basic_solver 10.
  Qed.

  Lemma issuable_next_w T (TCCOH : tc_coherent T):
    W ∩₁ next (covered T) ⊆₁ issuable T.
  Proof using WF IMMCON.
    unfold issuable, next.
    rewrite fwbob_in_bob, bob_in_sb.
    apply set_subset_inter_r; split.
    { basic_solver 10. }
    rewrite !set_interA.
    arewrite (dom_cond sb (covered T) ∩₁ set_compl (covered T) ⊆₁ dom_cond sb (covered T)).
    { basic_solver 10. }
    intros e [WW [HH DD]]. red in DD. red.
    arewrite (⦗eq e⦘ ⊆ ⦗W⦘ ⨾ ⦗eq e⦘) by basic_solver.
    rewrite ct_end, !seqA.
    arewrite (ar ⨾ ⦗W⦘ ⊆ sb).
    { unfold imm_s.ar.
      rewrite !seq_union_l. rewrite WF.(ar_int_in_sb).
      rewrite wf_scD with (sc:=sc); [|by apply IMMCON].
      rewrite WF.(wf_rfeD). type_solver. }
    apply dom_rel_helper_in in DD.
    rewrite DD.
    arewrite (dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗covered T⦘ ⨾ sb ⨾ ⦗eq e⦘) ⊆₁
              dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗covered T⦘)) by basic_solver 20.
      by apply ar_rt_C_in_I.
  Qed.
  
  (* TODO: move to a more appropriate place *)
  Lemma ar_ar_in_ar_ct : ar ;; ar ⊆ ar⁺.
  Proof using.
    rewrite ct_step with (r:=ar) at 1 2. apply ct_ct.
  Qed.
  
  Lemma dom_rfe_ppo_issued T (TCCOH : tc_coherent T):
    dom_rel (rfe ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (dom_l WF.(wf_rfeD)).
    arewrite (rfe ⊆ ar).
    rewrite ppo_in_ar.
    sin_rewrite ar_ar_in_ar_ct.
      by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_rfe_acq_sb_issued T (TCCOH : tc_coherent T):
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF .
    rewrite (dom_l WF.(wf_rfeD)).
    arewrite (rfe ⊆ ar).
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ ar).
    { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob). unfold imm_s.ar, ar_int. eauto with hahn. }
    sin_rewrite ar_ar_in_ar_ct.
      by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_wex_sb_issued T (TCCOH : tc_coherent T):
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ;; ⦗W_ex_acq⦘).
    { rewrite <- seq_eqvK at 1.
      rewrite WF.(W_ex_in_W) at 1. basic_solver. }
    arewrite (⦗issued T⦘ ⊆ ⦗W⦘ ;; ⦗issued T⦘).
    { rewrite <- seq_eqvK at 1. by rewrite TCCOH.(issuedW) at 1. }
    arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
      by apply ar_I_in_I.
  Qed.

  Lemma rf_rmw_issued_rfi_rmw_issued T (TCCOH : tc_coherent T): 
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⨾ (rf ⨾ rmw)＊.
  Proof using WF IMMCON.
    assert (transitive sb) as SBT by apply sb_trans.
    eapply rt_ind_left with (P:= fun r => r ⨾ ⦗issued T⦘).
    { by eauto with hahn. }
    { basic_solver 12. }
    intros k H; rewrite !seqA.
    sin_rewrite H.
    rewrite rfi_union_rfe at 1; relsf; unionL.
    rewrite <- seqA; seq_rewrite <- ct_begin; basic_solver 12.
    rewrite rtE at 2.
    relsf; unionR left.
    arewrite (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆
                  ⦗issued T⦘ ⨾ rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘).
    { apply dom_rel_helper.
      arewrite (rmw ⨾ (rfi ⨾ rmw)＊ ⊆ ar^*).
      { arewrite (rfi ⊆ rf).
        rewrite WF.(rmw_in_ppo) at 1. rewrite ppo_in_ar.
        rewrite rtE at 1. rewrite seq_union_r, seq_id_r.
        apply inclusion_union_l.
        { rewrite ct_step at 1. apply inclusion_t_rt. }
        rewrite ar_rfrmw_ct_in_ar_ct; auto. apply inclusion_t_rt. }
      rewrite (dom_l WF.(wf_rfeD)), !seqA.
      arewrite (rfe ⊆ ar) at 1.
      seq_rewrite <- ct_begin. by apply ar_ct_I_in_I. }
    arewrite (rfe ⨾ rmw ⊆ rf ⨾ rmw).
    arewrite (rfi ⊆ rf).
    arewrite (rf ⨾ rmw ⨾ (rf ⨾ rmw)＊ ⊆ (rf ⨾ rmw)⁺).
    { rewrite <- seqA. apply ct_begin. }
    arewrite_id ⦗issued T⦘ at 2. rewrite seq_id_l.
    rewrite ct_rt. by rewrite inclusion_t_rt.
  Qed.

  Lemma wex_rfi_rfe_rmw_issuable_is_issued T (TCCOH : tc_coherent T):
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issuable T ⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite seq_union_l. rewrite dom_union.
    apply set_subset_union_l; split.
    { rewrite seqA. rewrite WF.(rfi_in_sbloc'). rewrite WF.(rmw_in_sb).
      arewrite (sb ∩ same_loc ⨾ sb ⊆ sb).
      { generalize (@sb_trans G). basic_solver. }
      arewrite (⦗issuable T⦘ ⊆ ⦗W⦘ ;; ⦗issuable T⦘).
      { unfold issuable. basic_solver 10. }
      arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ;; ⦗W_ex_acq⦘).
      { rewrite <- seq_eqvK at 1.
        rewrite WF.(W_ex_in_W) at 1. basic_solver. }
      arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
      rewrite ct_step with (r:=ar).
      unfold issuable. basic_solver 10. }
    rewrite WF.(rmw_in_ppo).
    rewrite ppo_in_ar.
    rewrite (dom_l WF.(wf_rfeD)), !seqA.
    arewrite (rfe ⊆ ar).
    sin_rewrite ar_ar_in_ar_ct.
    unfold issuable. basic_solver 10. 
  Qed.

  Lemma wex_rfi_rfe_rmw_issued_is_issued T (TCCOH : tc_coherent T):
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite issued_in_issuable at 1; auto.
      by apply wex_rfi_rfe_rmw_issuable_is_issued.
  Qed.

  Lemma wex_rf_rmw_issued_is_issued T (TCCOH : tc_coherent T):
    dom_rel (⦗ W_ex_acq ⦘ ⨾ rf ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (⦗W_ex_acq⦘ ⨾ rf ⊆ (⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe)).
    { rewrite rfi_union_rfe. basic_solver. }
      by apply wex_rfi_rfe_rmw_issued_is_issued.
  Qed.

  Lemma rf_rmw_issued T (TCCOH : tc_coherent T)
        (ACQEX : W_ex ⊆₁ W_ex_acq) :
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rf ⨾ rmw ⨾ ⦗issued T⦘)＊.
  Proof using WF.
    rewrite rmw_W_ex at 1.
    rewrite ACQEX.
    rewrite rt_begin.
    relsf; unionL; [basic_solver|].
    rewrite !seqA.
    rewrite <- !(seqA rf rmw).
    arewrite (⦗W_ex_acq⦘ ⨾ ((rf ⨾ rmw) ⨾ ⦗W_ex_acq⦘)＊ ⨾ ⦗issued T⦘ ⊆
              ⦗issued T⦘ ⨾ ((rf ⨾ rmw) ⨾ ⦗issued T⦘)＊).
    2: { rewrite <- !seqA.
         rewrite <- ct_begin.
         apply inclusion_t_rt. }
    intros x y HH.
    apply seq_eqv_l in HH. destruct HH as [WX HH].
    apply seq_eqv_r in HH. destruct HH as [HH IY].
    apply clos_rt_rt1n in HH.
    induction HH as [|z v w [o [AA [BB CC]]]]; desf.
    { apply seq_eqv_l. split; auto. apply rt_refl. }
    specialize (IHHH CC IY).
    apply seq_eqv_l in IHHH. destruct IHHH as [ISSV DD].
    apply seq_eqv_l. split.
    2: { apply rt_rt.
         exists v. split; auto.
         apply rt_step. basic_solver. }
    eapply wex_rf_rmw_issued_is_issued; auto.
    exists v. apply seq_eqv_l. split; auto.
    apply seqA. basic_solver.
  Qed.

  Lemma dom_sb_loc_issued T (TCCOH : tc_coherent T):
    dom_rel (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using.
    rewrite (issued_in_issuable TCCOH).
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma sb_loc_issued T (TCCOH : tc_coherent T) :
    ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘ ⊆ 
               ⦗covered T⦘ ⨾ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘.
  Proof using.
    seq_rewrite (dom_rel_helper (dom_sb_loc_issued TCCOH)).
    basic_solver.
  Qed.

  Lemma dom_F_sb_issued T (TCCOH : tc_coherent T):
    dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using.
    rewrite (issued_in_issuable TCCOH).
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma F_sb_issued T (TCCOH : tc_coherent T) :
    ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb.
  Proof using.
    seq_rewrite (dom_rel_helper (dom_F_sb_issued TCCOH)).
    basic_solver.
  Qed.

  Lemma dom_release_issued T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    dom_rel (release ⨾ ⦗ issued T ⦘) ⊆₁ covered T.
  Proof using WF IMMCON.
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
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (dom_release_issued TCCOH RELCOV)).
    basic_solver.
  Qed.

  Lemma dom_release_rf_coverable T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    dom_rel (release ⨾ rf ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF IMMCON.
    generalize (dom_release_issued TCCOH RELCOV).
    generalize (dom_rf_coverable TCCOH).
    basic_solver 21.
  Qed.

  Lemma release_rf_coverable T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    release ⨾ rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (dom_release_rf_coverable TCCOH RELCOV)).
    basic_solver.
  Qed.

  Lemma release_rf_covered T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    release ⨾ rf ⨾ ⦗ covered T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply release_rf_coverable.
  Qed.

  Lemma dom_sb_W_rel_issued T (TCCOH : tc_coherent T) :
    dom_rel (sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using.
    rewrite (issued_in_issuable TCCOH).
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma sb_W_rel_issued T (TCCOH : tc_coherent T) :
    sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ sb ⨾ ⦗W ∩₁ Rel⦘.
  Proof using.
    seq_rewrite (dom_rel_helper (dom_sb_W_rel_issued TCCOH)).
    basic_solver.
  Qed.

  Lemma dom_sw_coverable T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    dom_rel (sw ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF IMMCON.
    unfold imm_s_hb.sw.
    generalize (dom_sb_coverable TCCOH).
    generalize (dom_release_rf_coverable TCCOH RELCOV).
    generalize (covered_in_coverable TCCOH).
    basic_solver 21.
  Qed.

  Lemma sw_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    sw ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (dom_sw_coverable TCCOH RELCOV)).
    basic_solver.
  Qed.

  Lemma sw_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    sw ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply sw_coverable.
  Qed.

  Lemma hb_coverable  T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    hb ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
  Proof using WF IMMCON.
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

Lemma sc_sb_I_dom_C T (TCCOH : tc_coherent T) :
  dom_rel (sc ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof using IMMCON.
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

  Lemma dom_hb_coverable T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    dom_rel (hb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF IMMCON.
    rewrite (hb_coverable TCCOH RELCOV); basic_solver 10.
  Qed.

  Lemma hb_covered  T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
    hb ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply hb_coverable.
  Qed.

  Lemma dom_urr_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
    dom_rel (urr l ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
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
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (@dom_urr_coverable T TCCOH RELCOV l)).
    basic_solver.
  Qed.

  Lemma urr_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
    urr l ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply urr_coverable.
  Qed.

  Lemma dom_c_acq_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l A:
    dom_rel (c_acq i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
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
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (@dom_c_acq_coverable T TCCOH RELCOV i l A)).
    basic_solver.
  Qed.

  Lemma c_acq_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l A:
    c_acq i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply c_acq_coverable.
  Qed.


  Lemma dom_c_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l A:
    dom_rel (c_cur i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
    unfold CombRelations.c_cur.
    generalize (@dom_urr_coverable T TCCOH RELCOV l).
    basic_solver 21.
  Qed.

  Lemma c_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l A:
    c_cur i l A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (@dom_c_cur_coverable T TCCOH RELCOV i l A)).
    basic_solver.
  Qed.


  Lemma c_cur_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l A:
    c_cur i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply c_cur_coverable.
  Qed.

  Lemma dom_c_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l l' A:
    dom_rel (c_rel i l l' A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
    unfold CombRelations.c_rel.
    generalize (@dom_urr_coverable T TCCOH RELCOV l).
    basic_solver 21.
  Qed.


  Lemma c_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l l' A:
    c_rel i l l' A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
  Proof using WF IMMCON.
    seq_rewrite (dom_rel_helper (@dom_c_rel_coverable T TCCOH RELCOV i l l' A)).
    basic_solver.
  Qed.


  Lemma c_rel_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        i l l' A:
    c_rel i l l' A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply c_rel_coverable.
  Qed.

  Lemma t_acq_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l thread:
    t_acq thread l (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON.
    unfold CombRelations.t_acq.
    rewrite (dom_r (wf_c_acqD G sc thread l (coverable T))).
    arewrite (⦗(Tid_ thread ∪₁ Init) ∩₁ coverable T⦘ ⊆ ⦗coverable T⦘) by basic_solver.
    rewrite (c_acq_coverable TCCOH RELCOV).
    basic_solver.
  Qed.

  Lemma t_acq_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l thread:
    t_acq thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply t_acq_coverable.
  Qed.

  Lemma t_cur_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l thread:
    t_cur thread l (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON.
    etransitivity; [by apply t_cur_in_t_acq|].
      by apply t_acq_coverable.
  Qed.

  Lemma t_cur_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l thread:
    t_cur thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply t_cur_coverable.
  Qed.

  Lemma t_rel_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l l' thread:
    t_rel thread l l' (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON.
    etransitivity; [by apply t_rel_in_t_cur|].
      by apply t_cur_coverable.
  Qed.

  Lemma t_rel_covered T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
        l l' thread:
    t_rel thread l l' (covered T) ⊆₁ issued T.
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply t_rel_coverable.
  Qed.

  Lemma S_tm_coverable T (TCCOH : tc_coherent T) (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
    S_tm l (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON.
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
  Proof using WF IMMCON.
    rewrite (covered_in_coverable TCCOH) at 1.
      by apply S_tm_coverable.
  Qed.

  Lemma msg_rel_issued T (TCCOH : tc_coherent T)
        (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) l:
    dom_rel (msg_rel l ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON.
    unfold CombRelations.msg_rel.
    generalize (dom_release_issued TCCOH RELCOV).
    generalize (@dom_urr_coverable T TCCOH RELCOV l).
    generalize (covered_in_coverable TCCOH).
    basic_solver 21.
  Qed.

Lemma exists_ncov T thread (TCCOH : tc_coherent T) :
  exists n, ~ covered T (ThreadEvent thread n).
Proof using.
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
Proof using WF IMMCON TCCOH.
  rewrite !id_union. rewrite seq_union_r. 
  unionL.
  { rewrite sw_covered; eauto. basic_solver. }
  assert (forall (s : actid -> Prop), s ∪₁ set_compl s ≡₁ fun _ => True) as AA.
  { split; [basic_solver|].
    unfolder. ins. apply classic. }
  arewrite (sw ⊆ ⦗ C ∪₁ set_compl C ⦘ ⨾ sw) at 1.
  { rewrite AA. by rewrite seq_id_l. }
  rewrite id_union, !seq_union_l.
  apply union_mori; [basic_solver|].
  rewrite (dom_r WF.(wf_swD)).
  rewrite sw_in_ar0; auto.
  remember (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rfe ∪ ar_int G)⁺) as ax.
  rewrite !seq_union_l, !seq_union_r.
  unionL; [|basic_solver].
  subst ax. rewrite !seqA.
  arewrite ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ ⦗W⦘) by basic_solver. 
  arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ release).
  { unfold imm_s_hb.release, imm_s_hb.rs. by rewrite <- inclusion_id_rt, seq_id_r. }
  enough (dom_rel (⦗W⦘ ⨾ (rfe ∪ ar_int G)⁺ ⨾ ⦗FR ∩₁ Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) ⊆₁ I) as BB.
  { rewrite (dom_rel_helper BB).
    seq_rewrite (dom_rel_helper (dom_release_issued TCCOH RELCOV)).
    basic_solver. }
  rewrite <- !seqA. rewrite dom_rel_eqv_dom_rel. rewrite !seqA.
  arewrite (⦗FR ∩₁ Acq⦘ ⨾ sb^? ⊆ (rfe ∪ ar_int G)^?).
  { rewrite !crE, !seq_union_r. apply union_mori; [basic_solver|].
    unionR right. rewrite set_inter_union_l, id_union, seq_union_l.
    rewrite sb_from_r_acq_in_bob.
    arewrite (Acq ⊆₁ Acq/Rel) by mode_solver.
    rewrite sb_from_f_in_bob. rewrite bob_in_ar_int. eauto with hahn. }
  seq_rewrite ct_cr.
  arewrite (rfe ∪ ar_int G ⊆ ar). by apply ar_ct_I_in_I.
Qed.

Lemma hb_in_Chb_sb (RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
  hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof using WF IMMCON TCCOH.
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
