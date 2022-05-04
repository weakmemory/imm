Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

Require Import AuxDef Events Execution.
Require Import Execution_eco imm_s_hb imm_s imm_bob.
Require Import imm_s_ppo CombRelations.
Require Import imm_s_rfppo.
Require Import FinExecution.

Set Implicit Arguments.

Section TraversalConfig.

  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'eco'" := (eco G).

  Notation "'bob'" := (bob G).
  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).
  Notation "'release'" := (release G).
  Notation "'sw'" := (sw G).
  Notation "'hb'" := (hb G).

  Notation "'ar'" := (ar G sc).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := (S_tm G).
  Notation "'S_tmr'" := (S_tmr G).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
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
                           (dom_cond (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺) (issued T)).

  Definition tc_coherent (T : trav_config) :=
    ⟪ ICOV  : Init ∩₁ E ⊆₁ covered T ⟫ /\
    ⟪ CC    : covered T ⊆₁ coverable T ⟫ /\
    ⟪ II    : issued  T ⊆₁ issuable T ⟫.

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

  Lemma same_trav_config_refl : reflexive same_trav_config.
  Proof using. split; basic_solver. Qed.

  Lemma same_trav_config_sym : symmetric same_trav_config.
  Proof using. unfold same_trav_config; split; ins; desf; symmetry; auto. Qed.

  Lemma same_trav_config_trans : transitive same_trav_config.
  Proof using. unfold same_trav_config; split; ins; desf; etransitivity; eauto. Qed.

  
(******************************************************************************)
(** **   *)
(******************************************************************************)
  
  Global Add Parametric Relation : trav_config same_trav_config
      reflexivity proved by same_trav_config_refl
      symmetry proved by same_trav_config_sym
      transitivity proved by same_trav_config_trans
        as same_tc.

  Lemma same_tc_extensionality tc1 tc2 (SAME: same_trav_config tc1 tc2):
    tc1 = tc2.
  Proof using.
    destruct SAME.
    destruct tc1, tc2. ins.
    apply set_extensionality in H, H0.   
    congruence. 
  Qed. 

  
  Global Add Parametric Morphism : covered with signature
      same_trav_config ==> set_equiv as covered_more.
  Proof using. by unfold same_trav_config; ins; split; ins; desf; apply H. Qed.

  Global Add Parametric Morphism : issued with signature
      same_trav_config ==> set_equiv as issued_more.
  Proof using. by unfold same_trav_config; ins; desf; apply H1. Qed.
  

  Global Add Parametric Morphism : coverable with signature
      same_trav_config ==> set_equiv as coverable_more.
  Proof using.
    unfold coverable, same_trav_config; split; ins; desf.
    all: unnw; try first [ rewrite <- H, <- H0 | rewrite H, H0].
    all: unfold set_equiv in *; unnw; intuition; basic_solver 12.
  Qed.

  Global Add Parametric Morphism : issuable with signature
      same_trav_config ==> set_equiv as issuable_more.
  Proof using.
    unfold issuable, same_trav_config; split; ins; desf.
    all: unnw; try first [ rewrite <- H, <- H0 | rewrite H, H0].
    all: unfold set_equiv in *; unnw; intuition; basic_solver 12.
  Qed.

  Global Add Parametric Morphism : tc_coherent with signature
      same_trav_config ==> iff as tc_coherent_more.
  Proof using.
    intros T T' EQ.
    split; [apply same_tc_Symmetric in EQ|];
      intros HH; cdes HH; red; splits.
    all: try erewrite covered_more; eauto.
    all: try erewrite coverable_more; eauto.
    all: try erewrite issued_more; eauto.
    all: erewrite issuable_more; eauto.
  Qed.

  Global Add Parametric Morphism : mkTC with signature
         (@set_equiv actid) ==> (@set_equiv actid) ==> same_trav_config as mkTC_more.
  Proof using. vauto. Qed.  

(******************************************************************************)
(** **   *)
(******************************************************************************)

Section Properties.
  Variable T : trav_config.
  Variable TCCOH : tc_coherent T.

  Lemma issued_in_issuable : issued T ⊆₁ issuable T.
  Proof using TCCOH. apply TCCOH. Qed.

  Lemma issuableE :
    issuable T ⊆₁ E.
  Proof using. unfold issuable; basic_solver. Qed.

  Lemma issuedE :
    issued T ⊆₁ E.
  Proof using TCCOH. rewrite issued_in_issuable. by apply issuableE. Qed.

  Lemma issuableW :
    issuable T ⊆₁ W.
  Proof using. unfold issuable; basic_solver. Qed.

  Lemma issuedW :
    issued T ⊆₁ W.
  Proof using TCCOH.
    rewrite issued_in_issuable.
    by apply issuableW.
  Qed.

  Lemma covered_in_coverable :
    covered T ⊆₁ coverable T.
  Proof using TCCOH.
    apply TCCOH.
  Qed.

  Lemma coverableE :
    coverable T ⊆₁ E.
  Proof using.
    unfold coverable; basic_solver.
  Qed.

  Lemma coveredE :
    covered T ⊆₁ E.
  Proof using TCCOH.
    rewrite covered_in_coverable.
    by apply coverableE.
  Qed.

  Lemma w_coverable_issued :
    W ∩₁ coverable T ⊆₁ issued T.
  Proof using.
    unfold coverable; type_solver.
  Qed.

  Lemma w_covered_issued :
    W ∩₁ covered T ⊆₁ issued T.
  Proof using TCCOH.
    rewrite covered_in_coverable.
    by apply w_coverable_issued.
  Qed.

  Lemma init_issued : is_init ∩₁ E ⊆₁ issued T.
  Proof using WF TCCOH.
    unfolder; ins; desf.
    apply w_covered_issued.
    split.
    { by apply (init_w WF). }
    cdes TCCOH; unfolder in ICOV; basic_solver 21. 
  Qed.

  Lemma init_covered : is_init ∩₁ E ⊆₁ covered T.
  Proof using TCCOH. 
    unfolder; ins; desf.
    cdes TCCOH; unfolder in ICOV; basic_solver 21. 
  Qed.

  Lemma next_n_init e
        (NEXT : next (covered T) e) :
    ~ Init e.
  Proof using TCCOH.
    intros HH. apply NEXT.
    apply init_covered. split; auto.
    apply NEXT.
  Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

  Lemma ar_ct_issuable_is_issued  : 
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using.
    arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc).
    unfold issuable. basic_solver 20.
  Qed.

  Lemma ar_issuable_is_issued  : 
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using.
    rewrite ct_step with (r:=ar).
    apply ar_ct_issuable_is_issued.
  Qed.

  Lemma dom_sb_coverable :
    dom_rel (sb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using.
    unfold coverable, dom_cond; basic_solver 21.
  Qed.

  Lemma sb_coverable :
    sb ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ sb.
  Proof using.
   rewrite (dom_rel_helper dom_sb_coverable).
   basic_solver.
  Qed.

  Lemma dom_sb_covered :
    dom_rel (sb ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using TCCOH.
  rewrite covered_in_coverable at 1.
  seq_rewrite (dom_rel_helper dom_sb_coverable).
  basic_solver.
  Qed.

  Lemma sb_covered :
    sb ⨾ ⦗ covered T ⦘ ≡ ⦗ covered T ⦘ ⨾ sb ⨾ ⦗ covered T ⦘.
  Proof using TCCOH.
  rewrite (dom_rel_helper dom_sb_covered).
  basic_solver.
  Qed.

  Lemma dom_rf_coverable :
    dom_rel (rf ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    unfold coverable, dom_cond.
    rewrite (dom_r (wf_rfD WF)).
    type_solver 40.
  Qed.

  Lemma dom_rf_covered :
    dom_rel (rf ⨾ ⦗ covered  T ⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite covered_in_coverable.
    apply dom_rf_coverable.
  Qed.

  Lemma rf_coverable :
    rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ issued T ⦘ ⨾ rf.
  Proof using WF TCCOH.
    rewrite (dom_rel_helper dom_rf_coverable).
    basic_solver.
  Qed.

  Lemma rf_covered :
    rf ⨾ ⦗ covered T ⦘ ≡ ⦗ issued T ⦘ ⨾ rf ⨾ ⦗ covered T ⦘.
  Proof using WF TCCOH.
    rewrite (dom_rel_helper dom_rf_covered).
    basic_solver.
  Qed.

  Lemma dom_sc_coverable :
    dom_rel (sc ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using IMMCON.
    cdes IMMCON.
    rewrite (dom_r (@wf_scD G sc Wf_sc)).
    unfold coverable, dom_cond; type_solver 42.
  Qed.

  Lemma dom_sc_covered :
    dom_rel (sc ⨾ ⦗ covered T ⦘) ⊆₁ covered T.
  Proof using IMMCON TCCOH.
    rewrite covered_in_coverable at 1.
    seq_rewrite (dom_rel_helper dom_sc_coverable).
    basic_solver.
  Qed.

  Lemma sc_coverable  :
    sc ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
  Proof using IMMCON.
    seq_rewrite (dom_rel_helper dom_sc_coverable).
    basic_solver.
  Qed.

  Lemma sc_covered  :
    sc ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sc.
  Proof using IMMCON TCCOH.
    rewrite covered_in_coverable at 1.
      by apply sc_coverable.
  Qed.

  Lemma ar_coverable_in_CI  :
    dom_rel (ar ⨾ ⦗coverable T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    unfold imm_s.ar.
    rewrite !seq_union_l.
    rewrite (ar_int_in_sb WF).
    arewrite (rfe ⊆ rf).
    rewrite sb_coverable, rf_coverable.
    rewrite sc_coverable.
    basic_solver.
  Qed.

  Lemma ar_C_in_CI  :
    dom_rel (ar ⨾ ⦗covered T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite covered_in_coverable at 1.
    apply ar_coverable_in_CI.
  Qed.

  Lemma ar_rf_ppo_loc_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using.
    unfold issuable.
    basic_solver 10.
  Qed.

  Lemma ar_rfrmw_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    rewrite issued_in_issuable at 1.
    apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union; unionL.
    { basic_solver. }
    apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rfrmw_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_rt_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc)) ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using.
    rewrite ct_step with (r := ar ∪ rf ⨾ (ppo ∩ same_loc)).
      by apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc)) ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    rewrite ct_step with (r := ar ∪ rf ⨾ (ppo ∩ same_loc)).
      by apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rfrmw_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_I_in_I.
  Qed.

  Lemma ar_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw). by apply ar_rfrmw_ct_issuable_in_I.
  Qed.

  Lemma ar_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw). by apply ar_rfrmw_ct_I_in_I.
  Qed.

  Lemma ar_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite ct_step with (r:=ar). by apply ar_ct_issuable_in_I.
  Qed.

  Lemma ar_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite ct_step with (r:=ar). by apply ar_ct_I_in_I.
  Qed.

  Lemma W_ar_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite dom_eqv1. rewrite ar_coverable_in_CI.
    rewrite set_inter_union_r; unionL.
    2: basic_solver.
    apply w_covered_issued.
  Qed.

  Lemma W_ar_C_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite covered_in_coverable.
    apply W_ar_coverable_in_I.
  Qed.

  Lemma W_ar_coverable_issuable_in_CI  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply W_ar_coverable_in_I. }
    apply ar_issuable_in_I.
  Qed.

  Lemma ar_CI_in_CI  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply W_ar_C_in_I. }
    apply ar_I_in_I.
  Qed.

  Lemma ar_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite rtE, !seq_union_l, !seq_union_r, seq_id_l, dom_union.
    unionL; [basic_solver|]. by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_W_sb_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    rewrite sb_coverable; auto.
    etransitivity.
    2: by apply w_covered_issued.
    basic_solver.
  Qed.
  
  Lemma dom_W_sb_C_in_I  :
    dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    rewrite covered_in_coverable.
    apply dom_W_sb_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_coverable_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    arewrite (ppo ∩ same_loc ⊆ ppo).
    rewrite (dom_l (wf_rfD WF)), seqA.
    rewrite rfi_union_rfe, !seq_union_l, !seq_union_r, dom_union.
    unionL.
    2: { rewrite (dom_r (@wf_ppoD G)), !seqA.
         rewrite <- id_inter.
         rewrite w_coverable_issued.
         sin_rewrite rfe_ppo_in_ar_ct; auto.
           by apply ar_ct_I_in_I. }
    arewrite (rfi ⊆ sb).
    rewrite (ppo_in_sb WF). sin_rewrite sb_sb.
    rewrite dom_W_sb_coverable_in_I; auto.
  Qed.

  Lemma rfrmw_coverable_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_C_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite covered_in_coverable.
    apply rf_ppo_loc_coverable_in_I.
  Qed.

  Lemma rfrmw_C_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite covered_in_coverable.
    apply rfrmw_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_coverable_issuable_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { apply rf_ppo_loc_coverable_in_I. }
    rewrite (dom_l (wf_rfD WF)), !seqA.
    arewrite (rf ⨾ ppo ∩ same_loc ⊆ ar ∪ rf ⨾ ppo ∩ same_loc).
      by apply ar_rf_ppo_loc_issuable_in_I.
  Qed.

  Lemma rfrmw_coverable_issuable_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma rf_ppo_loc_I_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (dom_l (wf_rfD WF)), seqA.
    arewrite (rf ⨾ (ppo ∩ same_loc) ⊆ ar ∪ rf ⨾ (ppo ∩ same_loc)).
      by apply ar_rf_ppo_loc_I_in_I.
  Qed.

  Lemma rfrmw_I_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_I_in_I.
  Qed.

  Lemma rf_ppo_loc_rt_I_in_I  :
    dom_rel ((rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_id_l. rewrite dom_union.
    unionL; [basic_solver|].
    rewrite (dom_l (wf_rfD WF)). rewrite !seqA.
    rewrite inclusion_ct_seq_eqv_l. rewrite !seqA.
    arewrite (rf ⨾ ppo ∩ same_loc ⊆ ar ∪ rf ⨾ ppo ∩ same_loc).
    apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma rfrmw_rt_I_in_I  :
    dom_rel ((rf ⨾ rmw)＊ ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_rt_I_in_I.
  Qed.

  Lemma rf_ppo_loc_CI_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { by apply rf_ppo_loc_C_in_I. }
      by apply rf_ppo_loc_I_in_I.
  Qed.

  Lemma rfrmw_CI_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_coverable_in_CI  :
    dom_rel ((ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗coverable T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite seq_union_l, dom_union, !seqA.
    unionL.
    { by apply ar_coverable_in_CI. }
    rewrite rf_ppo_loc_coverable_in_I; eauto with hahn.
  Qed.

  Lemma ar_rfrmw_coverable_in_CI  :
    dom_rel ((ar ∪ rf ⨾ rmw) ⨾ ⦗coverable T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_coverable_in_CI.
  Qed.

  Lemma ar_rf_ppo_loc_C_in_CI  :
    dom_rel ((ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗covered T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite covered_in_coverable at 1.
    apply ar_rf_ppo_loc_coverable_in_CI.
  Qed.

  Lemma ar_rfrmw_C_in_CI  :
    dom_rel ((ar ∪ rf ⨾ rmw) ⨾ ⦗covered T⦘) ⊆₁ covered T ∪₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_C_in_CI.
  Qed.

  Lemma ar_rf_ppo_loc_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite seq_union_l, seq_union_r, dom_union; unionL.
    { apply W_ar_coverable_issuable_in_CI. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    apply rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite seq_union_l, seq_union_r, dom_union; unionL.
    { apply ar_CI_in_CI. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    apply rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rfrmw_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    intros x [y HH].
    destruct_seq HH as [AA BB].
    apply clos_trans_tn1 in HH.
    induction HH as [y HH|y z QQ].
    { eapply ar_rf_ppo_loc_coverable_issuable_in_I. basic_solver 10. }
    apply clos_tn1_trans in HH.
    destruct QQ as [QQ|QQ].
    2: { apply IHHH. right.
         apply issued_in_issuable.
         apply rf_ppo_loc_coverable_issuable_in_I.
         exists z. apply seqA. basic_solver. }
    destruct BB as [BB|BB].
    2: { apply ar_rf_ppo_loc_ct_issuable_in_I. exists z.
         apply seq_eqv_lr. splits; auto.
         apply ct_end. exists y. split; auto.
         { by apply clos_trans_in_rt. }
           by left. }
    apply IHHH.
    destruct QQ as [[QQ|QQ]|QQ].
    { left. apply covered_in_coverable.
      apply dom_sc_coverable. exists z. basic_solver. }
    { right. apply issued_in_issuable.
      apply dom_rf_coverable. exists z.
      do 2 red in QQ. basic_solver. }
    left. apply covered_in_coverable.
    apply dom_sb_coverable. exists z.
    apply seq_eqv_r. split; auto. by apply ar_int_in_sb.
  Qed.

  Lemma ar_rfrmw_ct_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite covered_in_coverable.
    rewrite issued_in_issuable at 1.
    apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_ct_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    { generalize w_coverable_issued. basic_solver. }
    arewrite (coverable T ⊆₁ coverable T ∪₁ issuable T).
    apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_rt_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗coverable T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_rt_coverable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    { generalize w_covered_issued. basic_solver. }
    apply ar_rf_ppo_loc_ct_CI_in_I.
  Qed.

  Lemma ar_rfrmw_rt_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_rt_CI_in_I.
  Qed.
  
  Lemma ar_rt_C_in_I  :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗covered T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
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

  Lemma ar_rt_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗covered T ∪₁ issued T⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH.
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply ar_rt_C_in_I. }
      by apply ar_rt_I_in_I.
  Qed.

  Lemma sbCsbI_CsbI   :
    sb ⨾ ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⊆
    ⦗covered T ∪₁ dom_rel (sb^? ⨾ ⦗issued T⦘)⦘ ⨾ sb.
  Proof using TCCOH.
    rewrite id_union, !seq_union_r, !seq_union_l.
    apply union_mori.
    { rewrite sb_covered; eauto. basic_solver. }
    generalize (@sb_trans G). basic_solver 10.
  Qed.

  Lemma issuable_next_w :
    W ∩₁ next (covered T) ⊆₁ issuable T.
  Proof using WF IMMCON TCCOH.
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
    arewrite (ar ∪ rf ⨾ ppo ∩ same_loc ⊆ (ar ∪ sb)^? ⨾ ar) at 2.
    { apply inclusion_union_l; [basic_solver|].
      rewrite rfi_union_rfe. rewrite rfe_in_ar, ppo_in_ar.
      arewrite (rfi ⊆ sb). basic_solver 10. }
    arewrite (ar ⨾ ⦗W⦘ ⊆ sb).
    { unfold imm_s.ar.
      rewrite !seq_union_l. rewrite (ar_int_in_sb WF).
      rewrite wf_scD with (sc:=sc); [|by apply IMMCON].
      rewrite (wf_rfeD WF). type_solver. }
    apply dom_rel_helper_in in DD.
    rewrite DD.
    arewrite ((ar ∪ sb)^? ⨾ ⦗covered T⦘ ⊆ ⦗covered T ∪₁ issued T⦘ ⨾ (ar ∪ sb)^? ⨾ ⦗covered T⦘).
    2: { etransitivity.
         2: by apply ar_rf_ppo_loc_rt_CI_in_I.
         basic_solver 20. }
    apply dom_rel_helper_in.
    rewrite crE, !seq_union_l, !dom_union, seq_id_l.
    unionL; [basic_solver| |].
    2: rewrite dom_sb_covered; basic_solver.
    apply ar_C_in_CI.
  Qed.
  
  Lemma dom_rfe_ppo_issued :
    dom_rel (rfe ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    rewrite ppo_in_ar.
    sin_rewrite ar_ar_in_ar_ct.
      by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_ar_ct_issuable : dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using.
    arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc).
    unfold issuable.
    basic_solver 20.
  Qed.

  Lemma dom_detour_rfe_ppo_issuable :
    dom_rel ((detour ∪ rfe) ⨾ ppo ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (dom_l (wf_rfeD WF)).
    rewrite (dom_l (wf_detourD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    rewrite ppo_in_ar, !seqA.
    sin_rewrite ar_ar_in_ar_ct.
    apply dom_ar_ct_issuable.
  Qed.
  
  Lemma dom_detour_rfe_ppo_issued :
    dom_rel ((detour ∪ rfe) ⨾ ppo ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1.
    apply dom_detour_rfe_ppo_issuable.
  Qed.

  Lemma dom_detour_rfe_acq_sb_issuable :
    dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite (dom_l (wf_detourD WF)).
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ ar).
    { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob). unfold imm_s.ar, ar_int. eauto with hahn. }
    sin_rewrite ar_ar_in_ar_ct.
    apply dom_ar_ct_issuable.
  Qed.

  Lemma dom_detour_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1.
    apply dom_detour_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_detour_rmwrfi_rfe_acq_sb_issuable :
    dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗Acq⦘ ⨾ ⦗R ∩₁ Acq⦘) by basic_solver.
    arewrite (rfi ⊆ rf).
    sin_rewrite (@rmwrf_rt_Acq_in_ar_rfrmw_rt G WF sc); auto.
    rewrite (dom_l (wf_detourD WF)).
    rewrite (dom_l (wf_rfeD WF)).
    arewrite (rfe ⊆ ar).
    arewrite (detour ⊆ ar).
    relsf.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ ar).
    { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob). unfold imm_s.ar, ar_int. eauto with hahn. }
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw) at 3.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw) at 1.
    seq_rewrite <- ct_end.
    arewrite ((ar ∪ rf ⨾ rmw) ⨾ (ar ∪ rf ⨾ rmw)⁺ ⊆ (ar ∪ rf ⨾ rmw)⁺).
    { rewrite ct_step with (r:= ar ∪ rf ⨾ rmw) at 1. apply ct_ct. }
    apply ar_rfrmw_ct_issuable_in_I.
  Qed.

  Lemma dom_detour_rmwrfi_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1.
    apply dom_detour_rmwrfi_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_rfe_acq_sb_issuable :
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (rfe ⊆ detour ∪ rfe).
    apply dom_detour_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_rfe_acq_sb_issued :
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1.
    apply dom_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_wex_sb_issuable :
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issuable T⦘) ⊆₁ issued T.
  Proof using WF.
    arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗W_ex_acq⦘).
    { rewrite <- seq_eqvK at 1.
      rewrite (W_ex_in_W WF) at 1. basic_solver. }
    arewrite (⦗issuable T⦘ ⊆ ⦗W⦘ ⨾ ⦗issuable T⦘).
    { unfold issuable. basic_solver 10. }
    arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
    apply ar_issuable_is_issued.
  Qed.

  Lemma dom_wex_sb_issued :
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1.
    apply dom_wex_sb_issuable.
  Qed.
  
  Lemma rf_rmw_issued_rfi_rmw_issued : 
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⨾ (rf ⨾ rmw)＊.
  Proof using WF TCCOH IMMCON.
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
      arewrite (rmw ⨾ (rfi ⨾ rmw)＊ ⊆ ar＊).
      { arewrite (rfi ⊆ rf).
        rewrite (rmw_in_ppo WF) at 1. rewrite ppo_in_ar.
        rewrite rtE at 1. rewrite seq_union_r, seq_id_r.
        apply inclusion_union_l.
        { rewrite ct_step at 1. apply inclusion_t_rt. }
        rewrite rmw_in_ppo_loc; auto.
        rewrite ar_rf_ppo_loc_ct_in_ar_ct; auto. apply inclusion_t_rt. }
      rewrite (dom_l (wf_rfeD WF)), !seqA.
      arewrite (rfe ⊆ ar) at 1.
      seq_rewrite <- ct_begin. by apply ar_ct_I_in_I. }
    arewrite (rfe ⨾ rmw ⊆ rf ⨾ rmw).
    arewrite (rfi ⊆ rf).
    arewrite (rf ⨾ rmw ⨾ (rf ⨾ rmw)＊ ⊆ (rf ⨾ rmw)⁺).
    { rewrite <- seqA. apply ct_begin. }
    arewrite_id ⦗issued T⦘ at 2. rewrite seq_id_l.
    rewrite ct_rt. by rewrite inclusion_t_rt.
  Qed.

  Lemma wex_rfi_rfe_rmw_issuable_is_issued :
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issuable T ⦘) ⊆₁ issued T.
  Proof using WF.
    rewrite seq_union_l. rewrite dom_union.
    apply set_subset_union_l; split.
    { rewrite seqA. rewrite (rfi_in_sbloc' WF). rewrite (rmw_in_sb WF).
      arewrite (sb ∩ same_loc ⨾ sb ⊆ sb).
      { generalize (@sb_trans G). basic_solver. }
      arewrite (⦗issuable T⦘ ⊆ ⦗W⦘ ⨾ ⦗issuable T⦘).
      { unfold issuable. basic_solver 10. }
      arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗W_ex_acq⦘).
      { rewrite <- seq_eqvK at 1.
        rewrite (W_ex_in_W WF) at 1. basic_solver. }
      arewrite (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar).
      rewrite ct_step with (r:=ar).
      unfold issuable.
      arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc) at 1.
      basic_solver 10. }
    rewrite (rmw_in_ppo WF).
    rewrite ppo_in_ar.
    rewrite (dom_l (wf_rfeD WF)), !seqA.
    arewrite (rfe ⊆ ar).
    sin_rewrite ar_ar_in_ar_ct.
    unfold issuable.
    arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc) at 1.
    basic_solver 10. 
  Qed.

  Lemma wex_rfi_rfe_rmw_issued_is_issued :
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    rewrite issued_in_issuable at 1; auto.
      by apply wex_rfi_rfe_rmw_issuable_is_issued.
  Qed.

  Lemma wex_rf_rmw_issued_is_issued :
    dom_rel (⦗ W_ex_acq ⦘ ⨾ rf ⨾ rmw ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF TCCOH.
    arewrite (⦗W_ex_acq⦘ ⨾ rf ⊆ (⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe)).
    { rewrite rfi_union_rfe. basic_solver. }
      by apply wex_rfi_rfe_rmw_issued_is_issued.
  Qed.

  Lemma rf_rmw_issued :
    (rf ⨾ rmw)＊ ⨾ ⦗issued T⦘ ⊆ (rf ⨾ rmw ⨾ ⦗issued T⦘)＊.
  Proof using WF TCCOH.
    intros x y HH. destruct_seq_r HH as II.
    apply clos_rt_rtn1 in HH.
    induction HH as [|y z TT].
    { apply rt_refl. }
    apply rt_end. right. exists y.
    split.
    2: apply seqA; basic_solver.
    apply IHHH.
    apply ar_rfrmw_I_in_I. exists z.
    apply seq_eqv_lr. splits; auto.
    2: by right.
    red in TT. desf. apply (wf_rfD WF) in TT. unfolder in TT. desf.
  Qed.

  Lemma dom_W_Rel_sb_loc_I_in_C :
    dom_rel (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using TCCOH.
    rewrite issued_in_issuable.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma I_eq_EW_I : issued T ≡₁ E ∩₁ W ∩₁ issued T.
  Proof using TCCOH.
    split; [|clear; basic_solver].
    generalize issuedW, issuedE.
    basic_solver.
  Qed.

  Lemma W_rel_sb_loc_W_CI :
    (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘) ⨾ ⦗covered T ∪₁ issued T⦘ ⊆
    ⦗covered T ∪₁ issued T⦘ ⨾ (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘).
  Proof using TCCOH.
    (* case_refl _; [basic_solver|]. *)
    rewrite !seqA.
    arewrite (⦗W⦘ ⨾ ⦗covered T ∪₁ issued T⦘ ⊆ ⦗W⦘ ⨾ ⦗issued T⦘).
    { generalize w_covered_issued. basic_solver. }
    generalize dom_W_Rel_sb_loc_I_in_C. basic_solver 12.
  Qed.

  Lemma sb_W_rel_CI (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T) :
    (sb ⨾ ⦗W ∩₁ Rel⦘) ⨾ ⦗covered T ∪₁ issued T⦘ ⊆ ⦗covered T ∪₁ issued T⦘ ⨾ (sb ⨾ ⦗W ∩₁ Rel⦘).
  Proof using TCCOH.
    generalize RELCOV, dom_sb_covered.
    basic_solver 12.
  Qed.

  Lemma W_Rel_sb_loc_I : dom_rel (⦗W ∩₁ Rel⦘ ⨾  (sb ∩ same_loc) ⨾ ⦗W ∩₁ issued T⦘) ⊆₁ issued T.
  Proof using TCCOH.
    generalize dom_W_Rel_sb_loc_I_in_C, w_covered_issued. basic_solver 21.
  Qed.

  Lemma sb_loc_issued  :
    ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗issued T⦘ ⊆ 
               ⦗covered T⦘ ⨾ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘.
  Proof using TCCOH.
    seq_rewrite (dom_rel_helper dom_W_Rel_sb_loc_I_in_C).
    basic_solver.
  Qed.

  Lemma dom_F_sb_I_in_C :
    dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using TCCOH.
    rewrite issued_in_issuable.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma F_sb_I_in_C  :
    ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb.
  Proof using TCCOH.
    seq_rewrite (dom_rel_helper dom_F_sb_I_in_C).
    basic_solver.
  Qed.

  Lemma dom_F_Rel_sb_I_in_C :  dom_rel (⦗F ∩₁ Rel⦘ ⨾  sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using TCCOH. etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 21. Qed.

  Lemma dom_F_Acq_sb_I_in_C :  dom_rel (⦗F ∩₁ Acq⦘ ⨾  sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using TCCOH. etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 12. Qed.

  Lemma coverable_add_eq_iff e:
    coverable T e <-> coverable (mkTC (covered T ∪₁ eq e) (issued T)) e.
  Proof using IMMCON.
    split.
    { eapply traversal_mon; simpls. eauto with hahn. }
    unfold coverable; simpls. 
    intros [[EE COVE] HH].
    split.
    { clear HH. split; auto.
      unfolder in *. ins. desf.
      edestruct COVE.
      { eexists; eauto. }
      { done. }
      exfalso. desf. eapply sb_irr; eauto. }
    destruct HH as [[HH|HH]|[AA HH]]; [do 2 left| left;right|right]; auto.
    split; auto.
    unfolder in *. ins. desf. edestruct HH.
    { eexists; eauto. }
    { done. }
    exfalso. desf. eapply sc_irr; eauto.
    apply IMMCON.
  Qed.

  Lemma issuable_add_eq_iff e :
    issuable T e <-> issuable (mkTC (covered T) (issued T ∪₁ eq e)) e.
  Proof using WF IMMCON.
    cdes IMMCON.
    split.
    { eapply traversal_mon; simpls. eauto with hahn. }
    unfold issuable; simpls. 
    intros [[EE ISSE] HH].
    unfold dom_cond in *.
    split; [split|]; auto.
    all: intros x BB; set (CC:=BB).
    apply HH in CC.
    destruct CC; desf.
    exfalso; clear -BB WF IMMCON.
    unfolder in *; desf.
    eapply ar_rf_ppo_loc_acyclic; eauto.
    apply IMMCON.
  Qed.
  
  Variable RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T.

  Lemma dom_release_issued :
    dom_rel (release ⨾ ⦗ issued T ⦘) ⊆₁ covered T.
  Proof using WF TCCOH RELCOV IMMCON.
    unfold imm_s_hb.release, imm_s_hb.rs.
    rewrite !seqA.
    sin_rewrite rf_rmw_issued_rfi_rmw_issued.
    rewrite (dom_r (wf_rmwD WF)) at 1.
    arewrite (⦗W⦘ ⨾ (rfi ⨾ rmw ⨾ ⦗W⦘)＊ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗W⦘).
    { rewrite rtE; relsf; unionL; [basic_solver|].
      rewrite <- seqA; rewrite inclusion_ct_seq_eqv_r; basic_solver. }
    rewrite (rmw_in_sb_loc WF) at 1; rewrite (rfi_in_sbloc' WF).
    generalize (@sb_same_loc_trans G); ins; relsf.
    rewrite !crE; relsf; unionL; splits.
    { revert RELCOV; basic_solver 21. }
    { generalize dom_W_Rel_sb_loc_I_in_C. basic_solver 21. }
    2: generalize (@sb_trans G).
    all: generalize dom_F_Rel_sb_I_in_C; basic_solver 40.
  Qed.

  Lemma release_issued :
    release ⨾ ⦗ issued T ⦘ ⊆ ⦗covered T⦘ ⨾ release.
  Proof using WF TCCOH RELCOV IMMCON.
    seq_rewrite (dom_rel_helper dom_release_issued).
    basic_solver.
  Qed.

  Lemma dom_release_rf_coverable :
    dom_rel (release ⨾ rf ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF TCCOH RELCOV IMMCON.
    generalize dom_release_issued.
    generalize dom_rf_coverable.
    basic_solver 21.
  Qed.

  Lemma release_rf_coverable :
    release ⨾ rf ⨾ ⦗ coverable T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
  Proof using WF TCCOH RELCOV IMMCON.
    seq_rewrite (dom_rel_helper dom_release_rf_coverable).
    basic_solver.
  Qed.

  Lemma release_rf_covered :
    release ⨾ rf ⨾ ⦗ covered T ⦘ ⊆ ⦗ covered T ⦘ ⨾ release ⨾ rf.
  Proof using WF TCCOH RELCOV IMMCON.
    rewrite covered_in_coverable at 1.
      by apply release_rf_coverable.
  Qed.

  Lemma dom_sb_W_rel_issued  :
    dom_rel (sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘) ⊆₁ covered T.
  Proof using TCCOH.
    rewrite issued_in_issuable.
    arewrite (⦗issuable T⦘ ⊆ ⦗dom_cond fwbob (covered T)⦘).
    { unfold issuable. basic_solver 10. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma sb_W_rel_issued  :
    sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗issued T⦘ ⊆ ⦗covered T⦘ ⨾ sb ⨾ ⦗W ∩₁ Rel⦘.
  Proof using TCCOH.
    seq_rewrite (dom_rel_helper dom_sb_W_rel_issued).
    basic_solver.
  Qed.

  Lemma dom_sw_coverable :
    dom_rel (sw ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF TCCOH RELCOV IMMCON.
    unfold imm_s_hb.sw.
    generalize dom_sb_coverable.
    generalize dom_release_rf_coverable.
    generalize covered_in_coverable.
    basic_solver 21.
  Qed.

  Lemma sw_coverable : sw ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
  Proof using WF TCCOH RELCOV IMMCON.
    seq_rewrite (dom_rel_helper dom_sw_coverable).
    basic_solver.
  Qed.

  Lemma sw_covered : sw ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ sw.
  Proof using WF TCCOH RELCOV IMMCON.
    rewrite covered_in_coverable at 1.
      by apply sw_coverable.
  Qed.

  Lemma hb_coverable : hb ⨾ ⦗ coverable T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
  Proof using WF TCCOH RELCOV IMMCON.
    unfold imm_s_hb.hb.
    assert (A: (sb ∪ sw) ⨾ ⦗coverable T⦘ ⊆ ⦗covered T⦘ ⨾ (sb ∪ sw)⁺).
    { relsf.
      rewrite sb_coverable, sw_coverable.
      rewrite <- ct_step; basic_solver. }
    unfold imm_s_hb.hb.
    eapply ct_ind_left with (P:= fun r => r ⨾ ⦗coverable T⦘); eauto with hahn.
    intros k H; rewrite !seqA, H.
    rewrite covered_in_coverable at 1.
    sin_rewrite A.
    arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw)＊) at 1.
    relsf.
  Qed.

Lemma sc_sb_I_dom_C  :
  dom_rel (sc ⨾ sb ⨾ ⦗issued T⦘) ⊆₁ covered T.
Proof using WF IMMCON TCCOH RELCOV.
  cdes IMMCON.
  rewrite (dom_r (wf_scD Wf_sc)).
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

  Lemma dom_hb_coverable :
    dom_rel (hb ⨾ ⦗ coverable T ⦘) ⊆₁ covered T.
  Proof using WF TCCOH RELCOV IMMCON.
    rewrite hb_coverable; basic_solver 10.
  Qed.

  Lemma hb_covered :
    hb ⨾ ⦗ covered T ⦘ ⊆ ⦗covered T⦘ ⨾ hb.
  Proof using WF TCCOH RELCOV IMMCON.
    rewrite covered_in_coverable at 1.
      by apply hb_coverable.
  Qed.

  Lemma dom_urr_coverable l:
    dom_rel (urr l ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.urr.
    generalize dom_hb_coverable.
    generalize dom_sc_coverable.
    generalize dom_rf_coverable.
    generalize covered_in_coverable.
    generalize w_coverable_issued.
    basic_solver 21.
  Qed.

  Lemma urr_coverable l:
    urr l ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite (dom_rel_helper (@dom_urr_coverable l)).
    basic_solver.
  Qed.

  Lemma urr_covered l:
    urr l ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ urr l.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply urr_coverable.
  Qed.

  Lemma dom_c_acq_coverable i l A:
    dom_rel (c_acq i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.c_acq.
    generalize (@dom_urr_coverable l).
    generalize covered_in_coverable.
    generalize dom_release_issued.
    generalize dom_rf_coverable.
    basic_solver 21.
  Qed.

  Lemma c_acq_coverable i l A:
    c_acq i l A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite (dom_rel_helper (@dom_c_acq_coverable i l A)).
    basic_solver.
  Qed.

  Lemma c_acq_covered i l A:
    c_acq i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_acq i l A.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable  at 1.
      by apply c_acq_coverable.
  Qed.

  Lemma dom_c_cur_coverable i l A:
    dom_rel (c_cur i l A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.c_cur.
    generalize (@dom_urr_coverable l).
    basic_solver 21.
  Qed.

  Lemma c_cur_coverable i l A:
    c_cur i l A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
  Proof using WF IMMCON TCCOH RELCOV.
    seq_rewrite (dom_rel_helper (@dom_c_cur_coverable i l A)).
    basic_solver.
  Qed.


  Lemma c_cur_covered i l A:
    c_cur i l A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_cur i l A.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply c_cur_coverable.
  Qed.

  Lemma dom_c_rel_coverable i l l' A:
    dom_rel (c_rel i l l' A ⨾ ⦗ coverable T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.c_rel.
    generalize (@dom_urr_coverable l).
    basic_solver 21.
  Qed.


  Lemma c_rel_coverable i l l' A:
    c_rel i l l' A ⨾ ⦗ coverable T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
  Proof using WF IMMCON TCCOH RELCOV.
    seq_rewrite (dom_rel_helper (@dom_c_rel_coverable i l l' A)).
    basic_solver.
  Qed.


  Lemma c_rel_covered i l l' A:
    c_rel i l l' A ⨾ ⦗ covered T ⦘ ⊆ ⦗issued T⦘ ⨾ c_rel i l l' A.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply c_rel_coverable.
  Qed.

  Lemma t_acq_coverable l thread:
    t_acq thread l (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.t_acq.
    rewrite (dom_r (wf_c_acqD G sc thread l (coverable T))).
    arewrite (⦗(Tid_ thread ∪₁ Init) ∩₁ coverable T⦘ ⊆ ⦗coverable T⦘) by basic_solver.
    rewrite c_acq_coverable.
    basic_solver.
  Qed.

  Lemma t_acq_covered l thread:
    t_acq thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply t_acq_coverable.
  Qed.

  Lemma t_cur_coverable l thread:
    t_cur thread l (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    etransitivity; [by apply t_cur_in_t_acq|].
      by apply t_acq_coverable.
  Qed.

  Lemma t_cur_covered l thread:
    t_cur thread l (covered T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply t_cur_coverable.
  Qed.

  Lemma t_rel_coverable l l' thread:
    t_rel thread l l' (coverable T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    etransitivity; [by apply t_rel_in_t_cur|].
      by apply t_cur_coverable.
  Qed.

  Lemma t_rel_covered l l' thread:
    t_rel thread l l' (covered T) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    rewrite covered_in_coverable at 1.
      by apply t_rel_coverable.
  Qed.

  Lemma S_tm_coverable l :
    S_tm l (coverable T) ⊆₁ issued T.
  Proof using WF TCCOH RELCOV IMMCON.
    unfold CombRelations.S_tm, CombRelations.S_tmr.
    generalize dom_hb_coverable.
    generalize w_coverable_issued.
    generalize covered_in_coverable.
    generalize dom_release_issued.
    generalize dom_rf_coverable.
    basic_solver 21.
  Qed.

  Lemma S_tm_covered l:
    S_tm l (covered T) ⊆₁ issued T.
  Proof using WF TCCOH RELCOV IMMCON.
    rewrite covered_in_coverable at 1.
      by apply S_tm_coverable.
  Qed.

  Lemma msg_rel_issued l:
    dom_rel (msg_rel l ⨾ ⦗ issued T ⦘) ⊆₁ issued T.
  Proof using WF IMMCON TCCOH RELCOV.
    unfold CombRelations.msg_rel.
    generalize dom_release_issued.
    generalize (@dom_urr_coverable l).
    generalize covered_in_coverable.
    basic_solver 21.
  Qed.

Lemma exists_ncov thread (FINDOM : set_finite E) :
  exists n, ~ covered T (ThreadEvent thread n).
Proof using TCCOH.
  destruct (exists_nE G FINDOM thread) as [n HH].
  exists n. intros CC. apply HH.
  eapply coveredE; eauto.
Qed.

Section HbProps.

Notation "'C'" := (covered T).
Notation "'I'" := (issued  T).

Lemma sw_in_Csw_sb :
  sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ sw ∪ sb.
Proof using WF TCCOH RELCOV IMMCON.
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
  rewrite (dom_r (wf_swD WF)).
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
    seq_rewrite (dom_rel_helper dom_release_issued).
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

Lemma hb_in_Chb_sb :
  hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof using WF TCCOH RELCOV IMMCON.
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
         (* TODO: is the last tactic needed? *)
         apply ct_ct. exists y. split; eauto; try by apply ct_step. }
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
End Properties.

End TraversalConfig.
