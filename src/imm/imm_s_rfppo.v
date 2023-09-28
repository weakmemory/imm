Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Events.
Require Import Execution.
Require Import Execution_eco imm_s_hb imm_bob imm_s_ppo imm_s. 
Require Import FinExecution. 
Require Import ImmFair.
Require Import FairExecution.

Set Implicit Arguments.

Section ImmRFRMWPPO.

  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.
  Variable WFSC : wf_sc G sc.

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
  Notation "'ar_int'" := (ar_int G).

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

Lemma ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct :
  (rfe ∪ ar_int) ⨾ rf ⨾ (ppo ∩ same_loc) ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  remember (rfe ∪ ar_int) as ax.
  assert (sb ⨾ sb ⊆ sb) as AA.
  { apply transitiveI. apply sb_trans. }
  
  assert (rfi ⨾ sb ∩ same_loc ⊆ sb ∩ same_loc) as DD.
  { rewrite (rfi_in_sbloc' WF). apply transitiveI. apply sb_same_loc_trans. }

  rewrite rfi_union_rfe.
  rewrite seq_union_l, seq_union_r.
  unionL.
  2: { arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite ppo_in_ar_int.
       arewrite (rfe ⨾ ar_int ⊆ ax ⨾ ax).
       { subst ax. basic_solver 10. }
       arewrite (ax ⊆ ax⁺) at 1.
       arewrite (ax ⊆ ax⁺) at 2. by rewrite ct_unit, ct_ct. }
  subst ax.
  rewrite !seq_union_l.
  unionL.
  { rewrite (dom_l (wf_rfiD WF)).
    rewrite (dom_r (wf_rfeD WF)).
    type_solver. }
  unfold imm_s_ppo.ar_int at 1.
  rewrite !seq_union_l.
  unionL.
  5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
  3: { rewrite (wf_detourD WF).
       rewrite (wf_rfiD WF). type_solver. }
  2: { arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite ppo_rfi_ppo. rewrite <- ct_step.
       rewrite ppo_in_ar_int. eauto with hahn. }
  2: { arewrite_id ⦗W⦘ at 1. rewrite seq_id_l.
       rewrite rfi_in_sb.
       arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite (dom_r (@wf_ppoD G)).
       rewrite (ppo_in_sb WF).
       arewrite (sb ⨾ sb ⨾ sb ⊆ sb).
       { generalize (@sb_trans G). basic_solver. }
       rewrite <- ct_step.
       rewrite w_ex_acq_sb_w_in_ar_int. eauto with hahn. }
  rewrite (dom_r (@wf_ppoD G)).
  rewrite (ppo_in_sb WF).
  rewrite seq_eqv_inter_lr.
  sin_rewrite DD.
  rewrite bob_sb_same_loc_W_in_bob.
  apply clos_trans_mori. rewrite bob_in_ar_int. eauto with hahn.
Qed.

Lemma ar_rf_ppo_loc_in_ar_ct :
  ar ⨾ rf ⨾ ppo ∩ same_loc ⊆ ar⁺.
Proof using WF IMMCON.
  unfold imm_s.ar.
  rewrite unionA, seq_union_l.
  unionL.
  { rewrite wf_scD with (sc:=sc) at 1; [|by apply IMMCON].
    rewrite (dom_l (wf_rfD WF)).
    type_solver. }
  rewrite ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct.
  apply clos_trans_mori. eauto with hahn.
Qed.

Lemma ar_ct_rf_ppo_loc_in_ar_ct :
  ar⁺ ⨾ rf ⨾ ppo ∩ same_loc ⊆ ar⁺.
Proof using WF IMMCON.
  rewrite ct_end at 1. rewrite !seqA.
  rewrite ar_rf_ppo_loc_in_ar_ct.
  apply rt_ct.
Qed.

Lemma ar_rf_ppo_loc_acyclic :
  acyclic (ar ∪ rf ⨾ ppo ∩ same_loc).
Proof using WF COM IMMCON.
  rewrite ct_step with (r:=ar).
  rewrite unionC.
  apply acyclic_absorb.
  { right. apply ar_ct_rf_ppo_loc_in_ar_ct. }
  split.
  2: { red. rewrite ct_of_ct. apply IMMCON. }
  rewrite ppo_loc_in_fr; auto.
  2: { apply coherence_sc_per_loc. by apply IMMCON. }
  rewrite rf_fr; auto. by apply co_acyclic.
Qed.

Lemma ar_ct_rf_ppo_loc_ct_in_ar_ct :
  ar⁺ ⨾ (rf ⨾ ppo ∩ same_loc)⁺ ⊆ ar⁺.
Proof using WF IMMCON.
  intros x y [z [AA BB]].
  apply clos_trans_t1n in BB.
  induction BB.
  2: apply IHBB.
  all: apply ar_ct_rf_ppo_loc_in_ar_ct; auto.
  all: eexists; split; eauto.
Qed.

Lemma ar_rf_ppo_loc_ct_in_ar_ct :
  ar ⨾ (rf ⨾ ppo ∩ same_loc)⁺ ⊆ ar⁺.
Proof using WF IMMCON.
  rewrite ct_step with (r:=ar) at 1. by apply ar_ct_rf_ppo_loc_ct_in_ar_ct.
Qed.

Lemma no_ar_rfppo_rt_to_init :
  ⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊
  ⊆ ⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗set_compl is_init⦘.
Proof using WF IMMCON. 
  rewrite !rtE, !seq_union_r, !seq_union_l, !seq_union_r.
  apply union_mori.
  { clear; basic_solver. }
  rewrite !ct_end.
  hahn_frame_l. hahn_frame_l.
  transitivity ((ar ∪ rf ⨾ ppo ∩ same_loc) ;; <|is_init ∪₁ set_compl is_init|>).
  { rewrite <- set_full_split. clear; basic_solver. }
  rewrite id_union, seq_union_r.
  rewrite no_ar_rf_ppo_loc_to_init; auto.
  now unionL.
Qed.

Lemma fsupp_ar_implies_fsupp_ar_rf_ppo_loc
      (FAIR : mem_fair G)
      (IMM_FAIR   : imm_s_fair G sc) :
  fsupp (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺).
Proof using WF COM IMMCON.  
  rewrite ct_unionE.
  arewrite (ar ⨾ (rf ⨾ ppo ∩ same_loc)＊ ⊆ ar⁺).
  { rewrite rtE, seq_union_r, seq_id_r.
    rewrite ar_rf_ppo_loc_ct_in_ar_ct.
    eauto with hahn. }
  rewrite ct_of_ct.
  assert (fsupp (rf ⨾ ppo ∩ same_loc)⁺) as AA.
  { rewrite ppo_loc_in_fr; auto.
    2: { apply coherence_sc_per_loc. by apply IMMCON. }
    rewrite rf_fr; auto. 
    rewrite ct_of_trans; [apply FAIR| apply WF]. }

  rewrite seq_union_r. 
  apply fsupp_union; auto.
  { apply fsupp_seq; auto. apply fsupp_eqv. }
  rewrite <- seqA, clos_refl_trans_domb_l.
  2: { rewrite ppo_in_sb, no_sb_to_init; auto. basic_solver. }
  rewrite !seqA. 
  apply fsupp_seq; [by apply fsupp_eqv|].
  apply fsupp_seq; auto. 
  now apply fsupp_ct_rt. 
Qed.

(* Lemma fsupp_ar_rf_ppo_loc (FINDOM : set_finite E) : *)
(*   fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺. *)
Lemma fsupp_ar_rf_ppo_loc_fin (FIN : fin_exec G):
  fsupp (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺).
Proof using WFSC WF IMMCON COM.
  apply fsupp_ar_implies_fsupp_ar_rf_ppo_loc; 
    auto using fin_exec_fair, fin_exec_imm_s_fair. 
Qed.

Lemma wf_ar_rf_ppo_loc_ct
      (FSUPP : fsupp (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺)) :
  well_founded (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺).
Proof using WF COM IMMCON.
  apply fsupp_well_founded; auto.
  { eapply irreflexive_mori. 
    2: { now apply ar_rf_ppo_loc_acyclic. }
    red. basic_solver 10. }
  red. ins. apply seq_eqv_l. apply seq_eqv_l in H, H0. desc.
  split; auto. eapply transitive_ct; eauto. 
Qed.

Lemma ar_rf_ppo_loc_in_sb_rf_no_f_sc
      (NOSC : E ∩₁ F ∩₁ Sc ⊆₁ ∅) :
  ar ∪ rf ⨾ ppo ∩ same_loc ⊆ (sb ∪ rf)⁺.
Proof using WF WFSC.
  unfold imm_s.ar. rewrite ar_int_in_sb; auto.
  arewrite_false sc.
  { rewrite (dom_l (wf_scE WFSC)).
    rewrite (dom_l (wf_scD WFSC)).
    rewrite <- !seqA, <- id_inter, <- set_interA.
    rewrite NOSC. basic_solver 1. }
  rewrite rfe_in_rf.
  unionL.
  { basic_solver 1. }
  1,2: now rewrite <- ct_step; eauto with hahn.
  rewrite <- ct_ct, <- !ct_step.
  rewrite (ppo_in_sb WF). basic_solver 10.
Qed.

Lemma fsupp_sb_rf_implies_fsupp_ar_rf_ppo_loc
      (NOSC : E ∩₁ F ∩₁ Sc ⊆₁ ∅)
      (FSUPP : fsupp (⦗set_compl is_init⦘ ⨾ (sb ∪ rf)⁺)) :
  fsupp (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺).
Proof using WF WFSC.
  rewrite ar_rf_ppo_loc_in_sb_rf_no_f_sc; auto.
  now rewrite ct_of_ct.
Qed.


Lemma wf_ar_rf_ppo_loc_ct_inf_imm_s
      (FAIR: mem_fair G)
      (IMM_CONS: imm_s.imm_consistent G sc)
      (IMM_FAIR: imm_s_fair G sc):
  well_founded (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ;; ppo ∩ same_loc)⁺).
Proof using WF COM IMMCON.
  apply wf_ar_rf_ppo_loc_ct_inf_helper; auto. 
  { by apply ar_rf_ppo_loc_acyclic. }
  { by apply no_ar_rf_ppo_loc_to_init. }
  { by apply imm_s_ppo.ppo_in_sb. }
  { by apply ar_rf_ppo_loc_ct_in_ar_ct. }
  cdes IMM_CONS. by apply imm_s_hb.coherence_sc_per_loc.
Qed. 

End ImmRFRMWPPO.
