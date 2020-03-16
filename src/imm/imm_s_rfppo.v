Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import AuxDef Events Execution.
Require Import Execution_eco imm_s_hb imm_s imm_bob imm_s_ppo.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ImmRFRMWPPO.

  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.
  Variable WFSC : wf_sc G sc.

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
  Notation "'ar_int'" := (ar_int G).

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

Lemma ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct :
  (rfe ∪ ar_int) ;; rf ;; (ppo ∩ same_loc) ⊆ (rfe ∪ ar_int)⁺.
Proof using WF.
  remember (rfe ∪ ar_int) as ax.
  assert (sb ;; sb ⊆ sb) as AA.
  { apply transitiveI. apply sb_trans. }
  
  assert (rfi ⨾ sb ∩ same_loc ⊆ sb ∩ same_loc) as DD.
  { rewrite WF.(rfi_in_sbloc'). apply transitiveI. apply sb_same_loc_trans. }

  rewrite rfi_union_rfe.
  rewrite seq_union_l, seq_union_r.
  unionL.
  2: { arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite ppo_in_ar_int.
       arewrite (rfe ⨾ ar_int ⊆ ax ;; ax).
       { subst ax. basic_solver 10. }
       arewrite (ax ⊆ ax⁺) at 1.
       arewrite (ax ⊆ ax⁺) at 2. by rewrite ct_unit, ct_ct. }
  subst ax.
  rewrite !seq_union_l.
  unionL.
  { rewrite (dom_l WF.(wf_rfiD)).
    rewrite (dom_r WF.(wf_rfeD)).
    type_solver. }
  unfold imm_s_ppo.ar_int at 1.
  rewrite !seq_union_l.
  unionL.
  5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
  3: { rewrite WF.(wf_detourD).
       rewrite WF.(wf_rfiD). type_solver. }
  2: { arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite ppo_rfi_ppo. rewrite <- ct_step.
       rewrite ppo_in_ar_int. eauto with hahn. }
  2: { arewrite_id ⦗W⦘ at 1. rewrite seq_id_l.
       rewrite rfi_in_sb.
       arewrite (ppo ∩ same_loc ⊆ ppo).
       rewrite (dom_r (@wf_ppoD G)).
       rewrite WF.(ppo_in_sb).
       arewrite (sb ⨾ sb ⨾ sb ⊆ sb).
       { generalize (@sb_trans G). basic_solver. }
       rewrite <- ct_step.
       rewrite w_ex_acq_sb_w_in_ar_int. eauto with hahn. }
  rewrite (dom_r (@wf_ppoD G)).
  rewrite WF.(ppo_in_sb).
  rewrite seq_eqv_inter_lr.
  sin_rewrite DD.
  rewrite bob_sb_same_loc_W_in_bob.
  apply clos_trans_mori. rewrite bob_in_ar_int. eauto with hahn.
Qed.

Lemma ar_rf_ppo_loc_in_ar_ct :
  ar ;; rf ;; ppo ∩ same_loc ⊆ ar⁺.
Proof using WF IMMCON.
  unfold imm_s.ar.
  rewrite unionA, seq_union_l.
  unionL.
  { rewrite wf_scD with (sc:=sc) at 1; [|by apply IMMCON].
    rewrite (dom_l WF.(wf_rfD)).
    type_solver. }
  rewrite ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct.
  apply clos_trans_mori. eauto with hahn.
Qed.

Lemma ar_ct_rf_ppo_loc_in_ar_ct :
  ar⁺ ;; rf ;; ppo ∩ same_loc ⊆ ar⁺.
Proof using WF IMMCON.
  rewrite ct_end at 1. rewrite !seqA.
  rewrite ar_rf_ppo_loc_in_ar_ct.
  apply rt_ct.
Qed.

Lemma ar_rf_ppo_loc_acyclic :
  acyclic (ar ∪ rf ;; ppo ∩ same_loc).
Proof using WF COM IMMCON.
  rewrite ct_step with (r:=ar).
  rewrite unionC.
  apply acyclic_absorb.
  { right. apply ar_ct_rf_ppo_loc_in_ar_ct. }
  split.
  2: { red. rewrite ct_of_ct. apply IMMCON. }
  rewrite (@wf_ppoD G).
  rewrite WF.(ppo_in_sb).
  rewrite seq_eqv_inter_ll.
  rewrite seq_eqv_inter_lr.
  rewrite r_sb_loc_w_in_fri; auto.
  2: { apply coherence_sc_per_loc. by apply IMMCON. }
  arewrite (fri G ⊆ fr).
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

Lemma wf_ar_rf_ppo_loc_ct :
  well_founded (ar ∪ rf ;; ppo ∩ same_loc)⁺.
Proof using WF WFSC COM IMMCON.
  eapply wf_finite; auto.
  { red. rewrite ct_of_ct. apply ar_rf_ppo_loc_acyclic; auto. }
  rewrite (dom_l (wf_arE WF WFSC)).
  rewrite (dom_l (wf_rfE WF)). rewrite !seqA.
  rewrite <- seq_union_r.
  rewrite inclusion_ct_seq_eqv_l.
  red. basic_solver.
Qed.

End ImmRFRMWPPO.
