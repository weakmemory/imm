(* Require Import imm_s imm_s_ppo imm_s_hb.  *)
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_hb imm_bob imm imm_ppo. 
From hahn Require Import Hahn.
Require Import ImmFair.
Require Import FairExecution. 


Section ImmRfPpo.
  (* TODO: unify with lemmas for imm_s *)
  Variables (G: execution).
  Hypotheses (WF: Wf G).
  Hypotheses (COM: complete G). 


  Lemma IMM_ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct :
    (rfe G ∪ imm_ppo.ar_int G) ⨾ rf G ⨾ (ppo G ∩ same_loc (lab G)) ⊆ (rfe G ∪ imm_ppo.ar_int G)⁺.
  Proof using WF.
    remember (rfe G ∪ imm_ppo.ar_int G) as ax.
    assert (sb G ⨾ sb G ⊆ sb G) as AA.
    { apply transitiveI. apply sb_trans. }
    
    assert (rfi G ⨾ sb G ∩ same_loc (lab G) ⊆ sb G ∩ same_loc (lab G)) as DD.
    { rewrite (rfi_in_sbloc' WF). apply transitiveI. apply sb_same_loc_trans. }
    
    rewrite rfi_union_rfe.
    rewrite seq_union_l, seq_union_r.
    unionL.
    2: { arewrite (ppo G ∩ same_loc (lab G) ⊆ ppo G).
         rewrite ppo_in_ar_int.
         arewrite (rfe G ⨾ imm_ppo.ar_int G ⊆ ax  ⨾ ax).
         { subst ax. basic_solver 10. }
         arewrite (ax ⊆ ax⁺) at 1.
         arewrite (ax ⊆ ax⁺) at 2. by rewrite ct_unit, ct_ct. }
    subst ax.
    rewrite !seq_union_l.
    unionL.
    { rewrite (dom_l (wf_rfiD WF)).
      rewrite (dom_r (wf_rfeD WF)).
      type_solver. }
    unfold imm_ppo.ar_int at 1.
    rewrite !seq_union_l.
    unionL.
    5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
    3: { rewrite (wf_detourD WF).
         rewrite (wf_rfiD WF). type_solver. }
    2: { arewrite (ppo G ∩ same_loc (lab G) ⊆ ppo G).
         rewrite ppo_rfi_ppo. rewrite <- ct_step.
         rewrite ppo_in_ar_int. eauto with hahn. }
    2: { arewrite_id ⦗is_w (lab G)⦘ at 1. rewrite seq_id_l.
         rewrite rfi_in_sb.
         arewrite (ppo G ∩ same_loc (lab G) ⊆ ppo G).
         rewrite (dom_r (@wf_ppoD G)).
         rewrite (ppo_in_sb WF).
         arewrite (sb G ⨾ sb G ⨾ sb G ⊆ sb G).
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

  Lemma IMM_ar_rf_ppo_loc_in_ar_ct :
    ar G ⨾ rf G ⨾ ppo G ∩ same_loc (lab G) ⊆ (ar G)⁺.
  Proof using WF.
    unfold imm.ar.
    rewrite unionA, seq_union_l.
    unionL.
    { rewrite wf_pscD, wf_rfD; auto. type_solver. }
    rewrite IMM_ar_int_rfe_rf_ppo_loc_in_ar_int_rfe_ct.
    apply clos_trans_mori. eauto with hahn.
  Qed.

  Lemma IMM_ar_ct_rf_ppo_loc_in_ar_ct :
    (ar G)⁺ ⨾ rf G ⨾ ppo G ∩ same_loc (lab G) ⊆ (ar G)⁺.
  Proof using WF.
    rewrite ct_end at 1. rewrite !seqA.
    rewrite IMM_ar_rf_ppo_loc_in_ar_ct.
    apply rt_ct.
  Qed.
  
  Lemma IMM_ar_ct_rf_ppo_loc_ct_in_ar_ct:
    (ar G)⁺ ⨾ (rf G ⨾ ppo G ∩ same_loc (lab G))⁺ ⊆ (ar G)⁺.
  Proof using WF.
    intros x y [z [AA BB]].
    apply clos_trans_t1n in BB.
    induction BB.
    2: apply IHBB.
    all: apply IMM_ar_ct_rf_ppo_loc_in_ar_ct; auto.
    all: eexists; split; eauto.
  Qed.

  Lemma IMM_ar_rf_ppo_loc_ct_in_ar_ct :
    (ar G) ⨾ (rf G ⨾ ppo G ∩ same_loc (lab G))⁺ ⊆ (ar G)⁺.
  Proof using WF.
    rewrite ct_step with (r:=ar G) at 1.
    by apply IMM_ar_ct_rf_ppo_loc_ct_in_ar_ct.
  Qed.

  Lemma IMM_ppo_loc_in_fr 
        (SPL : sc_per_loc G) :
    ppo G ∩ same_loc (lab G) ⊆ fr G.
  Proof using WF COM.
    rewrite wf_ppoD.
    rewrite (ppo_in_sb WF).
    rewrite seq_eqv_inter_ll.
    rewrite seq_eqv_inter_lr.
    rewrite r_sb_loc_w_in_fri; auto.
    apply fri_in_fr.
  Qed.
  
  Lemma IMM_ar_rf_ppo_loc_acyclic
    (CONS: imm_consistent G):
    acyclic (ar G ∪ rf G ⨾ ppo G ∩ same_loc (lab G)).
  Proof using WF COM.
    rewrite ct_step with (r:=ar G).
    rewrite unionC.
    apply acyclic_absorb.
    { right. apply IMM_ar_ct_rf_ppo_loc_in_ar_ct. }
    split.
    2: { red. rewrite ct_of_ct. apply CONS. }
    rewrite IMM_ppo_loc_in_fr; auto.
    2: { apply coherence_sc_per_loc. by apply CONS. }
    rewrite rf_fr; auto. by apply co_acyclic.
  Qed.

  Lemma IMM_no_ar_to_init : ar G ⨾ ⦗is_init⦘ ≡ ∅₂.
  Proof using WF.
    split; [|basic_solver].
    unfold ar.
    rewrite (ar_int_in_sb WF). rewrite no_sb_to_init.
    rewrite wf_pscD. 
    rewrite (wf_rfeD WF).
    rewrite seq_union_l. unionL; [|basic_solver].
    rewrite (init_w WF). type_solver 10.
  Qed.

  Lemma IMM_no_ar_rf_ppo_loc_to_init:
    (ar G ∪ rf G ⨾ ppo G ∩ same_loc (lab G)) ⨾ ⦗is_init⦘ ≡ ∅₂.
  Proof using WF.
    split; [|basic_solver].
    rewrite seq_union_l, seqA, IMM_no_ar_to_init; auto.
    arewrite (ppo G ∩ same_loc (lab G) ⊆ ppo G).
    rewrite (ppo_in_sb WF). rewrite no_sb_to_init.
    basic_solver.
  Qed.

  Lemma wf_ar_rf_ppo_loc_ct_inf_imm 
        (IMM_CONS: imm_consistent G)
        (IMM_FAIR: imm_fair G)
        (FAIR: mem_fair G):
    well_founded (⦗set_compl is_init⦘ ⨾ (ar G ∪ rf G ;; ppo G ∩ same_loc (lab G))⁺).
  Proof using WF COM.
    apply wf_ar_rf_ppo_loc_ct_inf_helper; auto. 
    { by apply IMM_ar_rf_ppo_loc_acyclic. }
    { by apply IMM_no_ar_rf_ppo_loc_to_init. }
    { by apply ppo_in_sb. }
    { by apply IMM_ar_rf_ppo_loc_ct_in_ar_ct. }
    cdes IMM_CONS. by apply coherence_sc_per_loc.
  Qed. 

End ImmRfPpo. 
