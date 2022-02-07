Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s imm_s_ppo imm_s_hb imm_s_rfppo.
Require Import imm_hb imm_bob imm imm_ppo. 
Require Import FairExecution.
From hahn Require Import Hahn.


Definition imm_fair G := fsupp (⦗set_compl is_init⦘ ⨾ (ar G)⁺).
Definition imm_s_fair G sc := fsupp (⦗set_compl is_init⦘ ⨾ (imm_s.ar G sc)⁺).


Section ar_rf_ppo_sl_duplicate.
  (* such lemmas exist for imm_s, but not for plain imm. *)
  (* TODO: extract this and unify with existing code *)
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


End ar_rf_ppo_sl_duplicate. 


Section ImmFairProperties.

  Variables (G: execution) (sc: relation actid).
  Hypotheses (WF: Wf G) (WFSC: wf_sc G sc).
  Hypotheses (COM: complete G). 
  Hypotheses (FAIR: mem_fair G).

  Notation "'E'" := (acts_set G).
  Notation "'R'" := (fun x => is_true (is_r (lab G) x)).
  Notation "'W'" := (fun x => is_true (is_w (lab G) x)).
  Notation "'F'" := (fun x => is_true (is_f (lab G) x)).
  
  Lemma fsupp_rf_sb_loc: fsupp (rf G ⨾ sb G ∩ same_loc (lab G)).
  Proof using WF FAIR. 
    apply fsupp_seq; auto using fsupp_rf, fsupp_sb_loc.
  Qed.

  Lemma fsupp_rf_sb_loc_ct (SCpL: sc_per_loc G):
    fsupp (rf G ⨾ sb G ∩ same_loc (lab G))⁺.
  Proof using FAIR WF.
    eapply fsupp_mori with (x := (co G)^* ⨾ rf G ⨾ sb G ∩ same_loc (lab G)).
    2: { apply fsupp_seq; [| by apply fsupp_rf_sb_loc].
         apply fsupp_ct_rt. rewrite ct_of_trans; [| by apply WF].
         apply FAIR. }
    red.
    rewrite ctEE. apply inclusion_bunion_l. intros i _. induction i.
    { simpl. apply seq_mori; basic_solver. }
    rewrite pow_S_end. rewrite IHi.
    arewrite (rf G ≡ ⦗W⦘ ⨾ rf G) at 2.
    { rewrite wf_rfD; basic_solver. }
    hahn_frame.
    etransitivity; [| apply inclusion_t_rt]. rewrite ct_end. hahn_frame_l.
    apply rf_sb_loc_w_in_co; auto.
  Qed.

  Lemma clos_trans_domb_begin {A: Type} (r: relation A) (s: A -> Prop)
        (DOMB_S: domb r s):
    ⦗s⦘ ⨾ r⁺ ≡ (⦗s⦘ ⨾ r)⁺.
  Proof.
    split; [| by apply inclusion_ct_seq_eqv_l].    
    erewrite domb_rewrite with (r := r) at 1; eauto.
    rewrite ct_rotl. rewrite <- seqA. seq_rewrite <- ct_begin. 
    rewrite inclusion_seq_eqv_r. basic_solver.
  Qed. 

  Lemma wf_ar_rf_ppo_loc_ct_inf_helper (r_ar r_ppo: relation actid)
        (R_RFPPO_AC: acyclic (r_ar ∪ rf G ⨾ r_ppo ∩ same_loc (lab G)))
        (R_RFPPO_NI: (r_ar ∪ rf G ⨾ r_ppo ∩ same_loc (lab G)) ⨾ ⦗is_init⦘ ≡ ∅₂)
        (FSUPPr: fsupp (⦗set_compl is_init⦘ ⨾ r_ar⁺))
        (R_PPO_SB: r_ppo ⊆ sb G)
        (R_RFPPO_CLOS: r_ar ⨾ (rf G ⨾ r_ppo ∩ same_loc (lab G))⁺ ⊆ r_ar⁺)
        (SCpL: sc_per_loc G):
    well_founded (⦗set_compl is_init⦘ ⨾ (r_ar ∪ rf G ;; r_ppo ∩ same_loc (lab G))⁺).
  Proof using WF FAIR COM. 
    apply fsupp_well_founded.
    3: { generalize transitive_ct. basic_solver. }
    2: { eapply irreflexive_mori; [| by apply R_RFPPO_AC]; eauto.
         red. basic_solver. } 

    rewrite clos_trans_domb_begin.
    2: { generalize R_RFPPO_NI. basic_solver 10.
         Unshelve. all: by eauto. }

    rewrite seq_union_r.
    eapply fsupp_mori.
    { red. eapply clos_trans_mori, union_mori; [reflexivity| ].
      apply inclusion_seq_eqv_l. }
      
    rewrite ct_unionE. apply fsupp_union.
    { rewrite R_PPO_SB. by apply fsupp_rf_sb_loc_ct. }
    apply fsupp_seq.
    { apply fsupp_ct_rt.
      rewrite R_PPO_SB. by apply fsupp_rf_sb_loc_ct. }

    eapply fsupp_mori; [| by apply FSUPPr].
    red. rewrite rtE, seq_union_r, seq_id_r.
    rewrite seqA, R_RFPPO_CLOS; auto.
    etransitivity.
    2: { rewrite <- ct_of_ct. reflexivity. }
    etransitivity.
    2: { apply inclusion_ct_seq_eqv_l. } 
    apply clos_trans_mori. basic_solver. 
  Qed.

  Lemma wf_ar_rf_ppo_loc_ct_inf_imm
        (IMM_CONS: imm_consistent G)
        (IMM_FAIR: imm_fair G):
    well_founded (⦗set_compl is_init⦘ ⨾ (ar G ∪ rf G ;; ppo G ∩ same_loc (lab G))⁺).
  Proof using WF FAIR COM.
    apply wf_ar_rf_ppo_loc_ct_inf_helper; auto. 
    { by apply IMM_ar_rf_ppo_loc_acyclic. }
    { by apply IMM_no_ar_rf_ppo_loc_to_init. }
    { by apply ppo_in_sb. }
    { by apply IMM_ar_rf_ppo_loc_ct_in_ar_ct. }
    cdes IMM_CONS. by apply coherence_sc_per_loc.
  Qed. 
    
  Lemma wf_ar_rf_ppo_loc_ct_inf_imm_s
        (IMM_CONS: imm_s.imm_consistent G sc)
        (IMM_FAIR: imm_s_fair G sc):
    well_founded (⦗set_compl is_init⦘ ⨾ (imm_s.ar G sc ∪ rf G ;; imm_s_ppo.ppo G ∩ same_loc (lab G))⁺).
  Proof using WF FAIR COM.
    apply wf_ar_rf_ppo_loc_ct_inf_helper; auto. 
    { by apply ar_rf_ppo_loc_acyclic. }
    { by apply no_ar_rf_ppo_loc_to_init. }
    { by apply imm_s_ppo.ppo_in_sb. }
    { by apply ar_rf_ppo_loc_ct_in_ar_ct. }
    cdes IMM_CONS. by apply imm_s_hb.coherence_sc_per_loc.
  Qed. 
  
End ImmFairProperties.
