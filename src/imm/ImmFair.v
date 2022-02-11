Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm. 
Require Import imm_s. 
Require Import FairExecution.
From hahn Require Import Hahn.
Require Import FinExecution.


Definition imm_fair G := fsupp (⦗set_compl is_init⦘ ⨾ (imm.ar G)⁺).
Definition imm_s_fair G sc := fsupp (⦗set_compl is_init⦘ ⨾ (imm_s.ar G sc)⁺).


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
      
End ImmFairProperties.

Lemma fin_exec_imm_s_fair G sc (WF: Wf G) (WFSC: wf_sc G sc)
      (FIN: fin_exec G):
  imm_s_fair G sc. 
Proof. 
  red. red in FIN.
  eapply fsupp_mori.
  2: { eapply fsupp_cross with (s' := set_full); eauto. }
  red. rewrite ct_begin, wf_arE; auto. basic_solver.  
Qed. 

Lemma fin_exec_imm_fair G (WF: Wf G)
      (FIN: fin_exec G):
  imm_fair G. 
Proof. 
  red. red in FIN.
  eapply fsupp_mori.
  2: { eapply fsupp_cross with (s' := set_full); eauto. }
  red. rewrite ct_begin, imm.wf_arE; auto. basic_solver.  
Qed. 

