From hahn Require Import Hahn.

Require Import AuxDef Events Execution.
Require Import Execution_eco imm_s_hb imm_s imm_bob.
Require Import imm_s_ppo CombRelations.
Require Import imm_s_rfppo.
Require Import FinExecution.

Require Import TraversalOrder.
Require Import TLSCoherency.
Require Import IordCoherency.
Require Import TlsEventSets.
Require Import AuxRel.

Set Implicit Arguments.

Section TlsProperties.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  (* Variable IMMCON : imm_consistent G sc. *)
  Variable WFSC: wf_sc G sc. 
  Variable SCPL: sc_per_loc G. 

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


Context
  (T : trav_label -> Prop)
  (TLSCOH  : tls_coherent G T)
  (IORDCOH : iord_coherent G sc T)
  (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T).

  (* TODO: decide if it's needed in the end *)
  (* Lemma dom_rel_iord_parts (a1 a2: trav_action) (r: relation actid) *)
  (*       (R_IORD: ⦗action ↓₁ eq a1⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a2⦘ *)
  (*                ⊆ iord_simpl G sc) *)
  (*       (R_E_ENI: r ⊆ E × (E \₁ is_init)): *)
  (*   dom_rel (r ⨾ ⦗event ↑₁ (T ∩₁ action ↓₁ eq a2)⦘) *)
  (*   ⊆₁ event ↑₁ (T ∩₁ action ↓₁ eq a1). *)
  (* Lemma dom_rel_iord_parts (a1 a2: trav_action) (r: relation actid) *)
  (*       (R_IORD: ⦗action ↓₁ eq a1⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a2⦘ *)
  (*                ⊆ iord_simpl G sc): *)
  (*   dom_rel (r ⨾ ⦗event ↑₁ (T ∩₁ action ↓₁ eq a2)⦘) *)
  (*   ⊆₁ event ↑₁ (T ∩₁ action ↓₁ eq a1). *)
  (* Proof using WF TLSCOH IORDCOH WFSC SCPL.  *)
  (*   eapply dom_rel_collect_event with (b := a1); [basic_solver| ]. *)
  (*   apply set_subset_inter_r. split; [| basic_solver]. *)
  (*   rewrite set_interC, id_inter. sin_rewrite R_IORD. *)
  (*   eapply iord_coh_implies_iord_simpl_coh'; eauto. *)
  (* Qed. *)

  Notation "'C'" := (covered T).
  Notation "'I'" := (issued T).

  Lemma dom_sb_coverable :
    dom_rel (sb ⨾ ⦗ coverable G sc T ⦘) ⊆₁ C.
  Proof using TLSCOH.
    unfold coverable, covered. rewrite id_inter, <- seqA. 
    eapply dom_rel_iord_ext_parts.
    3: { by apply init_covered. }
    2: { rewrite sb_E_ENI. basic_solver. }
    unfold iord_simpl, SB. 
    rewrite <- ct_step, <- inclusion_union_r1 with (r' := sc).
    rewrite inclusion_seq_eqv_r with (r := sb). intuition.
  Qed.

  Lemma dom_sb_covered :
    dom_rel (sb ⨾ ⦗ C ⦘) ⊆₁ C.
  Proof using WF TLSCOH IORDCOH.
    rewrite covered_in_coverable at 1; eauto. apply dom_sb_coverable.  
  Qed.

  Lemma sb_coverable :
    sb ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗ C ⦘ ⨾ sb.
  Proof using TLSCOH.
   rewrite (dom_rel_helper dom_sb_coverable). basic_solver.
  Qed.

  Lemma sb_covered :
    sb ⨾ ⦗ C ⦘ ≡ ⦗ C ⦘ ⨾ sb ⨾ ⦗ C ⦘.
  Proof using WF TLSCOH IORDCOH .
    rewrite (dom_rel_helper dom_sb_covered). basic_solver.
  Qed.

  Lemma dom_rf_coverable :
    dom_rel (rf ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH. 
    unfold coverable, issued. rewrite id_inter, <- seqA.
    apply dom_rel_iord_ext_parts.
    3: by apply init_issued.
    2: rewrite rf_E_ENI; basic_solver. 
    transitivity (RF G); [| unfold iord_simpl; basic_solver 10].
    unfold RF. hahn_frame. apply map_rel_mori; [done| ].
    rewrite wf_rfD, wf_rfE; eauto. basic_solver 10. 
  Qed. 

  Lemma dom_rf_covered :
    dom_rel (rf ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH. 
    rewrite covered_in_coverable; eauto. apply dom_rf_coverable. 
  Qed.

  Lemma rf_coverable :
    rf ⨾ ⦗coverable G sc T⦘ ⊆ ⦗I⦘ ⨾ rf.
  Proof using WF TLSCOH.
    rewrite (dom_rel_helper dom_rf_coverable).
    basic_solver.
  Qed.

  Lemma rf_covered:
    rf ⨾ ⦗C⦘ ≡ ⦗I⦘ ⨾ rf ⨾ ⦗C⦘.
  Proof using WF TLSCOH IORDCOH.
    rewrite (dom_rel_helper dom_rf_covered). basic_solver.
  Qed.

  Lemma dom_sc_coverable :
    dom_rel (sc ⨾ ⦗ coverable G sc T ⦘) ⊆₁ C.
  Proof using WF TLSCOH WFSC.
    unfold coverable, covered. rewrite id_inter, <- seqA.
    apply dom_rel_iord_ext_parts.
    3: by apply init_covered.
    2: { erewrite (sc_E_ENI _ _ WF WFSC). basic_solver. } 
    transitivity (SB G sc); [| unfold iord_simpl; basic_solver 10].
    unfold SB. hahn_frame. apply map_rel_mori; [done| ].
    rewrite <- ct_step. rewrite (wf_scE WFSC). basic_solver 10.
  Qed. 
    
  Lemma dom_sc_covered :
    dom_rel (sc ⨾ ⦗ C ⦘) ⊆₁ C.
  Proof using WF TLSCOH IORDCOH WFSC. 
    rewrite covered_in_coverable at 1; eauto. apply dom_sc_coverable. 
  Qed.

  Lemma sc_coverable  :
    sc ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗C⦘ ⨾ sc.
  Proof using WF TLSCOH WFSC.
    seq_rewrite (dom_rel_helper dom_sc_coverable). basic_solver.
  Qed.

  Lemma sc_covered :
    sc ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ sc.
  Proof using WF TLSCOH IORDCOH WFSC. 
    seq_rewrite (dom_rel_helper dom_sc_covered). basic_solver.
  Qed.

  Lemma ar_int_ct_issuable_in_I:
    dom_rel (⦗W⦘ ⨾ (ar_int G)^+ ⨾ ⦗issuable G sc T⦘) ⊆₁ I. 
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA. 
    apply dom_rel_iord_ext_parts.
    3: { rewrite init_issued; eauto. basic_solver. }
    2: { rewrite ar_int_in_sb, ct_of_trans, wf_sbE, no_sb_to_init; try basic_solver.
         apply sb_trans. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    hahn_frame. apply clos_trans_mori. unfold ar. basic_solver. 
  Qed.

  Lemma ar_coverable_in_CI  :
    dom_rel (ar ⨾ ⦗coverable G sc T⦘) ⊆₁ C ∪₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    unfold imm_s.ar.
    rewrite !seq_union_l.
    rewrite ar_int_in_sb, rfe_in_rf; eauto. 
    rewrite sb_coverable, rf_coverable, sc_coverable.
    basic_solver.
  Qed.

  Lemma ar_C_in_CI  :
    dom_rel (ar ⨾ ⦗C⦘) ⊆₁ C ∪₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    unfold imm_s.ar.
    rewrite !seq_union_l.
    rewrite (ar_int_in_sb WF).
    arewrite (rfe ⊆ rf).
    rewrite sb_covered, rf_covered.
    rewrite sc_covered.
    basic_solver.
  Qed.
  
  Lemma ar_rf_ppo_loc_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    unfold issuable, issued. rewrite id_inter, <- !seqA. 
    eapply dom_rel_iord_ext_parts.
    3: by apply init_issued.
    2: rewrite ar_rf_ppo_loc_ct_E_ENI; basic_solver.  
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| red; intro; apply proj2]. 
    unfold AR. basic_solver 10.
  Qed.

  Lemma ar_rfrmw_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))⁺ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite issued_in_issuable at 1; eauto. apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite issued_in_issuable at 1; eauto. apply ar_rfrmw_ct_issuable_in_I. 
  Qed.

  Lemma ar_rf_ppo_loc_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc))＊ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union; unionL.
    { basic_solver. }
    apply ar_rf_ppo_loc_ct_I_in_I.
  Qed.

  Lemma ar_rfrmw_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_rt_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_issuable_in_I:
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc)) ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    rewrite ct_step with (r := ar ∪ rf ⨾ (ppo ∩ same_loc)).
    by apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.     

  Lemma ar_rfrmw_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ (ppo ∩ same_loc)) ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite ct_step with (r := ar ∪ rf ⨾ (ppo ∩ same_loc)).
    rewrite issued_in_issuable at 1; eauto. apply ar_rf_ppo_loc_ct_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_I_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_I_in_I.
  Qed.

  Lemma ar_ct_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    arewrite (ar ⊆ ar ∪ rf ⨾ rmw). by apply ar_rfrmw_ct_issuable_in_I.
  Qed.

  Lemma ar_ct_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite issued_in_issuable at 1; eauto. apply ar_ct_issuable_in_I. 
  Qed.

  Lemma ar_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH WFSC.
    rewrite ct_step with (r:=ar). by apply ar_ct_issuable_in_I.
  Qed.

  Lemma ar_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite issued_in_issuable at 1; eauto. apply ar_issuable_in_I. 
  Qed.

  Lemma W_ar_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite dom_eqv1. rewrite ar_coverable_in_CI.
    rewrite set_inter_union_r; unionL.
    2: basic_solver.
    eapply w_covered_issued; eauto.
  Qed.

  Lemma W_ar_C_in_I  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite covered_in_coverable; eauto. apply W_ar_coverable_in_I.
  Qed.

  Lemma W_ar_coverable_issuable_in_CI  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply W_ar_coverable_in_I. }
    apply ar_issuable_in_I.
  Qed.


  Lemma ar_rt_I_in_I  :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH WFSC.
    rewrite rtE, !seq_union_l, !seq_union_r, seq_id_l, dom_union.
    unionL; [basic_solver|]. by apply ar_ct_I_in_I.
  Qed.

  Lemma dom_W_sb_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using TLSCOH IORDCOH. 
    rewrite sb_coverable; auto.
    etransitivity.
    2: by eapply w_covered_issued; eauto. 
    basic_solver.
  Qed.
  
  Lemma dom_W_sb_C_in_I  :
    dom_rel (⦗W⦘ ⨾ sb ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite covered_in_coverable; eauto. apply dom_W_sb_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_issuable_in_I:
    dom_rel (rf ⨾ ppo ∩ same_loc ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter. 
    rewrite <- !seqA. eapply dom_rel_iord_ext_parts.
    3: { by erewrite init_issued; eauto. }
    2: { rewrite wf_rfE, ppo_in_sb, wf_sbE, no_sb_to_init; basic_solver. }
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| intro; apply proj2].
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver].
    unfold AR. hahn_frame.
    apply map_rel_mori; [done| ]. hahn_frame.
    rewrite <- ct_step. rewrite (dom_l (wf_rfD WF)) at 1. basic_solver 10.
  Qed. 

  Lemma rf_ppo_loc_coverable_in_I:
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite rfi_union_rfe, !seq_union_l, dom_union.
    unionL.
    2: { rewrite (dom_r (@wf_ppoD G)), seq_eqv_inter_lr, !seqA.
         rewrite <- id_inter. rewrite w_coverable_issued; eauto. 
         rewrite issued_in_issuable at 1; eauto. rewrite rfe_in_rf. 
         eapply rf_ppo_loc_issuable_in_I. }
    rewrite (dom_l (wf_rfiD WF)), seqA.
    rewrite inclusion_inter_l1. rewrite (ppo_in_sb WF), rfi_in_sb.
    sin_rewrite sb_sb. rewrite dom_W_sb_coverable_in_I; auto.
  Qed.

  Lemma rfrmw_coverable_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH . 
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_C_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite covered_in_coverable; eauto. apply rf_ppo_loc_coverable_in_I.
  Qed.

  Lemma rfrmw_C_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite covered_in_coverable; eauto. apply rfrmw_coverable_in_I.
  Qed.

  Lemma rf_ppo_loc_coverable_issuable_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { apply rf_ppo_loc_coverable_in_I. }
    apply rf_ppo_loc_issuable_in_I. 
  Qed.

  Lemma rfrmw_coverable_issuable_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma rf_ppo_loc_I_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite issued_in_issuable at 1; eauto. apply rf_ppo_loc_issuable_in_I. 
  Qed.

  Lemma rfrmw_I_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_I_in_I.
  Qed.

  Lemma rf_ppo_loc_rt_I_in_I  :
    dom_rel ((rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    apply dom_rel_clos_refl_trans_eqv.
    rewrite seqA. apply rf_ppo_loc_I_in_I. 
  Qed.

  Lemma rfrmw_rt_I_in_I  :
    dom_rel ((rf ⨾ rmw)＊ ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_rt_I_in_I.
  Qed.

  Lemma rf_ppo_loc_CI_in_I  :
    dom_rel (rf ⨾ (ppo ∩ same_loc) ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite id_union, !seq_union_r, dom_union.
    unionL.
    { by apply rf_ppo_loc_C_in_I. }
      by apply rf_ppo_loc_I_in_I.
  Qed.

  Lemma rfrmw_CI_in_I  :
    dom_rel (rf ⨾ rmw ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH .
    rewrite (rmw_in_ppo_loc WF). by apply rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_coverable_in_CI  :
    dom_rel ((ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗coverable G sc T⦘) ⊆₁ C ∪₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite seq_union_l, dom_union, !seqA.
    unionL.
    { by apply ar_coverable_in_CI. }
    rewrite rf_ppo_loc_coverable_in_I; eauto with hahn.
  Qed.

  Lemma ar_rfrmw_coverable_in_CI  :
    dom_rel ((ar ∪ rf ⨾ rmw) ⨾ ⦗coverable G sc T⦘) ⊆₁ C ∪₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_coverable_in_CI.
  Qed.

  Lemma ar_rf_ppo_loc_C_in_CI  :
    dom_rel ((ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗C⦘) ⊆₁ C ∪₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite covered_in_coverable at 1; eauto. 
    apply ar_rf_ppo_loc_coverable_in_CI.
  Qed.

  Lemma ar_rfrmw_C_in_CI  :
    dom_rel ((ar ∪ rf ⨾ rmw) ⨾ ⦗C⦘) ⊆₁ C ∪₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_C_in_CI.
  Qed.

  Lemma ar_rf_ppo_loc_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite seq_union_l, seq_union_r, dom_union; unionL.
    { apply W_ar_coverable_issuable_in_CI. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    apply rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_coverable_issuable_in_I.
  Qed.

  Lemma ar_CI_in_CI  :
    dom_rel (⦗W⦘ ⨾ ar ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH . 
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply W_ar_C_in_I. }
    apply ar_I_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite seq_union_l, seq_union_r, dom_union; unionL.
    { apply ar_CI_in_CI. }
    arewrite_id ⦗W⦘. rewrite seq_id_l.
    apply rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rfrmw_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw) ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). by apply ar_rf_ppo_loc_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    intros x [y HH].
    destruct_seq HH as [AA BB].
    apply clos_trans_tn1 in HH.
    induction HH as [y HH|y z QQ].
    { eapply ar_rf_ppo_loc_coverable_issuable_in_I. basic_solver 10. }
    apply clos_tn1_trans in HH.
    destruct QQ as [QQ|QQ].
    2: { apply IHHH. right.
         apply issued_in_issuable; eauto.
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
    { left. apply covered_in_coverable; eauto.
      apply dom_sc_coverable. exists z. basic_solver. }
    { right. apply issued_in_issuable; eauto.
      apply dom_rf_coverable. exists z.
      do 2 red in QQ. basic_solver. }
    left. apply covered_in_coverable; eauto.
    apply dom_sb_coverable. exists z.
    apply seq_eqv_r. split; auto. by apply ar_int_in_sb.
  Qed.

  Lemma ar_rfrmw_ct_coverable_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗coverable G sc T ∪₁ issuable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_ct_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite covered_in_coverable; eauto.
    rewrite issued_in_issuable at 1; eauto. 
    apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_ct_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_ct_CI_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    { generalize w_coverable_issued. basic_solver. }
    arewrite (coverable G sc T ⊆₁ coverable G sc T ∪₁ issuable G sc T).
    apply ar_rf_ppo_loc_ct_coverable_issuable_in_I.
  Qed.

  Lemma ar_rfrmw_rt_coverable_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗coverable G sc T⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_rt_coverable_in_I.
  Qed.

  Lemma ar_rf_ppo_loc_rt_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊ ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    { generalize w_covered_issued. basic_solver. }
    apply ar_rf_ppo_loc_ct_CI_in_I.
  Qed.

  Lemma ar_rfrmw_rt_CI_in_I  :
    dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)＊ ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite (rmw_in_ppo_loc WF). apply ar_rf_ppo_loc_rt_CI_in_I.
  Qed.
  
  Lemma ar_rt_C_in_I  :
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗C⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    unfolder.
    ins. desf.
    apply clos_rt_rtn1 in H0.
    induction H0.
    { eapply w_covered_issued; basic_solver. }
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
    dom_rel (⦗W⦘ ⨾ ar＊ ⨾ ⦗C ∪₁ I⦘) ⊆₁ I.
  Proof using WF WFSC TLSCOH IORDCOH.
    rewrite id_union, !seq_union_r, dom_union; unionL.
    { by apply ar_rt_C_in_I. }
      by apply ar_rt_I_in_I.
  Qed.

  Lemma sbCsbI_CsbI   :
    sb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
    ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ sb.
  Proof using WF TLSCOH IORDCOH.
    rewrite id_union, !seq_union_r, !seq_union_l.
    apply union_mori.
    { rewrite sb_covered; eauto. basic_solver. }
    generalize (@sb_trans G). basic_solver 10.
  Qed.

  Lemma dom_rfe_ppo_issuable_in_I :
    dom_rel (rfe ⨾ ppo ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter. rewrite <- !seqA.
    apply dom_rel_iord_ext_parts.
    3: { rewrite init_issued; eauto. basic_solver. }
    2: { rewrite wf_rfeE, ppo_in_sb, wf_sbE, no_sb_to_init; basic_solver. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| intro; apply proj2].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    rewrite (dom_l (wf_rfeD WF)). hahn_frame.
    rewrite <- ct_unit, <- ct_step. unfold ar, ar_int.
    apply seq_mori; basic_solver 10.
  Qed.

  Lemma dom_rfe_ppo_issued :
    dom_rel (rfe ⨾ ppo ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto. apply dom_rfe_ppo_issuable_in_I. 
  Qed.

  Lemma dom_detour_ppo_issuable_in_I :
    dom_rel (detour ⨾ ppo ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter. rewrite <- !seqA.
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; basic_solver. }
    2: { rewrite detour_in_sb, ppo_in_sb, wf_sbE, no_sb_to_init; basic_solver. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| intro; apply proj2].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    rewrite (dom_l (wf_detourD WF)). hahn_frame.
    rewrite <- ct_unit, <- ct_step. unfold ar, ar_int.
    apply seq_mori; basic_solver 10.
  Qed.

  Lemma dom_detour_rfe_ppo_issuable :
    dom_rel ((detour ∪ rfe) ⨾ ppo ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    repeat case_union _ _. rewrite dom_union.
    rewrite dom_rfe_ppo_issuable_in_I, dom_detour_ppo_issuable_in_I. basic_solver.
  Qed.
  
  Lemma dom_detour_rfe_ppo_issued :
    dom_rel ((detour ∪ rfe) ⨾ ppo ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto. 
    apply dom_detour_rfe_ppo_issuable.
  Qed.

  (* Lemma R_acq_sb_issuable_in_I: *)
  (*   dom_rel (⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I. *)
  (* Proof using. *)
  (*   unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA. *)
  (*   apply dom_rel_iord_ext_parts. *)
  (*   3: { rewrite init_issued. basic_solver. } *)
  (*   2: { rewrite wf_sbE, no_sb_to_init; basic_solver. } *)
  (*   transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10]. *)
  (*   erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2]. *)
  (*   unfold AR. hahn_frame. apply map_rel_mori; [done| ]. *)
  (*   hahn_frame. rewrite <- ct_step. unfold ar, ar_int. *)
  (*   apply seq_mori; basic_solver 10. *)

  Lemma dom_detour_rfe_acq_sb_issuable :
    dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA.
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; eauto. basic_solver. }
    2: { rewrite detour_in_sb, wf_sbE, wf_rfeE, no_sb_to_init; basic_solver. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    rewrite (dom_l (wf_detourD WF)), (dom_l (wf_rfeD WF)), <- seq_union_r.
    hahn_frame. rewrite <- ct_unit, <- ct_step.
    unfold ar, ar_int, bob. apply seq_mori; basic_solver 10.
  Qed.

  Lemma dom_detour_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH. 
    rewrite issued_in_issuable at 1; eauto.
    apply dom_detour_rfe_acq_sb_issuable.
  Qed.

  Lemma rfe_ar_int_issuable_in_I  :
    dom_rel (⦗W⦘ ⨾ (rfe ∪ ar_int G) ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA.
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; eauto. basic_solver. }
    2: { rewrite rfe_in_rf, wf_rfE, ar_int_in_sb, wf_sbE, no_sb_to_init, no_rf_to_init; basic_solver 10. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    unfold AR. hahn_frame.
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    apply map_rel_mori; [done|]. hahn_frame.
    rewrite <- ct_step. unfold ar. basic_solver. 
  Qed. 

  Lemma dom_detour_rfe_rmw_rfi_rmw_rt_issuable_in_I:
    dom_rel ((((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊) ⨾ rmw) ⨾ ⦗issuable G sc T⦘) ⊆₁ issued T.
  Proof using WF TLSCOH IORDCOH.
    rewrite !seqA. seq_rewrite rt_seq_swap. rewrite seqA.
    assert (dom_rel ((rfi ⨾ rmw)＊ ⨾ ⦗issuable G sc T⦘) ⊆₁ (issuable G sc T)) as D2.
    { apply dom_rel_clos_refl_trans_eqv.
      transitivity (issued T); [| apply issued_in_issuable; auto].
      rewrite <- rf_ppo_loc_issuable_in_I; eauto.
      rewrite rfi_in_rf, rmw_in_ppo_loc; auto. basic_solver. }
    apply dom_rel_helper in D2. rewrite D2.
    rewrite <- !seqA. do 2 rewrite dom_seq. rewrite seqA.
    
    unfold issuable. rewrite id_inter. rewrite <- !seqA. 
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; eauto. basic_solver. }
    2: { rewrite rmw_in_sb, detour_in_sb, wf_rfeE, wf_sbE, no_sb_to_init; basic_solver. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    rewrite (dom_l (wf_detourD WF)), (dom_l (wf_rfeD WF)), <- seq_union_r.
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    hahn_frame. 
    rewrite <- ct_unit, <- ct_step. unfold ar. apply seq_mori.
    { unfold ar_int. basic_solver 10. }
    rewrite rmw_in_ar_int; auto. basic_solver 10. 
  Qed. 

  Lemma dom_detour_rfe_rmw_rfi_rmw_rt_I_in_I:
    dom_rel ((((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊) ⨾ rmw) ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH. 
    rewrite issued_in_issuable at 1; eauto.
    by apply dom_detour_rfe_rmw_rfi_rmw_rt_issuable_in_I.
  Qed.

  Lemma dom_detour_rmwrfi_rfe_acq_sb_issuable :
    dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    remember (detour ∪ rfe) as DR.
    rewrite rtE. repeat case_union _ _. rewrite dom_union. subst DR.
    apply set_subset_union_l. split.
    { rewrite seq_id_l. apply dom_detour_rfe_acq_sb_issuable. }
    rewrite ct_end. 
    rewrite AuxRel2.r_to_r_codom_rel_r with (r := rmw) at 2. rewrite !seqA.

    assert (dom_rel (⦗codom_rel rmw⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I) as D1.
    { unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA.
      apply dom_rel_iord_ext_parts.
      3: { erewrite init_issued; eauto. basic_solver. }
      2: { rewrite wf_rfiE, wf_sbE, no_sb_to_init; basic_solver. }
      transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
      unfold AR. hahn_frame.
      erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
      apply map_rel_mori; [done|].
      rewrite <- seq_eqvK with (dom := codom_rel rmw), !seqA.
      arewrite (codom_rel rmw ⊆₁ W) at 1 by (rewrite wf_rmwD; basic_solver).
      hahn_frame. 
      rewrite <- seq_eqvK with (dom := R ∩₁ Acq), !seqA.
      rewrite <- ct_unit. do 2 rewrite <- seqA. apply seq_mori.
      { rewrite <- ct_step. unfold ar, ar_int. unfold W_ex. basic_solver 10. }
      unfold ar, ar_int. unfold bob. basic_solver 10. }
    apply dom_rel_helper in D1. rewrite D1.
    rewrite <- !seqA. do 5 rewrite dom_seq.
    apply dom_detour_rfe_rmw_rfi_rmw_rt_I_in_I. 
  Qed.

  Lemma dom_detour_rmwrfi_rfe_acq_sb_issued :
    dom_rel ((detour ∪ rfe) ⨾ (rmw ⨾ rfi)＊ ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto.
    apply dom_detour_rmwrfi_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_rfe_acq_sb_issuable :
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    arewrite (rfe ⊆ detour ∪ rfe).
    apply dom_detour_rfe_acq_sb_issuable.
  Qed.

  Lemma dom_rfe_acq_sb_issued :
    dom_rel (rfe ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto.
    apply dom_rfe_acq_sb_issuable.
  Qed.

  Lemma W_ex_acq_sb_in_ar_int_W:
    ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ ar_int G ⨾ ⦗W⦘. 
  Proof using WF. 
    rewrite <- seq_eqvK. rewrite <- seq_eqvK with (dom := W) at 1.
    arewrite (W_ex_acq ⊆₁ W) at 1.
    { unfold W_ex. rewrite wf_rmwD; basic_solver. }
    hahn_frame. unfold ar_int. basic_solver 10.
  Qed. 

  Lemma dom_wex_sb_issuable :
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗issuable G sc T⦘) ⊆₁ I.
  Proof using WF TLSCOH.
    unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA. 
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; eauto. basic_solver. }
    2: { rewrite wf_sbE, no_sb_to_init; basic_solver. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    rewrite W_ex_acq_sb_in_ar_int_W. 
    rewrite <- ct_step. unfold ar. basic_solver 10. 
  Qed.

  Lemma dom_wex_sb_issued :
    dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto.
    apply dom_wex_sb_issuable.
  Qed.
  
  Lemma rf_rmw_issued_rfi_rmw_issued : 
    (rf ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘ ⨾ (rf ⨾ rmw)＊.
  Proof using WF TLSCOH IORDCOH.
    assert (transitive sb) as SBT by apply sb_trans.
    eapply rt_ind_left with (P:= fun r => r ⨾ ⦗I⦘).
    { by eauto with hahn. }
    { basic_solver 12. }
    intros k H; rewrite !seqA.
    sin_rewrite H.
    rewrite rfi_union_rfe at 1; relsf; unionL.
    rewrite <- seqA; seq_rewrite <- ct_begin; basic_solver 12.
    rewrite rtE at 2.
    relsf; unionR left.
    arewrite (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆
                  ⦗I⦘ ⨾ rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊ ⨾ ⦗I⦘).
    { apply dom_rel_helper.
      rewrite <- dom_detour_rfe_rmw_rfi_rmw_rt_I_in_I at 2. apply dom_rel_mori.
      hahn_frame_r. rewrite <- rt_seq_swap. basic_solver 10. }

    arewrite (rfe ⨾ rmw ⊆ rf ⨾ rmw).
    arewrite (rfi ⊆ rf).
    arewrite (rf ⨾ rmw ⨾ (rf ⨾ rmw)＊ ⊆ (rf ⨾ rmw)⁺).
    { rewrite <- seqA. apply ct_begin. }
    arewrite_id ⦗I⦘ at 2. rewrite seq_id_l.
    rewrite ct_rt. by rewrite inclusion_t_rt.
  Qed.
  
  Lemma wex_rfi_rfe_rmw_issued_is_issued :
    dom_rel ((⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗ I ⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    rewrite seq_union_l. rewrite dom_union.
    apply set_subset_union_l; split.
    { rewrite seqA. rewrite (rfi_in_sbloc' WF). rewrite (rmw_in_sb WF).
      arewrite (sb ∩ same_loc ⨾ sb ⊆ sb).
      { generalize (@sb_trans G). basic_solver. }
      arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
      { generalize issuedW. basic_solver. }
      arewrite (⦗W_ex_acq⦘ ⊆ ⦗W⦘ ⨾ ⦗W_ex_acq⦘).
      { rewrite <- seq_eqvK at 1.
        rewrite (W_ex_in_W WF) at 1. basic_solver. }

      rewrite issued_in_issuable at 1; eauto.
      unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA.
      apply dom_rel_iord_ext_parts.
      3: { erewrite init_issued; eauto. basic_solver. }
      2: { rewrite wf_sbE, no_sb_to_init; basic_solver. }
      transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
      unfold AR. hahn_frame. apply map_rel_mori; [done|]. 
      erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
      sin_rewrite W_ex_acq_sb_in_ar_int_W.
      unfold ar. rewrite <- ct_step. basic_solver 10. } 
     
    rewrite (rmw_in_ppo WF).
    apply dom_rfe_ppo_issued. 
  Qed. 

  Lemma wex_rf_rmw_issued_is_issued :
    dom_rel (⦗ W_ex_acq ⦘ ⨾ rf ⨾ rmw ⨾ ⦗ I ⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    arewrite (⦗W_ex_acq⦘ ⨾ rf ⊆ (⦗ W_ex_acq ⦘ ⨾ rfi ∪ rfe)).
    { rewrite rfi_union_rfe. basic_solver. }
    by apply wex_rfi_rfe_rmw_issued_is_issued.
  Qed.

  Lemma rf_rmw_issued :
    (rf ⨾ rmw)＊ ⨾ ⦗I⦘ ⊆ (rf ⨾ rmw ⨾ ⦗I⦘)＊.
  Proof using WF TLSCOH IORDCOH.
    intros x y HH. destruct_seq_r HH as II.
    apply clos_rt_rtn1 in HH.
    induction HH as [|y z TT].
    { apply rt_refl. }
    apply rt_end. right. exists y.
    split.
    2: apply seqA; basic_solver.
    apply IHHH.
    apply rfrmw_I_in_I. exists z. apply seqA. basic_solver 10. 
  Qed.

  Lemma fwbob_issuable_in_C:
    dom_rel (fwbob ⨾ ⦗issuable G sc T⦘) ⊆₁ C. 
  Proof using TLSCOH.
    unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA. 
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_covered; eauto. basic_solver. }
    2: { rewrite fwbob_in_sb, wf_sbE, no_sb_to_init; basic_solver. }
    transitivity (FWBOB G); [| unfold iord_simpl; basic_solver 10].
    unfold FWBOB. hahn_frame. basic_solver. 
  Qed. 

  Lemma fwbob_I_in_C:
    dom_rel (fwbob ⨾ ⦗I⦘) ⊆₁ C. 
  Proof using WF TLSCOH IORDCOH.
    rewrite issued_in_issuable at 1; eauto.
    apply fwbob_issuable_in_C. 
  Qed.

  Lemma dom_W_Rel_sb_loc_I_in_C :
    dom_rel (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗I⦘) ⊆₁ C.
  Proof using WF TLSCOH IORDCOH.
    arewrite (I ⊆₁ dom_cond fwbob (C)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed. 

  Lemma I_eq_EW_I : I ≡₁ E ∩₁ W ∩₁ I.
  Proof using WF TLSCOH.
    split; [|clear; basic_solver].
    generalize issuedW, issuedE.
    basic_solver.
  Qed.

  Lemma W_rel_sb_loc_W_CI :
    (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘) ⨾ ⦗C ∪₁ I⦘ ⊆
    ⦗C ∪₁ I⦘ ⨾ (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘).
  Proof using WF TLSCOH IORDCOH.
    (* case_refl _; [basic_solver|]. *)
    rewrite !seqA.
    arewrite (⦗W⦘ ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
    { rewrite <- !id_inter. apply eqv_rel_mori.
      rewrite set_inter_union_r. rewrite <- set_interK with (s := W), set_interA.
      erewrite w_covered_issued; eauto. basic_solver. }
    generalize dom_W_Rel_sb_loc_I_in_C. basic_solver 12.
  Qed. 

  Lemma sb_W_rel_CI :
    (sb ⨾ ⦗W ∩₁ Rel⦘) ⨾ ⦗C ∪₁ I⦘ ⊆ ⦗C ∪₁ I⦘ ⨾ (sb ⨾ ⦗W ∩₁ Rel⦘).
  Proof using RELCOV WF TLSCOH IORDCOH.
    generalize RELCOV, dom_sb_covered.
    basic_solver 12.
  Qed.

  Lemma W_Rel_sb_loc_I : dom_rel (⦗W ∩₁ Rel⦘ ⨾  (sb ∩ same_loc) ⨾ ⦗W ∩₁ I⦘) ⊆₁ I.
  Proof using WF TLSCOH IORDCOH.
    generalize dom_W_Rel_sb_loc_I_in_C, w_covered_issued. basic_solver 21.
  Qed.

  Lemma sb_loc_issued  :
    ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ 
               ⦗C⦘ ⨾ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘.
  Proof using WF TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_W_Rel_sb_loc_I_in_C).
    basic_solver.
  Qed.

  Lemma dom_F_sb_I_in_C :
    dom_rel (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ C.
  Proof using WF TLSCOH IORDCOH. 
    arewrite (I ⊆₁ dom_cond fwbob (C)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma F_sb_I_in_C  :
    ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb.
  Proof using WF TLSCOH IORDCOH. 
    seq_rewrite (dom_rel_helper dom_F_sb_I_in_C). basic_solver.
  Qed.

  Lemma dom_F_Rel_sb_I_in_C :  dom_rel (⦗F ∩₁ Rel⦘ ⨾  sb ⨾ ⦗I⦘) ⊆₁ C.
  Proof using RELCOV WF TLSCOH IORDCOH.
    etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 21.
  Qed.

  Lemma dom_F_Acq_sb_I_in_C :  dom_rel (⦗F ∩₁ Acq⦘ ⨾  sb ⨾ ⦗I⦘) ⊆₁ C.
  Proof using RELCOV WF TLSCOH IORDCOH. 
    etransitivity; [|apply dom_F_sb_I_in_C]; mode_solver 12. 
  Qed.
  
  Lemma dom_release_issued :
    dom_rel (release ⨾ ⦗ I ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
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
    release ⨾ ⦗ I ⦘ ⊆ ⦗C⦘ ⨾ release.
  Proof using WF RELCOV TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_release_issued).
    basic_solver.
  Qed.

  Lemma dom_release_rf_coverable :
    dom_rel (release ⨾ rf ⨾ ⦗ coverable G sc T ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
    generalize dom_release_issued.
    generalize dom_rf_coverable. 
    basic_solver 21.
  Qed.

  Lemma dom_release_rf_covered :
    dom_rel (release ⨾ rf ⨾ ⦗ C ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
    rewrite covered_in_coverable at 1; eauto. by apply dom_release_rf_coverable. 
  Qed. 

  Lemma release_rf_covered :
    release ⨾ rf ⨾ ⦗ C ⦘ ⊆ ⦗ C ⦘ ⨾ release ⨾ rf.
  Proof using WF RELCOV TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_release_rf_covered).
    basic_solver.
  Qed.

  Lemma dom_sb_W_rel_issued  :
    dom_rel (sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗I⦘) ⊆₁ C.
  Proof using WF TLSCOH IORDCOH.
    arewrite (I ⊆₁ dom_cond fwbob (C)).
    { apply dom_rel_to_cond, fwbob_I_in_C. }
    rewrite <- !seqA.
    rewrite dom_cond_elim1; [basic_solver 21|].
    unfold imm_bob.fwbob.
    basic_solver 12.
  Qed.

  Lemma sb_W_rel_issued  :
    sb ⨾ ⦗W ∩₁ Rel⦘ ⨾ ⦗I⦘ ⊆ ⦗C⦘ ⨾ sb ⨾ ⦗W ∩₁ Rel⦘.
  Proof using WF TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_sb_W_rel_issued).
    basic_solver.
  Qed.

  Lemma dom_sw_coverable :
    dom_rel (sw ⨾ ⦗ coverable G sc T ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
    unfold imm_s_hb.sw.
    generalize dom_sb_coverable, dom_release_rf_coverable.
    generalize covered_in_coverable.
    basic_solver 21.
  Qed.

  Local Ltac by_similar lem :=
    etransitivity; [| apply lem];
    (rewrite covered_in_coverable at 1 || rewrite issued_in_issuable at 1); 
    eauto; basic_solver. 

  Lemma dom_sw_covered :
    dom_rel (sw ⨾ ⦗ C ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
    by_similar dom_sw_coverable. 
  Qed. 

  Lemma sw_coverable : sw ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗C⦘ ⨾ sw.
  Proof using WF RELCOV TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper dom_sw_coverable).
    basic_solver.
  Qed.

  Lemma sw_covered : sw ⨾ ⦗ C ⦘ ⊆ ⦗C⦘ ⨾ sw.
  Proof using WF RELCOV TLSCOH IORDCOH.
    by_similar sw_coverable. 
  Qed. 

  Lemma hb_coverable :
    hb ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗C⦘ ⨾ hb.
  Proof using WF RELCOV TLSCOH IORDCOH.
    unfold imm_s_hb.hb.
    assert (A: (sb ∪ sw) ⨾ ⦗coverable G sc T⦘ ⊆ ⦗C⦘ ⨾ (sb ∪ sw)⁺).
    { relsf.
      rewrite sb_coverable, sw_coverable.
      rewrite <- ct_step; basic_solver. }
    unfold imm_s_hb.hb.
    eapply ct_ind_left with (P:= fun r => r ⨾ ⦗coverable G sc T⦘); eauto with hahn.
    intros k H; rewrite !seqA, H.
    rewrite covered_in_coverable at 1; eauto. 
    sin_rewrite A.
    arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw)＊) at 1.
    relsf.
  Qed.

  Lemma hb_covered :
    hb ⨾ ⦗ C ⦘ ⊆ ⦗C⦘ ⨾ hb.
  Proof using WF RELCOV TLSCOH IORDCOH. by_similar hb_coverable. Qed. 

  Lemma dom_hb_coverable :
    dom_rel (hb ⨾ ⦗ coverable G sc T ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH.
    rewrite hb_coverable; basic_solver 10.
  Qed.

  Lemma dom_hb_covered :
    dom_rel (hb ⨾ ⦗ C ⦘) ⊆₁ C.
  Proof using WF RELCOV TLSCOH IORDCOH. by_similar dom_hb_coverable. Qed. 

  Lemma dom_urr_coverable l:
    dom_rel (urr l ⨾ ⦗ coverable G sc T ⦘) ⊆₁ I.
  Proof using WF RELCOV TLSCOH IORDCOH WFSC.
    unfold CombRelations.urr.
    unfold CombRelations.urr.
    generalize dom_hb_coverable.
    generalize dom_sc_coverable.
    generalize dom_rf_coverable.
    generalize covered_in_coverable.
    generalize w_coverable_issued.
    basic_solver 21.
  Qed.

  Lemma dom_urr_covered l:
    dom_rel (urr l ⨾ ⦗ C ⦘) ⊆₁ I.
  Proof using WF RELCOV TLSCOH IORDCOH WFSC. by_similar dom_urr_coverable. Qed.

  Lemma urr_coverable l:
    urr l ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗I⦘ ⨾ urr l.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    rewrite (dom_rel_helper (@dom_urr_coverable l)).
    basic_solver.
  Qed.

  Lemma urr_covered l:
    urr l ⨾ ⦗ C ⦘ ⊆ ⦗I⦘ ⨾ urr l.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar urr_coverable. Qed. 

  Lemma dom_c_acq_coverable i l A:
    dom_rel (c_acq i l A ⨾ ⦗ coverable G sc T ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. 
    unfold CombRelations.c_acq.
    generalize (@dom_urr_coverable l).
    generalize covered_in_coverable.
    generalize dom_release_issued.
    generalize dom_rf_coverable.
    basic_solver 21.
  Qed.

  Lemma dom_c_acq_covered i l A:
    dom_rel (c_acq i l A ⨾ ⦗ C ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar dom_c_acq_coverable. Qed.

  Lemma c_acq_coverable i l A:
    c_acq i l A ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗I⦘ ⨾ c_acq i l A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    rewrite (dom_rel_helper (@dom_c_acq_coverable i l A)).
    basic_solver.
  Qed.

  Lemma c_acq_covered i l A:
    c_acq i l A ⨾ ⦗ C ⦘ ⊆ ⦗I⦘ ⨾ c_acq i l A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar c_acq_coverable. Qed. 

  Lemma dom_c_cur_coverable i l A:
    dom_rel (c_cur i l A ⨾ ⦗ coverable G sc T ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    unfold CombRelations.c_cur.
    generalize (@dom_urr_coverable l).
    basic_solver 21.
  Qed.

  Lemma dom_c_cur_covered i l A:
    dom_rel (c_cur i l A ⨾ ⦗ C ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar dom_c_cur_coverable. Qed.

  Lemma c_cur_coverable i l A:
    c_cur i l A ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗I⦘ ⨾ c_cur i l A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    seq_rewrite (dom_rel_helper (@dom_c_cur_coverable i l A)).
    basic_solver.
  Qed.

  Lemma c_cur_covered i l A:
    c_cur i l A ⨾ ⦗ C ⦘ ⊆ ⦗I⦘ ⨾ c_cur i l A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar c_cur_coverable. Qed. 

  Lemma dom_c_rel_coverable i l l' A:
    dom_rel (c_rel i l l' A ⨾ ⦗ coverable G sc T ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. 
    unfold CombRelations.c_rel.
    generalize (@dom_urr_coverable l).
    basic_solver 21.
  Qed.

  Lemma dom_c_rel_covered i l l' A:
    dom_rel (c_rel i l l' A ⨾ ⦗ C ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar dom_c_rel_coverable. Qed. 

  Lemma c_rel_coverable i l l' A:
    c_rel i l l' A ⨾ ⦗ coverable G sc T ⦘ ⊆ ⦗I⦘ ⨾ c_rel i l l' A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. 
    seq_rewrite (dom_rel_helper (@dom_c_rel_coverable i l l' A)).
    basic_solver.
  Qed.

  Lemma c_rel_covered i l l' A:
    c_rel i l l' A ⨾ ⦗ C ⦘ ⊆ ⦗I⦘ ⨾ c_rel i l l' A.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar c_rel_coverable. Qed. 

  Lemma t_acq_coverable l thread:
    t_acq thread l (coverable G sc T) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    unfold CombRelations.t_acq.
    rewrite (dom_r (wf_c_acqD G sc thread l (coverable G sc T))).
    arewrite (⦗(Tid_ thread ∪₁ Init) ∩₁ coverable G sc  T⦘ ⊆ ⦗coverable G sc T⦘) by basic_solver.
    rewrite c_acq_coverable.
    basic_solver.
  Qed.

  Lemma t_acq_covered l thread:
    t_acq thread l (C) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar t_acq_coverable. Qed.

  Lemma t_cur_coverable l thread:
    t_cur thread l (coverable G sc T) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. 
    etransitivity; [by apply t_cur_in_t_acq|].
      by apply t_acq_coverable.
  Qed.

  Lemma t_cur_covered l thread:
    t_cur thread l (C) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar t_cur_coverable. Qed. 

  Lemma t_rel_coverable l l' thread:
    t_rel thread l l' (coverable G sc T) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    etransitivity; [by apply t_rel_in_t_cur|].
      by apply t_cur_coverable. 
  Qed.

  Lemma t_rel_covered l l' thread:
    t_rel thread l l' (C) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH. by_similar t_rel_coverable. Qed. 

  Lemma S_tm_coverable l :
    S_tm l (coverable G sc T) ⊆₁ I.
  Proof using WF RELCOV TLSCOH IORDCOH. 
    unfold CombRelations.S_tm, CombRelations.S_tmr.
    generalize dom_hb_coverable.
    generalize w_coverable_issued.
    generalize dom_release_issued.
    generalize dom_rf_coverable.
    generalize covered_in_coverable.
    basic_solver 21.
  Qed.

  Lemma S_tm_covered l :
    S_tm l (C) ⊆₁ I.
  Proof using WF RELCOV TLSCOH IORDCOH. by_similar S_tm_coverable. Qed. 

  Lemma msg_rel_issued l:
    dom_rel (msg_rel l ⨾ ⦗ I ⦘) ⊆₁ I.
  Proof using WF WFSC RELCOV TLSCOH IORDCOH.
    unfold CombRelations.msg_rel.
    generalize dom_release_issued.
    generalize (@dom_urr_covered l).
    basic_solver 21.
  Qed.

Section HbProps.

Lemma rfe_ar_int_ct_issuable_in_I:
  dom_rel (⦗W⦘ ⨾ (rfe ∪ ar_int G)⁺ ⨾ ⦗issuable G sc T⦘) ⊆₁ I. 
Proof using WF TLSCOH IORDCOH.
  rewrite unionC. rewrite path_ut_first.
  repeat case_union _ _ . rewrite dom_union. apply set_subset_union_l. split.
  { apply ar_int_ct_issuable_in_I. }
  
  rewrite !seqA.
  assert (dom_rel (rfe ⨾ (ar_int G ∪ rfe)＊ ⨾ ⦗issuable G sc T⦘) ⊆₁ (I)) as D.
  { unfold issuable. rewrite id_inter with (s := _ ∩₁ _). rewrite <- !seqA. 
    apply dom_rel_iord_ext_parts.
    3: { erewrite init_issued; eauto. basic_solver. }
    2: { rewrite ar_int_in_sb, rfe_in_rf, sb_E_ENI, rf_E_ENI, unionK, <- ct_begin, ct_of_trans; auto.
         { basic_solver. }
         apply E_ENI_trans. }
    transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
    unfold AR. hahn_frame. apply map_rel_mori; [done| ].
    erewrite eqv_rel_mori with (x := _ ∩₁ W); [| intro; apply proj2].
    rewrite (dom_l (wf_rfeD WF)) at 1. hahn_frame.
    arewrite (rfe ⊆ ar_int G ∪ rfe) at 1. rewrite <- ct_begin.
    apply clos_trans_mori. unfold ar. basic_solver. }
  apply dom_rel_helper in D. rewrite D.
  rewrite <- !seqA. do 3 rewrite dom_seq. rewrite !seqA. 
  rewrite rtE. repeat case_union _ _. rewrite dom_union.
  apply set_subset_union_l. split; [basic_solver| ]. 
  rewrite issued_in_issuable at 1; eauto. apply ar_int_ct_issuable_in_I. 
Qed.

Lemma sw_in_Csw_sb :
  sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ sw ∪ sb.
Proof using WF RELCOV TLSCOH IORDCOH.
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
  rewrite issued_in_issuable at 1; eauto. 
  apply rfe_ar_int_ct_issuable_in_I. 
Qed.

Lemma hb_in_Chb_sb :
  hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof using WF RELCOV TLSCOH IORDCOH. 
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
  

End TlsProperties.
