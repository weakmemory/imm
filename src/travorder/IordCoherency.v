From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import AuxEE.
Require Import travorder.TraversalOrder.
Require Import travorder.TLSCoherency. 
Require Import CombRelations.


Definition iord_coherent G sc tc :=
  dom_rel (iord G sc ⨾ ⦗tc⦘) ⊆₁ tc.

Definition iord_simpl_coherent G sc tc :=
  dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc.

Global Add Parametric Morphism : iord_coherent with signature
       eq ==> Basics.flip inclusion ==> set_equiv ==> Basics.impl as iord_coherent_mori.
Proof using.
  intros G sc sc' EQ s s' EQS.
  unfold iord_coherent. red. 
  intros HH.
  by rewrite EQ, <- EQS. 
Qed.

Global Add Parametric Morphism : iord_coherent with signature
       eq ==> same_relation ==> set_equiv ==> iff as iord_coherent_more.
Proof using.
  intros G sc sc' EQ s s' EQS.
  unfold iord_coherent.
  split; intros HH.
  { now rewrite <- EQS, <- EQ. }
  now rewrite EQS, EQ.
Qed.

Section IordCoherency.
  Variables (tc: trav_label -> Prop) (G: execution) (sc: relation actid). 
  Hypothesis (TCOH: tls_coherent G tc).
  Hypotheses (WF: Wf G)
             (* (CONS: imm_consistent G sc). *)
             (WFSC: wf_sc G sc)
             (SCPL: sc_per_loc G)
  .

  Implicit Types
           (ICOH: iord_coherent G sc tc)
           (ICOHs: iord_simpl_coherent G sc tc).
  

  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'ar'" := (ar G sc).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).

  Notation "'lab'" := (lab G).
  Notation "'loc'" := (loc lab).
  Notation "'val'" := (val lab).
  Notation "'mod'" := (Events.mod lab).
  Notation "'same_loc'" := (same_loc lab).
  
  Notation "'E'" := (acts_set G).
  Notation "'R'" := (fun x => is_true (is_r lab x)).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'F'" := (fun x => is_true (is_f lab x)).
  Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
  Notation "'RW'" := (R ∪₁ W).
  Notation "'FR'" := (F ∪₁ R).
  Notation "'FW'" := (F ∪₁ W).
  Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
  Notation "'W_ex'" := (W_ex G).
  Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).

  Let E_ENI := E × (E \₁ is_init).

  Lemma init_tls_iord_coherent :
    iord_coherent G sc (init_tls G). 
  Proof using.
    red. rewrite iord_alt, restr_relE.
    rewrite init_tls_EI at 1. basic_solver 10. 
  Qed.

  Lemma tlsc_w_covered_issued ICOH:
    (tc ∩₁ action ↓₁ eq ta_cover) ∩₁ (event ↓₁ W) ⊆₁
    event ↓₁ (event ↑₁ (tc ∩₁ action ↓₁ eq ta_issue)).
  (* (fun ae => mkTL ta_issue (event ae)) ↓₁ (tlsC ∩₁ (event ↓₁ W)) ⊆₁ tlsI. *)
  Proof using TCOH.
    destruct TCOH. 
    unfolder. ins. desc. destruct x as [a e]. ins. subst.
    
    exists (mkTL ta_issue e). splits; eauto.
    destruct (tls_coh_exec _ H) as [Il | EXl].
    { apply tls_coh_init. split; [basic_solver| ]. 
      apply init_tls_EI in Il. auto. }
    red in ICOH. apply ICOH.     
    red. eexists. apply seq_eqv_r. split; eauto.
    red. apply exec_tls_ENI in EXl. red. splits; try by vauto.
    do 4 left. right. red. basic_solver 10. 
  Qed.
  
  Lemma iord_simpl_E_ENI:
    iord_simpl G sc ⊆ event ↓ E_ENI^?.
  Proof using WF WFSC SCPL.
    unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
    rewrite ppo_in_sb, fwbob_in_sb; auto.
    rewrite inclusion_inter_l1 with (r := sb).
    rewrite inclusion_inter_l1. 
    rewrite !inclusion_eqv_rel_true with (dom:=action ↓₁ eq ta_cover).
    rewrite !inclusion_eqv_rel_true with (dom:=action ↓₁ eq ta_issue).
    rewrite !inclusion_eqv_rel_true with (dom:=action ↓₁ is_ta_propagate_to_G G).
    rewrite !seq_id_l, !seq_id_r.
    rewrite ?sb_E_ENI, ?rf_E_ENI, ?co_E_ENI, ?fr_E_ENI, ?ar_E_ENI, 
      ?furr_E_ENI_cr, ?(sc_E_ENI WF WFSC); auto.
    fold E_ENI.
    repeat (rewrite ?(@rt_of_trans _ E_ENI), ?(@rewrite_trans _ E_ENI),
             ?unionK, ?(@rewrite_trans _ E_ENI),
             ?(@rewrite_trans_seq_cr_cr _ E_ENI), ?(@ct_of_trans _ E_ENI)
           ).
    all: try now apply E_ENI_trans.
    repeat rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
    generalize (E_ENI_trans G).
    unfold E_ENI. basic_solver 10.
  Qed.

  Lemma iord_simpl_tc_doma_impl S (S_E: S ⊆₁ event ↓₁ acts_set G) :
    doma (iord_simpl G sc ⨾ ⦗S⦘) (event ↓₁ acts_set G).
  Proof using WF WFSC.
    rewrite iord_simpl_E_E; auto. rewrite crE, map_rel_union, seq_union_l.
    apply union_doma.
    2: { basic_solver. }
    rewrite S_E. unfolder. ins. desc. congruence. 
  Qed.

  Lemma iord_simpl_tc_doma:
    doma (iord_simpl G sc ⨾ ⦗tc⦘) (event ↓₁ E).
  Proof using WF WFSC SCPL TCOH.
    apply iord_simpl_tc_doma_impl.
    rewrite tlsc_E; eauto. 
  Qed.

  Lemma iord_coh_implies_iord_simpl_coh' ICOH:
    dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc. 
  Proof using WF TCOH WFSC SCPL.
    rewrite set_split_complete with (s' := dom_rel _) (s := event ↓₁ is_init).
    forward eapply iord_simpl_tc_doma as IS_DOM%doma_rewrite; eauto.

    apply set_subset_union_l. split.
    { rewrite IS_DOM.
      destruct TCOH. rewrite <- tls_coh_init at 2. unfold init_tls.
      rewrite set_pair_alt, set_map_inter.
      rewrite <- set_interA. apply set_subset_inter; [| reflexivity].  
      rewrite dom_eqv1, set_interC. apply set_subset_inter; [| reflexivity].
      unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
      basic_solver 10. }
    
    rewrite set_interC, <- dom_eqv1.
    red in ICOH. rewrite <- ICOH at 2. apply dom_rel_mori.
    unfold iord. fold iord_simpl.
    rewrite restr_relE. rewrite !seqA, seq_eqvC. 
    rewrite set_minusE, set_map_inter, id_inter.
    rewrite !seqA, seq_eqvC.
    rewrite <- seqA with (r3 := ⦗_⦘ ⨾ ⦗_⦘). rewrite <- seqA with (r2 := _ ⨾ ⦗tc⦘).
    rewrite set_compl_set_mapC.
    etransitivity.
    2: { apply seq_mori; [reflexivity| ].
         rewrite <- id_inter. apply domb_rewrite.
         rewrite iord_simpl_E_ENI; auto.
         rewrite crE, map_rel_union. repeat case_union _ _. apply union_domb.
         { rewrite (@tlsc_E G tc) at 1; eauto.
           unfolder. ins. desc. split; congruence. }
         unfold E_ENI. basic_solver. }
    apply doma_rewrite. rewrite IS_DOM. basic_solver.
  Qed. 

  Lemma iord_simpl_coh_implies_iord_coh ICOHs:
    iord_coherent G sc tc. 
  Proof using. 
    red. erewrite dom_rel_mori; [by apply ICOHs| ].
    unfold iord, iord_simpl. basic_solver 10.
  Qed.

  Lemma iord_coh_clos_refl ICOH:
    dom_rel ((iord G sc)^? ⨾ ⦗tc⦘) ⊆₁ tc. 
  Proof using.
    rewrite crE, seq_union_l, seq_id_l, dom_union.
    red in ICOH. rewrite ICOH. basic_solver.
  Qed.

  Lemma iord_simpl_coh_clos_refl ICOHs:
    dom_rel ((iord_simpl G sc)^? ⨾ ⦗tc⦘) ⊆₁ tc. 
  Proof using.
    rewrite crE, seq_union_l, seq_id_l, dom_union.
    red in ICOHs. rewrite ICOHs. basic_solver.
  Qed.

Lemma dom_rel_iord_ext_parts (a1 a2: trav_action) (r: relation actid)
      (R_IORD: ⦗action ↓₁ eq a1⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a2⦘ ⊆ iord_simpl G sc)
      (R_E_ENI: r ⊆ E × (E \₁ is_init))
      (INITa1: is_init ∩₁ E ⊆₁ event ↑₁ (tc ∩₁ action ↓₁ eq a1))
  :
  dom_rel (r ⨾ ⦗event ↑₁ (dom_cond (iord G sc) tc ∩₁ action ↓₁ eq a2)⦘)
          ⊆₁ event ↑₁ (tc ∩₁ action ↓₁ eq a1).
Proof using.
  rewrite set_split_complete with (s' := dom_rel _) (s := is_init).
  apply dom_helper_3 in R_E_ENI. 
  apply set_subset_union_l. split.
  { rewrite <- INITa1. rewrite !dom_seq. rewrite R_E_ENI. basic_solver. }
  rewrite set_interC, <- dom_eqv1, <- seqA. 
  eapply dom_rel_collect_event with (b := a1).
  apply set_subset_inter_r. split; [| basic_solver].
  rewrite set_interC, id_inter.  
  arewrite (⦗action ↓₁ eq a1⦘ ⨾ event ↓ (⦗set_compl is_init⦘ ⨾ r) ⨾ ⦗action ↓₁ eq a2⦘ ⊆ iord G sc). 
  { rewrite iord_alt. rewrite R_E_ENI. unfolder. ins. desc.
    splits; eauto; try congruence.
    apply R_IORD. basic_solver. }
  rewrite dom_cond_elim. basic_solver. 
Qed. 
        
Lemma iord_coherent_extend ICOH lbl      
      (ADD: dom_cond (iord G sc) tc lbl):
  iord_coherent G sc (tc ∪₁ eq lbl). 
Proof using. 
  red. rewrite id_union, seq_union_r, dom_union.
  red in ICOH, ADD. rewrite ICOH, ADD. basic_solver. 
Qed.

Lemma iord_coherent_element_prefix ICOH (lbl: trav_label)
      (Tlbl: tc lbl)
      (IMMCON: imm_consistent G sc):
  dom_rel (iord G sc ⨾ ⦗eq lbl⦘) ⊆₁ tc \₁ eq lbl.
Proof using WF.
  clear WFSC. 
  rewrite set_minusE. apply set_subset_inter_r. split.
  { etransitivity; [| apply ICOH]. basic_solver. }
  intros x [y [REL ->]%seq_eqv_r]. intros ->.  
  edestruct iord_irreflexive; eauto; apply IMMCON.
Qed.

Lemma dom_rel_iord_ext_parts_tl (r: relation trav_label)
      (R_IORD: r ⊆ iord_simpl G sc)
      (R_E_ENI: r ⊆ (event ↓₁ E) × (event ↓₁ (E \₁ is_init)))
      (INIT: event ↓₁ is_init ∩₁ dom_rel r ⊆₁ tc)
      (ICOH': iord_coherent G sc tc):
  dom_rel (r ⨾ ⦗tc⦘) ⊆₁ tc.
Proof using.
  rewrite AuxRel2.set_split_complete with (s' := dom_rel _) (s := event ↓₁ is_init).
  apply dom_helper_3 in R_E_ENI. 
  apply set_subset_union_l. split.
  { rewrite set_interC, <- dom_eqv1.
    generalize INIT. basic_solver. }
  rewrite set_interC, <- dom_eqv1, <- seqA.
  rewrite R_E_ENI.
  red in ICOH'. rewrite <- ICOH' at 2. apply dom_rel_mori.
  hahn_frame_r. rewrite iord_alt, R_IORD. basic_solver.
Qed. 

End IordCoherency.

Lemma iord_coherent_crt G sc T
  (ICOH: iord_coherent G sc T):
  dom_rel ((iord G sc)^* ⨾ ⦗T⦘) ⊆₁ T.
Proof using.
  intros x [y HH]. apply seq_eqv_r in HH.
  destruct HH as [II TY].
  apply clos_rt_rt1n in II.
  induction II; auto.
  apply IHII in TY.
  eapply iord_coh_clos_refl; eauto.
  clear -H TY. basic_solver 10.
Qed.

Lemma iord_coh_implies_iord_simpl_coh G sc tc
      (tCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      (CONS: imm_consistent G sc) (WF: Wf G):      
  dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc. 
Proof using. 
  apply iord_coh_implies_iord_simpl_coh'; auto.
  { by apply CONS. }
  apply imm_s_hb.coherence_sc_per_loc, CONS. 
Qed.

Lemma iord_coherent_equiv_wo_reserved G sc T1 T2
      (EQ': T1 \₁ action ↓₁ eq ta_reserve ≡₁ T2 \₁ action ↓₁ eq ta_reserve)
      (ICOH: iord_coherent G sc T1):
  iord_coherent G sc T2. 
Proof using. 
  red. red in ICOH.
  rewrite iord_no_reserve, restr_relE in *.
  rewrite !seqA, seq_eqvC, <- id_inter in *.
  transitivity (T2 \₁ action ↓₁ eq ta_reserve); [| basic_solver].
  rewrite <- EQ'. rewrite !set_minusE in EQ'. rewrite EQ' in ICOH.
  rewrite set_minusE. apply set_subset_inter_r. split; [| basic_solver].
  rewrite ICOH. basic_solver. 
Qed.
