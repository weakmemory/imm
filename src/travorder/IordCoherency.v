Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import AuxDef.
Require Import SetSize.
Require Import AuxRel2.
Require Import travorder.TraversalOrder.
Require Import travorder.TLSCoherency. 
Require Import AuxRel2.


Definition iord_coherent G sc tc :=
  dom_rel (iord G sc ⨾ ⦗tc⦘) ⊆₁ tc.

Definition iord_simpl G sc : relation trav_label :=
  SB G sc ∪ RF G ∪ FWBOB G ∪ AR G sc ∪ IPROP G ∪ PROP G sc.

Definition iord_simpl_coherent G sc tc :=
  dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc.

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
  
  Let E_ENI := E × (E \₁ is_init).

  Lemma sb_E_ENI: sb ⊆ E_ENI. 
  Proof using. rewrite wf_sbE, no_sb_to_init. basic_solver. Qed. 

  Lemma co_E_ENI: co ⊆ E_ENI. 
  Proof using WF SCPL. rewrite wf_coE, no_co_to_init; auto. basic_solver. Qed.

  Lemma rf_E_ENI : rf ⊆ E_ENI. 
  Proof using WF. rewrite wf_rfE, no_rf_to_init; auto. basic_solver. Qed. 

  Lemma fr_E_ENI: fr ⊆ E_ENI. 
  Proof using WF SCPL. rewrite wf_frE, no_fr_to_init; auto. basic_solver. Qed.

  (* TODO: replace the original lemma with it*)
  Lemma no_ar_to_init': ar ⨾ ⦗is_init⦘ ≡ ∅₂.
  Proof using WF WFSC.
    split; [|basic_solver].
    unfold ar.
    rewrite (ar_int_in_sb WF). rewrite no_sb_to_init.
    rewrite wf_scD with (sc:=sc); eauto.  
    rewrite (wf_rfeD WF).
    rewrite seq_union_l. unionL; [|basic_solver].
    rewrite (init_w WF). type_solver 10.
  Qed.

  Lemma no_ar_to_init_alt:
    ar ≡ ar ⨾ ⦗set_compl is_init⦘. 
  Proof using WF WFSC.
    forward eapply no_ar_to_init'; eauto. basic_solver 10.
    Unshelve. all: eauto.
  Qed. 

  Lemma ar_E_ENI: ar ⊆ E_ENI. 
  Proof using WF WFSC.
    rewrite wf_arE, no_ar_to_init_alt; auto. basic_solver.
  Qed.

  Lemma sc_E_ENI: sc ⊆ E_ENI. 
  Proof using WF WFSC.
    rewrite wf_scE, (@no_sc_to_init _ WF _ WFSC); eauto. basic_solver.
  Qed.

  Lemma E_ENI_trans: transitive E_ENI.
  Proof using. unfold E_ENI. basic_solver. Qed.

  Lemma iord_simpl_E_ENI:
    iord_simpl G sc ⊆ event ↓ E_ENI^?.
  Proof using WF WFSC SCPL.
    unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
    rewrite ppo_in_sb, fwbob_in_sb; auto. rewrite inclusion_inter_l1 with (r := sb).
    rewrite ?sb_E_ENI, ?rf_E_ENI, ?co_E_ENI, ?fr_E_ENI, ?ar_E_ENI, ?sc_E_ENI; auto.
    rewrite <- !seqA. 
    repeat (rewrite ?(@rt_of_trans _ E_ENI), ?(@rewrite_trans _ E_ENI),
             ?unionK, ?(@rewrite_trans _ E_ENI),
             ?(@rewrite_trans_seq_cr_cr _ E_ENI), ?(@ct_of_trans _ E_ENI)
           ); auto using E_ENI_trans.
    repeat rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r. basic_solver 10.
  Qed.

  Lemma iord_simpl_tc_doma:
    doma (iord_simpl G sc ⨾ ⦗tc⦘) (event ↓₁ E).
  Proof using WF WFSC SCPL TCOH.
    rewrite iord_simpl_E_ENI; auto. rewrite crE, map_rel_union, seq_union_l.
    apply union_doma.
    { rewrite tlsc_E; eauto. unfolder. ins. desc. congruence. }
    unfold E_ENI. basic_solver.
  Qed.

  (* TODO: move to lib*)
  Lemma set_compl_set_mapC {A B: Type} (d: B -> Prop) (f: A -> B):
    set_compl (f ↓₁ d) ≡₁  (f ↓₁ set_compl d).
  Proof using. basic_solver. Qed. 

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

End IordCoherency.

Lemma iord_coh_implies_iord_simpl_coh G sc tc
      (tCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      (CONS: imm_consistent G sc) (WF: Wf G):      
  dom_rel (iord_simpl G sc ⨾ ⦗tc⦘) ⊆₁ tc. 
Proof using. 
  apply iord_coh_implies_iord_simpl_coh'; auto.
  { by apply CONS. }
  apply imm_s_hb.coherence_sc_per_loc, CONS. 
Qed.
