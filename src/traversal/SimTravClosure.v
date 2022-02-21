Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import TraversalConfig.
Require Import Traversal.
Require Import TraversalConfigAlt.
Require Import AuxDef.
Require Import SetSize.
Require Import FairExecution.
Import ListNotations.
Require Import TraversalOrder.
Require Import PropExtensionality.
Require Import CountabilityHelpers.
Require Import IordTraversal.
Require Import SimTraversal.
Require Import SimTraversalProperties.
Require Import ImmFair.


Section SimTravClosure.
  Variable (G: execution) (sc: relation actid). 
  Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).

  Definition Cclos (tc: trav_config) :=
    issued tc ∩₁ (is_rel (lab G)) ∪₁ codom_rel (⦗covered tc⦘ ⨾ (rmw G)).
  Definition Iclos (tc: trav_config) :=
    codom_rel (⦗covered tc⦘ ⨾ (rmw G)).

  Definition sim_trav_closure (tc: trav_config) :=
    mkTC (covered tc ∪₁ (Cclos tc \₁ covered tc))
         (issued tc ∪₁ (Iclos tc \₁ issued tc)). 

  Lemma codom_I_rmw_empty WF WFSC
        (tc: trav_config) (COH: tc_coherent G sc tc):
    codom_rel (⦗(issued tc) ∩₁ is_rel (lab G)⦘ ⨾ (rmw G)) ≡₁ ∅.
  Proof using.
    rewrite wf_rmwD; auto. repeat seq_rewrite <- id_inter.
    forward eapply tc_I_in_W as IW; eauto.
    { apply tc_coherent_implies_tc_coherent_alt; eauto. }
    simpl in IW. split; [| basic_solver]. rewrite IW. type_solver.
  Qed. 

  (* TODO: move to hahn *)
  Lemma set_union_strict {A: Type}
        (s1 s2: A -> Prop):
    s1 ∪₁ s2 ≡₁ s1 ∪₁ s2 \₁ s1.
  Proof using.
    split; [| basic_solver].
    intros x Sx. destruct (classic (s1 x)); [basic_solver| ].
    destruct Sx; [done| ]. basic_solver. 
  Qed.

  Lemma sb_invrmw_sbclos WF:
    sb G ⨾ (rmw G)⁻¹ ⊆ (sb G)^?.
  Proof using.
    red. ins. destruct (classic (x = y)); [by left| ].
    right. red in H. destruct H as [w [SB RMW]]. red in RMW.
    forward eapply (wf_rmwi WF _ _ RMW) as [SByw IMMyw]. 
    eapply sb_semi_total_r in SByw; eauto.
    2: { eapply read_or_fence_is_not_init; eauto. left.
         apply wf_rmwD, seq_eqv_lr in RMW; auto. by desc. }
    des; auto. edestruct IMMyw; eauto. 
  Qed. 

  Lemma stc_coherent WF WFSC CONS
        (tc: trav_config)
        (COH: tc_coherent G sc tc):
    tc_coherent G sc (sim_trav_closure tc).
  Proof using.
    apply tc_coherent_alt_implies_tc_coherent.
    pose proof COH as COH'. apply tc_coherent_implies_tc_coherent_alt in COH'; auto.
    inversion COH'.
    unfold sim_trav_closure. 
    forward eapply codom_I_rmw_empty as CIR; eauto.
    destruct tc as [C I] eqn:TC. simpl in *. 
    assert ((sb G)^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ (sb G)^? ⨾ ⦗C⦘) as COV_SB'.
    { apply dom_rel_helper_in. 
      rewrite crE, seq_union_l, dom_union. 
      rewrite tc_sb_C. basic_solver. }
    constructor; simpl. 
    { etransitivity; [apply tc_init| ]. basic_solver. }
    { unfold Cclos. simpl. rewrite wf_rmwE; auto. basic_solver. }
    { rewrite <- set_union_strict.  
      rewrite id_union, seq_union_r, dom_union.
      apply set_subset_union_l. split; [generalize tc_sb_C; basic_solver 10 | ].
      unfold Cclos. simpl. rewrite id_union, seq_union_r, dom_union.
      apply set_subset_union_l. split.
      { apply set_subset_union_r. left.
        replace C with (covered tc); [| by rewrite TC].
        etransitivity.
        2: { eapply dom_sb_W_rel_issued; eauto. rewrite TC. apply COH. }
        rewrite TC. simpl. rewrite <- id_inter. apply dom_rel_mori. basic_solver. }
      rewrite dom_rel_eqv_codom_rel. rewrite transp_seq, transp_eqv_rel. 
      rewrite <- seqA, sb_invrmw_sbclos; auto.
      rewrite COV_SB'. basic_solver. }
    { rewrite <- !set_union_strict.
      rewrite set_inter_union_l. rewrite tc_W_C_in_I.
      unfold Cclos, Iclos. simpl.
      basic_solver 10. }
    { rewrite <- !set_union_strict.
      rewrite id_union, seq_union_r, dom_union, tc_rf_C.
      unfold Cclos, Iclos. simpl.
      rewrite tc_I_in_W at 2. 
      rewrite wf_rmwD; auto.
      do 3 rewrite codom_seq at 1. rewrite codom_eqv.
      rewrite wf_rfD; auto. type_solver. }
    { rewrite <- !set_union_strict.
      rewrite id_union, seq_union_r, dom_union, tc_sc_C.
      unfold Cclos. simpl.
      rewrite !id_union.
      rewrite seq_union_r, dom_union. repeat (apply set_subset_union_l; split).
      { basic_solver. }
      { erewrite (wf_scD WFSC). rewrite tc_I_in_W at 1.
        type_solver. }
      erewrite (wf_scD WFSC). rewrite wf_rmwD at 1; auto.
      do 3 rewrite codom_seq at 1. rewrite codom_eqv. type_solver. }
    { unfold Iclos. simpl. rewrite wf_rmwE; auto. basic_solver. }
    { unfold Iclos. simpl. rewrite wf_rmwD; auto. basic_solver. }
    { rewrite <- !set_union_strict.
      rewrite !id_union, seq_union_r, dom_union, tc_fwbob_I.
      unfold Iclos, Cclos. simpl.
      rewrite fwbob_in_sb.
      rewrite dom_rel_eqv_codom_rel. rewrite transp_seq, transp_eqv_rel.
      rewrite <- seqA. rewrite sb_invrmw_sbclos; auto.
      rewrite COV_SB'. basic_solver. }
    { rewrite <- !set_union_strict.
      rewrite id_union, !seq_union_r, dom_union, tc_I_ar_rf_ppo_loc_I.      
      
      unfold Iclos. simpl.
      rewrite ct_end, seqA. unfold ar at 2. 
      rewrite !seq_union_l.
      arewrite (sc ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw G)⦘ ⊆ ∅₂).
      { rewrite (wf_scD WFSC), (wf_rmwD WF). type_solver. }
      arewrite (rfe G ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw G)⦘ ⊆ ∅₂).
      { rewrite wf_rfeD, wf_rmwD; auto. type_solver. }
      rewrite !union_false_l.
      
      rewrite ar_int_in_sb; auto.
      arewrite (ppo G ∩ same_loc (lab G) ⊆ sb G) at 2 by (generalize ppo_in_sb; basic_solver).
      rewrite !seq_union_r. rewrite dom_union.
      repeat (apply set_subset_union_l; split).
      { basic_solver. }
      { rewrite <- !seqA. rewrite dom_rel_eqv_codom_rel.
        rewrite transp_seq, transp_eqv_rel.
        rewrite !seqA. rewrite <- seqA with (r3 := ⦗C⦘).
        seq_rewrite sb_invrmw_sbclos; auto. 
        rewrite COV_SB'. do 2 rewrite <- seqA. rewrite dom_seq.
        forward eapply ar_rf_ppo_loc_rt_CI_in_I as IN; eauto. simpl in IN.
        generalize IN. basic_solver 10. }
      (* TODO: refactor by unifying with case above? *)
      rewrite <- !seqA. rewrite dom_rel_eqv_codom_rel.
      rewrite transp_seq, transp_eqv_rel. rewrite seqA.
      rewrite <- seqA with (r1 := sb G). seq_rewrite sb_invrmw_sbclos; auto.
      rewrite COV_SB'. do 2 rewrite <- seqA. do 2 rewrite dom_seq.
      rewrite seqA. rewrite <- dom_rel_eqv_dom_rel. rewrite tc_rf_C.
      generalize tc_I_ar_rf_ppo_loc_I. basic_solver 10.  
    }
  Qed. 

 Lemma stc_domE WF COMP WFSC CONS MF
        tc (DOMC: covered tc ⊆₁ acts_set G) (DOMI: issued tc ⊆₁ acts_set G)
        (COH: tc_coherent G sc tc):
   covered (sim_trav_closure tc) ⊆₁ acts_set G /\
   issued (sim_trav_closure tc) ⊆₁ acts_set G.
  Proof using.
    unfold sim_trav_closure. 
    destruct tc. simpl in *.
    unfold Cclos, Iclos. simpl.
    rewrite wf_rmwE; auto. basic_solver.
  Qed.  

  Global Add Parametric Morphism: sim_trav_closure with signature
      same_trav_config ==> same_trav_config as stc_more. 
  Proof using.
    ins. destruct x as [C1 I1], y as [C2 I2]. destruct H. simpl in *.
    unfold sim_trav_closure, Cclos, Iclos. simpl.
    red. split; simpl; rewrite !H, !H0; reflexivity. 
  Qed. 
    
End SimTravClosure.


Section STCTraversal. 
  Variable (G: execution) (sc: relation actid). 
  Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).
    
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

  Lemma itrav_step_mon_ext e
        (C1 I1 C2 I2 C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C1 I1) (mkTC C2 I2)):
          (itrav_step G sc e)^?
                             (mkTC (C1 ∪₁ C') (I1 ∪₁ I'))
                             (mkTC (C2 ∪₁ C') (I2 ∪₁ I')).
  Proof using.
    red in STEP. desf; simpl in *. 

    { destruct (classic (C' e)).
      { left. f_equal; apply set_extensionality;
                (rewrite COVEQ || rewrite ISSEQ); basic_solver. }
      right. red. left. splits; simpl. 
      { intros [? | ?]; done. }
      { eapply traversal_mon; [.. | apply COV]; simpl; basic_solver. }
      all: (rewrite COVEQ || rewrite ISSEQ); basic_solver. }

    destruct (classic (I' e)).
    { left. f_equal; apply set_extensionality;
              (rewrite COVEQ || rewrite ISSEQ); basic_solver. }
    right. red. right. splits; simpl. 
    { intros [? | ?]; done. }
    { eapply traversal_mon; [| | apply ISS]; simpl; basic_solver. }
    all: (rewrite COVEQ || rewrite ISSEQ); basic_solver.
  Qed.

  Add Parametric Morphism thread: (isim_trav_step G sc thread) with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_more.
  Proof using. ins. apply same_tc_extensionality in H, H0. by subst. Qed.



  Lemma functional_codom {A: Type} (r: relation A) (a: A)
        (FUN: functional r)
        (DOMa: dom_rel r a):
    exists a', codom_rel (⦗eq a⦘ ⨾ r) ≡₁ eq a'.
  Proof using.
    destruct DOMa as [a' Raa']. exists a'. split; [| basic_solver].  
    intros x [a_ Ra_x%seq_eqv_l]. desc. subst.
    eapply FUN; eauto.
  Qed.

  Lemma ext_r_helper WF tc r
        (Rr: is_r lab r) (COH: tc_coherent G sc tc):
    set_disjoint (eq r)
                 ((issued tc ∩₁ (is_rel lab) ∪₁
                          codom_rel (⦗covered tc⦘ ⨾ rmw)) \₁ covered tc).
  Proof using.
    rewrite set_minus_union_l. apply set_disjoint_union_r. split. 
    { rewrite issuedW; eauto. type_solver. }
    rewrite wf_rmwD; eauto. type_solver.
  Qed.

  Lemma set_eq_helper {A: Type} (s1 s2: A -> Prop) (EQ: s1 = s2):
    s1 ≡₁ s2.
  Proof using. by rewrite EQ. Qed.

  Lemma set_minus_disjoint {A: Type} (s1 s2: A -> Prop)
        (DISJ: set_disjoint s1 s2):
    s1 \₁ s2 ≡₁ s1.
  Proof using. basic_solver. Qed.


  (* TODO: move upper *)
  Lemma itrav_step_mon_ext_equiv (e: actid)
        (C1 I1 C2 I2 C' I' Cu1 Iu1 Cu2 Iu2: actid -> Prop)
        (STEP: itrav_step G sc e {| covered := C1; issued := I1 |}
                          {| covered := C2; issued := I2 |})
        (EQC1: Cu1 ≡₁ C1 ∪₁ C') (EQI1: Iu1 ≡₁ I1 ∪₁ I')
        (EQC2: Cu2 ≡₁ C2 ∪₁ C') (EQI2: Iu2 ≡₁ I2 ∪₁ I'):
    (itrav_step G sc e)^? (mkTC Cu1 Iu1) (mkTC Cu2 Iu2).
  Proof using.
    forward eapply itrav_step_mon_ext with (C' := C') (I' := I') as STEP'; eauto.
    destruct STEP'.
    { left. apply same_tc_extensionality. rewrite EQC1, EQC2, EQI1, EQI2.
      inversion H. rewrite H1, H2. reflexivity. }
    right. eapply itrav_step_more; [done| .. | by apply H].
    all: red; split; simpl; auto.
  Qed. 

  Add Parametric Morphism thread: (isim_trav_step G sc thread)^? with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_refl_more.
  Proof using. ins. apply same_tc_extensionality in H, H0. by subst. Qed.
    
  Add Parametric Morphism thread: (isim_trav_step G sc thread)^* with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_refl_trans_more.
  Proof using. ins. apply same_tc_extensionality in H, H0. by subst. Qed.

  Lemma itrav_step_mon_ext_cover e
        (C I C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C I) (mkTC (C ∪₁ eq e) I))
        (NEW: set_disjoint (C ∪₁ C') (eq e)):
          (itrav_step G sc e)
                             (mkTC (C ∪₁ C') (I ∪₁ I'))
                             (mkTC (C ∪₁ C' ∪₁ eq e) (I ∪₁ I')).
  Proof using.
    forward eapply itrav_step_mon_ext with (C' := C') (I' := I') as STEP'; eauto. 
    red in STEP. desf; simpl in *. 
    2: { destruct (NEW e); auto. left. apply COVEQ. basic_solver. }
    destruct STEP'.
    { inversion H. destruct (NEW e); auto. rewrite H1. basic_solver. }
    rewrite set_unionA, set_unionC with (s := C'), <- set_unionA. auto. 
  Qed. 
    
  Lemma itrav_step_mon_ext_issue e
        (C I C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C I) (mkTC C (I ∪₁ eq e)))
        (NEW: set_disjoint (I ∪₁ I') (eq e)):
          (itrav_step G sc e)
                             (mkTC (C ∪₁ C') (I ∪₁ I'))
                             (mkTC (C ∪₁ C') (I ∪₁ I' ∪₁ eq e)).
  Proof using.
    forward eapply itrav_step_mon_ext with (C' := C') (I' := I') as STEP'; eauto. 
    red in STEP. desf; simpl in *. 
    { destruct (NEW e); auto. left. apply ISSEQ. basic_solver. }
    destruct STEP'.
    { inversion H. destruct (NEW e); auto. rewrite H1. basic_solver. }
    rewrite set_unionA, set_unionC with (s := I'), <- set_unionA. auto. 
  Qed.

  (* TODO: move to hahn *)
  Lemma set_disjoint_not_eq_r {A: Type} (a : A) (s : A -> Prop):
    ~ set_disjoint s (eq a) <-> s a.
  Proof using.
    pose proof (set_disjoint_eq_r a s) as EQ. apply not_iff_compat in EQ. tauto.
  Qed.

  Section CoverClosure.
    Variables (C I: actid -> Prop).
    Variable (e: actid).
    Let tc := {| covered := C; issued := I |}.
    Let tc' := {| covered := C ∪₁ eq e; issued := I |}.
    Let stc := sim_trav_closure G tc.
    Let stc' := sim_trav_closure G tc'. 
      
    Hypothesis (COH: tc_coherent G sc tc). 
    Hypothesis (COH': tc_coherent G sc tc'). 
    Hypothesis (TRAV_STEP : itrav_step G sc e tc tc'). 
    Hypothesis (NEXT: ~ C e). 
    Hypothesis (COV: coverable G sc tc e).

    Let irel_crmw := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C⦘ ⨾ rmw). 

    Lemma trav_step_closures_isim_cover_read WF WFSC CONS COMP
          (LABe : is_r lab e):
      same_trav_config
        (mkTC (C ∪₁ irel_crmw \₁ C) (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I)) stc ->
      same_trav_config (mkTC (C ∪₁ eq e ∪₁ ((irel_crmw \₁ eq e) \₁ C ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ (C ∪₁ eq e)))
                             (I ∪₁ (codom_rel (⦗C⦘ ⨾ rmw) \₁ I ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ I))) stc' ->
      (isim_trav_step G sc (tid e))＊ stc stc'. 
    Proof using COH COH' COV NEXT TRAV_STEP irel_crmw.
      (* We keep same_trav_config hypotheses in goal to both:
         - be able to rewrite without adding '.. in HYP' 
         - remember that the given TC, even after rewrites, 
           is still a sim_trav_closure which is exploited few times below *)
      
      rename e into r. 
      rewrite set_unionC with (s' := eq r) at 2. rewrite <- set_minus_minus_l.
      
      assert (set_disjoint irel_crmw (eq r)) as NICr.
      { subst irel_crmw. apply set_disjoint_union_l. split.
        { replace I with (issued tc); [| by vauto].
          rewrite issuedW; [| by vauto]. type_solver. }
        rewrite wf_rmwD; auto. type_solver. }
      
      rewrite set_minus_disjoint with (s2 := eq r); auto. 
      rewrite set_minus_disjoint with (s2 := eq r).
      2: { rewrite wf_rmwD; auto. type_solver. }
      
      destruct (classic (dom_rel rmw r)) as [RMWr | NRMWr].
      2: { arewrite (codom_rel (⦗eq r⦘ ⨾ rmw) ≡₁ ∅). 
           { generalize NRMWr. basic_solver. }
           rewrite !set_minusE with (s := ∅).
           rewrite !set_inter_empty_l, !set_union_empty_r.
           
           rewrite set_unionA, set_unionC with (s := eq r), <- set_unionA.
           intros STC STC'.
           apply rt_step. rewrite <- STC, <- STC'.
           apply read_trav_step; auto.
           simpl. apply itrav_step_mon_ext_cover; auto. 
           apply set_disjoint_union_l. split; [basic_solver| ].
           eapply set_disjoint_mori; eauto; [red| ]; basic_solver. }
      
      forward eapply (functional_codom rmw r) as [w RMWD]; auto using wf_rmwf.
      pose proof (proj2 RMWD) as RMW. red in RMW. specialize (RMW w eq_refl).
      red in RMW. desc. apply seq_eqv_l in RMW as [<- RMW].
      rewrite RMWD.
      
      assert (~ C w) as NCw.
      { intros COVw. 
        forward eapply (@dom_sb_covered G) with (T := tc) as COV_SB; eauto.
        specialize (COV_SB r). subst tc. simpl in *. 
        specialize_full COV_SB; [| done].
        exists w. apply rmw_in_sb in RMW; auto. basic_solver. }
      rewrite set_minus_disjoint with (s1 := eq w); [| basic_solver]. 
      
      assert (E w /\ W w) as [Ew Ww].
      { eapply same_relation_exp in RMW.
        2: { rewrite wf_rmwD, wf_rmwE; auto. }
        unfolder in RMW. desc. subst. auto. }
      
      assert (dom_cond sb (C ∪₁ eq r) w) as DC_SBw. 
      { unfolder. ins. desc. subst z y.
        destruct (classic (x = r)) as [-> | ]; [tauto| ]. left.
        apply wf_rmwi in RMW as [SBrw IMMrw]; auto.
        assert ((sb ⨾ ⦗C ∪₁ eq r⦘) x r) as SBxr.
        { apply seq_eqv_r. split; [| basic_solver]. 
          eapply sb_semi_total_r in SBrw; eauto.
          2: { eapply read_or_fence_is_not_init; eauto. }
          des; auto. edestruct IMMrw; eauto. }
        forward eapply (@dom_sb_covered G) with (T := tc') as SB_COV; eauto.
        specialize (SB_COV x). specialize_full SB_COV; [by vauto| ].
        subst tc'. simpl in *. 
        destruct SB_COV; vauto. }
      
      assert (set_disjoint (eq w) (codom_rel (⦗C⦘ ⨾ rmw))) as DISJW.
      { intros ? <- INTER. red in INTER. desc.
        apply seq_eqv_l in INTER. desc.
        forward eapply (wf_rmw_invf WF w r x) as ->; eauto. }
      
      destruct (classic (is_rel lab w)) as [RELw | NRELw].
      { assert (~ I w) as NIw. 
        { intros ISSw. cdes COH. unfold tc in II. apply II in ISSw.
          red in ISSw. apply proj1, proj2 in ISSw.
          red in ISSw. specialize (ISSw r). specialize_full ISSw; [| done]. 
          apply dom_rel_fun_alt. red. repeat left.
          apply seq_eqv_r. unfolder; splits; auto.
            by apply rmw_in_sb. }
        rewrite set_minus_disjoint with (s1 := eq w); [| basic_solver]. 
        
        rewrite set_unionA with (s' := eq r), <- set_unionA with (s := eq r).
        rewrite set_unionC with (s := eq r). rewrite <- !set_unionA.
        
        assert (~ (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I) w) as NICRMWw.
        { apply and_not_or. split; auto.
          apply or_not_and. left. generalize DISJW. basic_solver. }
        
        remember (mkTC (C ∪₁ irel_crmw \₁ C) (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I)) as tcc0.
        assert (tc_coherent G sc tcc0) as COHc0.
        { eapply tc_coherent_more. 
          2: { apply stc_coherent with (tc := tc); auto. }
          unfold sim_trav_closure.
          unfold trav_config_union, Cclos, Iclos. subst tc. simpl in *.
          fold irel_crmw. subst tcc0. reflexivity. }  
        
        remember (mkTC (C ∪₁ irel_crmw \₁ C ∪₁ eq r) (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I)) as tcc1. 
        assert (itrav_step G sc r tcc0 tcc1) as STEP1.
        { subst. apply itrav_step_mon_ext_cover; auto. 
          simpl. apply set_disjoint_union_l. split; [basic_solver| ].
          generalize NICr. basic_solver 10. }
        assert (tc_coherent G sc tcc1) as COHc1.
        { eapply trav_step_coherence; eauto. red. eauto. }
        
        assert (set_compl (C ∪₁ irel_crmw \₁ C ∪₁ eq r) w) as NNNw.
        { apply set_compl_union. split.
          2: { intros ->. type_solver. }
          apply set_compl_union. split; auto.
          unfolder. apply or_not_and. left. intros ICw. destruct NICRMWw.
          subst irel_crmw. destruct ICw as [ICw | ICw]; [left; by apply ICw| ].
          edestruct DISJW; eauto. }
        
        intros STC STC'. 
        
        apply rt_step. rewrite <- STC, <- STC'.
        rewrite Heqtcc0. apply rel_rmw_step; auto; simpl.
        { congruence. }
        { red. right. red. splits; simpl; auto.
          rewrite <- Heqtcc1. 
          apply issuable_next_w; auto. split; auto.
          subst tcc1. simpl. red. unfold set_inter. splits; auto.
          eapply dom_cond_mori; [red; reflexivity| ..| by apply DC_SBw].
          basic_solver. }
        
        red. left. simpl. splits; auto. 
        { apply coverable_add_eq_iff; auto. simpl.
          apply covered_in_coverable; auto.
          2: { simpl. basic_solver. }
          rewrite STC'. subst stc'. apply stc_coherent; auto. }
      }
      
      intros STC STC'.
      
      enough ((isim_trav_step G sc (tid r))＊ stc (mkTC (covered stc) (issued stc ∪₁ eq w))) as ISS_W_STEP. 
      { eapply rt_unit. eexists. split; [by apply ISS_W_STEP| ].
        
        eapply isim_trav_step_more.
        { rewrite <- (covered_more STC), <- (issued_more STC). simpl. reflexivity. }
        { rewrite <- STC'. reflexivity. }
        
        eapply isim_trav_step_more; [reflexivity| ..].
        { rewrite set_unionA. rewrite <- set_unionA with (s := eq r).
          rewrite set_unionC with (s := eq r). rewrite <- !set_unionA with (s := C).
          rewrite set_unionC with (s' := eq w \₁ I), <- set_unionA with (s' := eq w \₁ I).
          rewrite <- set_union_strict with (s2 := eq w).
          rewrite set_unionA with (s' := eq w), set_unionC with (s := eq w).
          rewrite <- set_unionA with (s := I). reflexivity. }
        
        apply rlx_rmw_cover_step; auto; simpl.
        { basic_solver. }
        { rewrite !set_unionA with (s := I). 
          apply itrav_step_mon_ext_cover. 
          { by subst tc tc'. }
          apply set_disjoint_union_l. split.
          { apply set_disjoint_eq_r. intros Cr.
            apply (DISJW w); basic_solver. }
          generalize NICr. basic_solver. }
        red. left. splits; simpl.
        { intros INw. destruct INw as [[Cw | ICw] | ->]; auto.
          2: { type_solver. }
          destruct ICw. subst irel_crmw.
          generalize H, NRELw, DISJW. basic_solver 10. }
        { red. split.
          { split; auto. simpl. red. red in DC_SBw.
            rewrite DC_SBw. basic_solver. }
          repeat left. split; auto. simpl. basic_solver. }
        { basic_solver. }
        basic_solver. }
      
      destruct (classic (I w)) as [Iw | NIw].
      { apply rtE. left. red. split; auto.
        apply same_tc_extensionality; split; simpl; [basic_solver| ].
        generalize Iw. basic_solver 10. }
      
      apply rt_step. eapply isim_trav_step_more.
      { symmetry. apply STC. }
      { rewrite <- (covered_more STC), <- (issued_more STC). simpl. reflexivity. }
      replace (tid r) with (tid w).
      2: { symmetry. eapply wf_rmwt; eauto. }
      
      eapply rlx_write_promise_step; auto; simpl. 
      { intros [? | [CRMW ?]]; [done| ].
        apply DISJW in CRMW; auto. }
      red. right. simpl. splits.
      3, 4: basic_solver. 
      { intros [? | [CRMW ?]]; [done| ].
        apply DISJW in CRMW; auto. }
      (* TODO: can it be simplified? *)
      red. split.
      { split; [basic_solver| ]. simpl.
        red in DC_SBw.
        unfold "fwbob". 
        red. intros x [w_ DOMx%seq_eqv_r]. desc. subst w_.
        unfolder in DOMx. des; [by vauto| ..]. 
        { specialize (DC_SBw x). specialize_full DC_SBw.
          { exists w. basic_solver. }
          destruct DC_SBw as [| ->]; [repeat left; basic_solver| ].
          type_solver. }
        { type_solver. }
        specialize (DC_SBw x). specialize_full DC_SBw.
        { exists w. basic_solver. }
        destruct DC_SBw as [| ->]; [repeat left; basic_solver| ].
        type_solver. }
        
      simpl. red. 
      forward eapply ar_rf_ppo_loc_ct_I_in_I as AR_CLOS_INCL.
      { eapply stc_coherent; eauto. }
      fold stc' in AR_CLOS_INCL. 
      erewrite issued_more in AR_CLOS_INCL.
      2: { symmetry. eauto. }
      simpl in AR_CLOS_INCL.
      
      rewrite !id_union, !seq_union_r, !dom_union in AR_CLOS_INCL.
      do 2 apply set_subset_union_l, proj2 in AR_CLOS_INCL.
      rewrite set_minus_disjoint in AR_CLOS_INCL; [| basic_solver].
      rewrite <- set_unionA in AR_CLOS_INCL.
      red. intros e DOMe.
      specialize (AR_CLOS_INCL e). specialize_full AR_CLOS_INCL. 
      { red in DOMe. desc. apply seq_eqv_r in DOMe. desc. subst y.
        apply seq_eqv_l in DOMe. desc. 
        exists w. apply seq_eqv_lr. splits; vauto. }
      destruct AR_CLOS_INCL; auto. subst e. 
      edestruct ar_rf_ppo_loc_acyclic with (x := w); eauto.
      generalize DOMe. basic_solver 10.
    Qed.

    Lemma trav_step_closures_isim_cover_write WF WFSC CONS COMP
          (LABe : is_w lab e):
      same_trav_config
        (mkTC (C ∪₁ irel_crmw \₁ C) (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I)) stc ->
      same_trav_config
        (mkTC
           (C ∪₁ eq e ∪₁ ((irel_crmw \₁ eq e) \₁ C ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ (C ∪₁ eq e)))
           (I ∪₁ (codom_rel (⦗C⦘ ⨾ rmw) \₁ I ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ I)))
        stc' ->
      (isim_trav_step G sc (tid e))＊ stc stc'.
    Proof using TRAV_STEP NEXT COV COH'.
      rename e into w. 
      assert (I w) as Iw. 
      { replace I with (issued tc') by vauto. 
        eapply tc_W_C_in_I.
        { subst tc'. eapply tc_coherent_implies_tc_coherent_alt; eauto. }
        subst tc'. split; basic_solver. }
      assert (codom_rel (⦗eq w⦘ ⨾ rmw) ≡₁ ∅) as NOWRMW.
      { rewrite wf_rmwD; auto. type_solver. }
      rewrite !NOWRMW.
      rewrite !set_minusE with (s := ∅), !set_inter_empty_l, !set_union_empty_r.
      
      destruct (classic (set_disjoint irel_crmw (eq w))) as [NEWw | OLDw].
      2: { intros STC STC'.
           eapply isim_trav_step_refl_trans_more.
           1, 2: symmetry; by eauto. 
           apply rtE. left. red. split; [| done].
           apply same_tc_extensionality; split; simpl; [| basic_solver].
           rewrite set_unionA. apply set_equiv_union; [basic_solver| ].
           rewrite <- (set_minus_disjoint (eq w) C) at 1; [| basic_solver]. 
           rewrite <- set_minus_union_l. apply set_equiv_minus; [| basic_solver].
           rewrite <- set_union_strict.
           edestruct @set_disjoint_not_eq_r as [SD _]. specialize (SD OLDw).  
           basic_solver. }
      
      rewrite !(set_minus_disjoint _ _ NEWw).
      intros STC STC'. 
      
      apply rt_step. eapply isim_trav_step_more.
      { symmetry; by eauto. }
      { rewrite <- STC'.
        rewrite set_unionA, set_unionC with (s := eq w), <- set_unionA.
        reflexivity. }
      
      apply set_disjointC in NEWw as NEWw_. specialize (NEWw_ w eq_refl).
      unfold irel_crmw in NEWw_. 
      apply Decidable.not_or in NEWw_ as [NRELw_ NCRMWw].  
      assert (~ is_rel lab w) as NRELw; [| clear NRELw_].
      { intros ?. by destruct NRELw_. }
      
      apply rlx_write_cover_step; auto.
      { intros [r RMW].
        red in COV. destruct COV as [[_ SB_COV] _].
        specialize (SB_COV r). specialize_full SB_COV.
        { exists w. apply seq_eqv_r. split; auto. by apply rmw_in_sb. }
        destruct NCRMWw. exists r. apply seq_eqv_l.
        subst tc. split; auto. }
      { simpl. left. basic_solver. }
      simpl.
      apply itrav_step_mon_ext_cover. 
      { by subst tc tc'. }
      apply set_disjoint_union_l. split; basic_solver.
    Qed. 
      
    Lemma trav_step_closures_isim_cover_fence WF WFSC CONS COMP
          (LABe : is_f lab e):
      same_trav_config
        (mkTC (C ∪₁ irel_crmw \₁ C) (I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I)) stc ->
      same_trav_config
        (mkTC
           (C ∪₁ eq e ∪₁ ((irel_crmw \₁ eq e) \₁ C ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ (C ∪₁ eq e)))
           (I ∪₁ (codom_rel (⦗C⦘ ⨾ rmw) \₁ I ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw) \₁ I)))
        stc' ->
      (isim_trav_step G sc (tid e))＊ stc stc'.
    Proof using TRAV_STEP NEXT COV COH' COH.
      rename e into f.
      assert (codom_rel (⦗eq f⦘ ⨾ rmw) ≡₁ ∅) as NOFRMW.
      { rewrite wf_rmwD; auto. type_solver. }
      rewrite !NOFRMW.
      rewrite !set_minusE with (s := ∅), !set_inter_empty_l, !set_union_empty_r.
      
      assert (set_disjoint irel_crmw (eq f))
        as F_NI_NCRMW. 
      { subst irel_crmw. 
        forward eapply issuedW as IW; [by apply COH| ].
        subst tc. rewrite IW. rewrite wf_rmwD; auto. type_solver. }
      rewrite set_minus_disjoint with (s2 := eq f); auto. 
      
      intros STC STC'. apply rt_step.
      eapply isim_trav_step_more.
      { symmetry; by eauto. }
      { rewrite <- STC'.
        rewrite set_unionA, set_unionC with (s := eq f), <- set_unionA.
        reflexivity. }
      apply fence_trav_step; auto. simpl.
      apply itrav_step_mon_ext_cover.
      { by subst tc tc'. }
      apply set_disjoint_union_l. split; basic_solver.
    Qed. 
    
    Lemma trav_step_closures_isim_cover WF WFSC CONS COMP:
      same_trav_config {|
          covered :=
            C
              ∪₁ (I ∩₁ (fun a : actid => is_rel lab a) ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C;
          issued := I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I
        |} (sim_trav_closure G tc) ->
      same_trav_config {|
          covered :=
            C ∪₁ eq e
              ∪₁ (I ∩₁ (fun a : actid => is_rel lab a)
                    ∪₁ codom_rel (⦗C ∪₁ eq e⦘ ⨾ rmw)) \₁ (C ∪₁ eq e);
          issued := I ∪₁ codom_rel (⦗C ∪₁ eq e⦘ ⨾ rmw) \₁ I
        |} (sim_trav_closure G tc') ->
      (isim_trav_step G sc (tid e))＊ (sim_trav_closure G tc)
                                   (sim_trav_closure G tc').
    Proof using TRAV_STEP NEXT COV COH' COH.
      rewrite !id_union, !seq_union_l, !codom_union.
      rewrite <- set_unionA with (s' := codom_rel (⦗C⦘ ⨾ rmw)).
      rewrite !set_minus_union_l with (s' := codom_rel (⦗eq e⦘ ⨾ rmw)).
      rewrite set_unionC with (s' := eq e) at 2. rewrite <- set_minus_minus_l. 
      
      pose proof (lab_rwf lab e) as LABe.
      des; auto using trav_step_closures_isim_cover_read,
           trav_step_closures_isim_cover_write,
           trav_step_closures_isim_cover_fence. 
    Qed.

  End CoverClosure.

  Section IssueClosure.
    Variables (C I: actid -> Prop).
    Variable (e: actid).
    Let tc := {| covered := C; issued := I |}.
    Let tc' := {| covered := C; issued := I ∪₁ eq e|}.
    Let stc := sim_trav_closure G tc.
    Let stc' := sim_trav_closure G tc'. 
      
    Hypothesis (COH: tc_coherent G sc tc). 
    Hypothesis (COH': tc_coherent G sc tc'). 
    Hypothesis (TRAV_STEP : itrav_step G sc e tc tc'). 
    Hypothesis (NISS: ~ I e).
    Hypothesis (ISS: issuable G sc tc e).

    Let irel_crmw := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C⦘ ⨾ rmw).

    Lemma trav_step_closures_isim_issue WF WFSC CONS COMP:
      same_trav_config {|
          covered :=
            C
              ∪₁ (I ∩₁ (fun a : actid => is_rel lab a) ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C;
          issued := I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I
        |} (sim_trav_closure G tc) ->
      same_trav_config {|
          covered :=
            C
              ∪₁ ((I ∪₁ eq e) ∩₁ (fun a : actid => is_rel lab a)
                    ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C;
          issued := I ∪₁ eq e ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ (I ∪₁ eq e)
        |} (sim_trav_closure G tc') ->
      (isim_trav_step G sc (tid e))＊ (sim_trav_closure G tc) (sim_trav_closure G tc').
    Proof using TRAV_STEP NISS ISS COH' COH.
      rename e into w. 
      assert (is_w lab w) as Ww.
      { eapply issuedW; [by apply COH'| ]. subst tc'. basic_solver. }
      assert (~ C w) as NCw.
      { intros Cw. forward eapply (w_covered_issued COH). basic_solver. }

      rewrite set_inter_union_l, set_unionA.
      rewrite set_unionC with (s := eq w ∩₁ _), <- set_unionA.
      rewrite set_minus_union_l with (s' := eq w ∩₁ _).
      rewrite set_minus_disjoint with (s1 := eq w ∩₁ _); [| basic_solver].
      rewrite <- set_minus_minus_l, set_unionA.
      rewrite <- set_union_strict with (s1 := eq w).

      destruct (classic (codom_rel (⦗C⦘ ⨾ rmw) w)) as [CRMWw | NCRMWw].
      { rewrite set_union_absorb_l with (s := eq w).
        2: { generalize CRMWw. basic_solver. }
        rewrite set_minus_union_l, set_unionA.
        rewrite set_union_absorb_r with (s := eq w ∩₁ _).
        2: { generalize CRMWw. basic_solver. } 
        rewrite <- set_minus_union_l. fold irel_crmw. 
        intros -> ->. apply rt_refl. }      
      
      destruct (classic (is_rel lab w)) as [RELw | NRELw].
      2: { rewrite (proj1 (set_disjointE (eq w) (is_rel lab))); [| basic_solver].
           rewrite set_union_empty_r.
           fold irel_crmw.           
           rewrite set_unionC with (s := eq w), <- set_unionA.
           intros <- <-. 
           apply rt_step. apply rlx_write_promise_step; auto.
           { simpl. intros [? | [?]]; basic_solver. }
           simpl. apply itrav_step_mon_ext_issue.
           { by fold tc tc'. }
           simpl. apply set_disjoint_eq_r. intros [? | [?]]; basic_solver. }

      rewrite set_inter_absorb_r with (s := eq w); [| basic_solver].
      fold irel_crmw.

      rewrite set_unionC with (s := eq w), <- !set_unionA.
      intros STC STC'. rewrite <- STC, <- STC'. 
      apply rt_step. apply rel_write_step; auto.
      { intros [r RMW]. apply NCRMWw. exists r. apply seq_eqv_l. split; auto.
        cdes ISS. apply proj1, proj2 in ISS0. red in ISS0. apply ISS0.
        red. exists w. apply seq_eqv_r. split; auto.
        red. repeat left. apply seq_eqv_r. split; [| basic_solver].
        by apply rmw_in_sb. }
      { simpl. intros [? | [?]]; basic_solver. }
      { simpl. apply itrav_step_mon_ext_issue.
        { by fold tc tc'. }
        simpl. apply set_disjoint_eq_r. intros [? | [?]]; basic_solver. }

      simpl. red. left. splits.
      3, 4: simpl; basic_solver.
      { simpl. unfold irel_crmw. intros [? | IC]; [by auto| ].
        red in IC. desc. destruct IC as [IC | IC]; auto.
        destruct NISS. apply IC. }
      simpl. apply coverable_add_eq_iff; auto.
      simpl. apply covered_in_coverable; [| simpl; basic_solver].
      rewrite STC'. apply stc_coherent; auto. 
    Qed. 

  End IssueClosure.

  Lemma trav_step_closures_isim WF WFSC CONS COMP
        (tc tc': trav_config)
        (COH: tc_coherent G sc tc)
        (COH': tc_coherent G sc tc')
        (TRAV_STEP: trav_step G sc tc tc'):
    (sim_trav_step G sc)^* (sim_trav_closure G tc) (sim_trav_closure G tc').
  Proof using.    
    red in TRAV_STEP. desc. 
    enough ((isim_trav_step G sc (tid e))^* (sim_trav_closure G tc) (sim_trav_closure G tc')) as ISIM.
    { apply rtE in ISIM as [[-> _] | ?]; [apply rt_refl| ]. 
      apply rtE. right. induction H.
      { apply ct_step. red. eauto. }
      eapply transitive_ct; eauto. }
    
    unfold sim_trav_closure, Cclos, Iclos.
    destruct tc as [C I], tc' as [C' I']. simpl in *.

    pose proof TRAV_STEP as TRAV_STEP_. 
    red in TRAV_STEP_. des; rewrite !COVEQ, !ISSEQ in *; simpl in *. 
    { apply trav_step_closures_isim_cover; auto; reflexivity. }
    apply trav_step_closures_isim_issue; auto; reflexivity. 
  Qed. 
  
  Section Traversal.
    Variable (steps: nat -> trav_label).
    Hypothesis (ENUM: enumerates steps (graph_steps G)).
    Hypothesis (RESP: respects_rel steps (iord G sc)⁺ (graph_steps G)).
    
    Definition tc_enum (i: nat): trav_config :=
      sim_trav_closure G (set2trav_config G (trav_prefix steps i)).

    Lemma sim_traversal_next WF COMP WFSC CONS MF:
      forall i (DOMi: NOmega.lt_nat_l i (set_size (graph_steps G))),
        (sim_trav_step G sc)^* (tc_enum i) (tc_enum (1 + i)).
    Proof using RESP ENUM.
      ins.
      unfold tc_enum. apply trav_step_closures_isim; auto.
      1, 2: apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. 
      { apply NOmega.lt_le_incl, DOMi. }
      apply trav_prefix_step; auto. 
    Qed. 
          
  End Traversal.

  Lemma sim_trav_closure_init WF:
    sim_trav_closure G (init_trav G) = init_trav G.
  Proof using.
    unfold sim_trav_closure. simpl. apply same_tc_extensionality.
    red. unfold Cclos, Iclos. splits; simpl.
    { split; [| basic_solver 10]. apply set_subset_union_l.
      split; try basic_solver. etransitivity; [| by apply set_subset_empty_l].
      rewrite set_minus_union_l. apply set_subset_union_l. split; [basic_solver|].
      unfolder. ins. desc. apply wf_rmwD, seq_eqv_lr in H1; auto. desc.
      generalize (@read_or_fence_is_not_init _ WF x0). tauto. } 
    split; [| basic_solver 10]. apply set_subset_union_l.
    split; try basic_solver. etransitivity; [| by apply set_subset_empty_l]. 
    unfolder. ins. desc. apply wf_rmwD, seq_eqv_lr in H1; auto. desc.
    generalize (@read_or_fence_is_not_init _ WF x0). tauto.
  Qed. 

  (* TODO: move to IordTraversal *)
  Global Add Parametric Morphism: (set2trav_config G) with signature
      (@set_equiv trav_label) ==> same_trav_config as set2trav_config_more. 
  Proof using.
    ins. unfold set2trav_config. split; rewrite H; simpl; basic_solver. 
  Qed.
    
  (* TODO: move to IordTraversal *)
  Lemma set2trav_config_empty:
    set2trav_config G ∅ = init_trav G.
  Proof using.
    unfold set2trav_config. apply same_tc_extensionality. unfold init_trav.
    split; basic_solver. 
  Qed. 

  Lemma sim_traversal_inf WF COMP WFSC CONS MF
        (IMM_FAIR: imm_s_fair G sc):
    exists (sim_enum: nat -> trav_config),
      ⟪INIT: sim_enum 0 = init_trav G ⟫ /\
      ⟪DOM_TC: forall i (DOMi: NOmega.le (NOnum i) (set_size (graph_steps G))),
          covered (sim_enum i) ⊆₁ E /\ issued (sim_enum i) ⊆₁ E ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size (graph_steps G))),
          tc_coherent G sc (sim_enum i) ⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size (graph_steps G))),
          (sim_trav_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
      ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i,
          NOmega.le (NOnum i) (set_size (graph_steps G)) /\
          covered (sim_enum i) e⟫.
  Proof using.
    edestruct iord_enum_exists as [steps_enum [ENUM RESP]]; eauto.
    exists (tc_enum steps_enum). splits.
    { unfold tc_enum, trav_prefix. rewrite <- sim_trav_closure_init; auto. f_equal.
      apply same_tc_extensionality.
      arewrite ((fun i => i < 0) ≡₁ (@set_empty nat)).
      { split; [red; ins; lia| basic_solver]. }
      rewrite set_bunion_empty. by rewrite set2trav_config_empty. }      
    3: { apply sim_traversal_next; auto. }
    2: { ins. unfold tc_enum. apply stc_coherent; auto.
         apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. }
    { intros i DOM. unfold tc_enum. eapply stc_domE; eauto.
      1, 2: unfold set2trav_config; simpl; basic_solver.
      apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. }
    intros e Ee.
    pose proof ENUM as ENUM'. apply enumeratesE' in ENUM. desc.
    specialize (IND (mkTL ta_cover e)). specialize_full IND; [by vauto| ].
    desc. exists (S i). split; [by vauto| ]. 
    unfold tc_enum, sim_trav_closure. 
    unfold trav_config_union. simpl. left. split; [| by apply Ee].
    left. split; [| by apply Ee].
    exists (mkTL ta_cover e). split; auto. split; [by vauto| ].
    rewrite <- IND0. eapply trav_prefix_ext; eauto. basic_solver. 
  Qed. 

End STCTraversal.   
