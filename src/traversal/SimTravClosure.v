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

Module SimTravClosure. 
  Include TraversalOrder.TravLabel.
  Import IordTraversal.
  
  Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).

  Definition sim_trav_closure (TC: trav_config) :=
    let (C, I) := TC in
    let C' := C ∪₁ I ∩₁ is_rel lab in
    let C'' := C' ∪₁ codom_rel (⦗C'⦘ ⨾ rmw) in
    mkTC
      C''
      (I ∪₁ C'' ∩₁ W).

  Definition Cclos (tc: trav_config) :=
    (* issued tc ∩₁ (is_rel lab) ∪₁ codom_rel (⦗covered tc ∪₁ issued tc ∩₁ is_rel lab⦘ ⨾ rmw). *)
    issued tc ∩₁ (is_rel lab) ∪₁ codom_rel (⦗covered tc⦘ ⨾ rmw).
  Definition Iclos (tc: trav_config) :=
    (* (covered tc ∪₁ Cclos tc) ∩₁ W. *)
    codom_rel (⦗covered tc⦘ ⨾ rmw). 

  Lemma codom_I_rmw_empty WF WFSC
        (tc: trav_config) (COH: tc_coherent G sc tc):
    codom_rel (⦗(issued tc) ∩₁ is_rel lab⦘ ⨾ rmw) ≡₁ ∅.
  Proof.
    rewrite wf_rmwD; auto. repeat seq_rewrite <- id_inter.
    forward eapply tc_I_in_W as IW; eauto.
    { apply tc_coherent_implies_tc_coherent_alt; eauto. }
    simpl in IW. split; [| basic_solver]. rewrite IW. type_solver.
  Qed. 

  Lemma set_union_strict {A: Type}
        (* (s1 s2 sm: A -> Prop) *)
        (s1 s2: A -> Prop)
        (* (SUB: s1 ⊆₁ sm): *)
        :
    s1 ∪₁ s2 ≡₁ s1 ∪₁ s2 \₁ s1.
  Proof.
    split; [| basic_solver].
    intros x Sx. destruct (classic (s1 x)); [basic_solver| ].
    destruct Sx; [done| ]. basic_solver. 
    (* right. destruct (classic (sm x)); [| basic_solver]. *)
  Qed.

  Lemma stc_alt WF WFSC
        (tc: trav_config) (COH: tc_coherent G sc tc):
    sim_trav_closure tc = tc ⊔ (mkTC (Cclos tc \₁ covered tc) (Iclos tc \₁ issued tc)). 
  Proof.
    forward eapply tc_coherent_implies_tc_coherent_alt as COH'; eauto.
    forward eapply codom_I_rmw_empty as IW; eauto. simpl in IW.
    unfold sim_trav_closure, Iclos, Cclos. destruct tc as [C I]. simpl.
    unfold trav_config_union. simpl. 
    apply trav_config_eq_helper; simpl.
    { rewrite <- set_union_strict.
      rewrite id_union, !seq_union_l. rewrite codom_union.
      rewrite IW. basic_solver 10. }
    rewrite <- set_union_strict. 
    rewrite !set_inter_union_l.
    rewrite <- !set_unionA. apply set_equiv_union.
    { split; [| basic_solver].
      forward eapply tc_W_C_in_I as CI; eauto.         
      simpl in CI. rewrite CI. basic_solver. }
    
    split.
    2: { rewrite wf_rmwD at 1; auto.
         basic_solver. }
    rewrite id_union, !seq_union_l. rewrite codom_union.
    rewrite IW. basic_solver 10. 
  Qed.

  (* Lemma stc_alt_unfolded (tc: trav_config): *)
  (*   let (C, I) := tc in *)
  (*   let C' := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ is_rel lab⦘ ⨾ rmw) in *)
  (*   let I' := (C ∪₁ I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ (is_rel lab)⦘ ⨾ rmw)) ∩₁ W in *)
  (*   sim_trav_closure tc = tc ⊔ (mkTC C' I').  *)
  (* Proof. *)
  (*   unfold sim_trav_closure. destruct tc as [C I]. simpl. *)
  (*   apply trav_config_eq_helper; simpl; basic_solver 10. *)
  (* Qed.      *)

  (* Lemma stc_alt_unfolded (tc: trav_config): *)
  (*   let (C, I) := tc in *)
  (*   let C' := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ is_rel lab⦘ ⨾ rmw) in *)
  (*   let I' := (C ∪₁ I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ (is_rel lab)⦘ ⨾ rmw)) ∩₁ W in *)
  (*   sim_trav_closure tc = tc ⊔ (mkTC C' I'). *)
  (* Proof. *)
  (*   unfold sim_trav_closure. destruct tc as [C I]. simpl. *)
  (*   apply trav_config_eq_helper; simpl; basic_solver 10. *)
  (* Qed. *)

  Lemma stc_tcu_distribute (tc1 tc2: trav_config):
    sim_trav_closure (tc1 ⊔ tc2) =
    (sim_trav_closure tc1) ⊔ (sim_trav_closure tc2).
  Proof. 
    unfold sim_trav_closure, trav_config_union.
    destruct tc1 as [C1 I1], tc2 as [C2 I2]. simpl.
    apply trav_config_eq_helper; simpl; basic_solver 10. 
  Qed.

  Lemma tcu_assoc (tc1 tc2 tc3: trav_config):
     (tc1 ⊔ tc2) ⊔ tc3 = tc1 ⊔ (tc2 ⊔ tc3).
  Proof.
    destruct tc1, tc2, tc3. unfold trav_config_union.
    apply trav_config_eq_helper; simpl; basic_solver.
  Qed.

  Lemma tcu_symm (tc1 tc2: trav_config):
    tc1 ⊔ tc2 = tc2 ⊔ tc1. 
  Proof.
    destruct tc1, tc2. unfold trav_config_union.
    apply trav_config_eq_helper; simpl; basic_solver.
  Qed.

  (* Lemma sim_trav_step_closure (tc tc': trav_config) *)
  (*       (SIM_TRAV_STEP: (sim_trav_step G sc)^? tc (trav_config_union tc tc')): *)
  (*   (sim_trav_step G sc)^? (sim_trav_closure tc) (trav_config_union (sim_trav_closure tc) (sim_trav_closure tc')). *)
  (* Proof.  *)
  (*   destruct SIM_TRAV_STEP. *)
  (*   2: { red in H. desc. right. exists thread. inversion H; subst. *)
  (*        { rewrite !stc_alt.  *)
  (* Admitted.  *)

  Lemma trav_config_eq_helper' (tc: trav_config) (C' I': actid -> Prop)
        (COV: covered tc ≡₁ C') (ISS: issued tc ≡₁ I'):
    tc = mkTC C' I'.
  Proof. apply trav_config_eq_helper; auto. Qed.

  Lemma itrav_step_mon_ext e
        (C1 I1 C2 I2 C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C1 I1) (mkTC C2 I2))
        :
          (itrav_step G sc e)^?
                             (mkTC (C1 ∪₁ C') (I1 ∪₁ I'))
                             (mkTC (C2 ∪₁ C') (I2 ∪₁ I')).
  Proof.
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

  (* TODO: move into TraversalConfig *)
  (* TODO: rename? *)
  Global Add Parametric Morphism : mkTC with signature
      (@set_equiv actid) ==> (@set_equiv actid) ==> same_trav_config as mkTC_more.
  Proof using. vauto. Qed.  
  

  (* TODO: move to TraversalConfig? *)
  Lemma same_tc_extensionality tc1 tc2 (SAME: same_trav_config tc1 tc2):
    tc1 = tc2.
  Proof. destruct SAME. apply trav_config_eq_helper; auto. Qed. 
    
  Add Parametric Morphism thread: (isim_trav_step G sc thread) with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_more.
  Proof. ins. apply same_tc_extensionality in H, H0. by subst. Qed.     

  Lemma itrav_step_mon_ext' e
        (C1 I1 C2 I2 C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C1 I1) (mkTC C2 I2))
        (NEW: ~ ((C1 ∪₁ C') ∪₁ (I1 ∪₁ I')) e)
        :
          itrav_step G sc e
                             (mkTC (C1 ∪₁ C') (I1 ∪₁ I'))
                             (mkTC (C2 ∪₁ C') (I2 ∪₁ I')).
  Proof.
    forward eapply itrav_step_mon_ext as [EQ | ?]; eauto.
    inversion EQ. exfalso. red in STEP. desf; simpl in *.
    { destruct NEW. left. rewrite H0. left. apply COVEQ. basic_solver. }
    destruct NEW. right. rewrite H1. left. apply ISSEQ. basic_solver.
  Qed. 

  (* Lemma isim_trav_step_mon_add_cov (e: actid) *)
  (*       (C1 I1 C2 I2 C' I': actid -> Prop) *)
  (*       (STEP: itrav_step G sc e {| covered := C1; issued := I2 |} *)
  (*                         {| covered := C1 ∪₁ eq e; issued := I2 |}) *)
  (*       (NCOVe: ~ (C1 ∪₁ C') e): *)
  (* isim_trav_step G sc (tid e) {| covered := C1 ∪₁ C'; issued := I2 ∪₁ I' |} *)
  (*                {| covered := C1 ∪₁ eq e ∪₁ C'; issued := I2 ∪₁ I' |}. *)
  (* Proof. *)
  (*   assert (C1 ∪₁ eq e ∪₁ C' ≡₁ C1 ∪₁ C' ∪₁ eq e) as C_ALT by basic_solver.  *)
  (*   erewrite trav_config_eq_helper'; [| simpl; by apply C_ALT | reflexivity]. *)
  (*   simpl. *)

    
    
  (*   apply fence_trav_step; auto. simpl. *)
  (*   erewrite trav_config_eq_helper'; [| simpl; by rewrite <- C_ALT | reflexivity]. *)
  (*   simpl. *)
  (*   eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?]. *)
  (*   2: { eapply itrav_step_more; [reflexivity| .. | apply H0]. *)
  (*        all: by apply same_tc_Symmetric. } *)
  (*   inversion H0. destruct H. rewrite H2. basic_solver.      *)

  (* Lemma stc_coherent (tc: trav_config) WF WFSC *)
  (*       (COH: tc_coherent G sc tc): *)
  (*   tc_coherent G sc (sim_trav_closure tc). *)
  (* Proof. *)
  (*   pose proof COH as COH'. red in COH'. desc.  *)
  (*   rewrite stc_alt; auto. *)
  (*   forward eapply codom_I_rmw_empty as CIR; eauto.  *)
  (*   destruct tc as [C I] eqn:TC. simpl in *.  *)
  (*   unfold trav_config_union. simpl. red. splits; simpl.  *)
  (*   { etransitivity; [apply ICOV| ]. basic_solver. } *)
  (*   { unfold Cclos, coverable. simpl.  *)

  Lemma sb_invrmw_sbclos WF:
    sb ⨾ rmw⁻¹ ⊆ sb^?.
  Proof.
    red. ins. destruct (classic (x = y)); [by left| ].
    right. red in H. destruct H as [w [SB RMW]]. red in RMW.
    forward eapply (wf_rmwi WF _ _ RMW) as [SByw IMMyw]. 
    eapply sb_semi_total_r in SByw; eauto.
    2: { eapply read_or_fence_is_not_init; eauto. left.
         apply wf_rmwD, seq_eqv_lr in RMW; auto. by desc. }
    des; auto. edestruct IMMyw; eauto. 
  Qed. 
    
  (* Lemma sb_invrmw_sbclos_ext WF: *)
  (*   sb ⨾ rmw⁻¹ ⊆ sb^? ⨾ ⦗W⦘ ⨾ sb^?. *)
  (* Proof. *)
  (*   red. ins. destruct (classic (x = y)). *)
  (*   { subst. red in H. desc. red in H0.  *)
  (*     apply seqA. red. exists z. split; [| basic_solver]. *)
  (*     apply seq_eqv_r. split; [| basic_solver]. *)
  (*   right. red in H. destruct H as [w [SB RMW]]. red in RMW. *)
  (*   forward eapply (wf_rmwi WF _ _ RMW) as [SByw IMMyw].  *)
  (*   eapply sb_semi_total_r in SByw; eauto. *)
  (*   2: { eapply read_or_fence_is_not_init; eauto. left. *)
  (*        apply wf_rmwD, seq_eqv_lr in RMW; auto. by desc. } *)
  (*   des; auto. edestruct IMMyw; eauto.  *)
  (* Qed.  *)
    
  Lemma stc_coherent (tc: trav_config) WF WFSC CONS
        (COH: tc_coherent G sc tc):
    tc_coherent G sc (sim_trav_closure tc).
  Proof.
    apply tc_coherent_alt_implies_tc_coherent.
    pose proof COH as COH'. apply tc_coherent_implies_tc_coherent_alt in COH'; auto.
    inversion COH'.
    rewrite stc_alt; auto.
    forward eapply codom_I_rmw_empty as CIR; eauto.
    destruct tc as [C I] eqn:TC. simpl in *. 
    assert (sb^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ sb^? ⨾ ⦗C⦘) as COV_SB'.
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
    {
      rewrite <- !set_union_strict.
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
      rewrite ct_end, seqA. unfold "ar" at 2. 
      rewrite !seq_union_l.
      arewrite (sc ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw)⦘ ⊆ ∅₂).
      { rewrite (wf_scD WFSC), (wf_rmwD WF). type_solver. }
      arewrite (rfe ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw)⦘ ⊆ ∅₂).
      { rewrite wf_rfeD, wf_rmwD; auto. type_solver. }
      rewrite !union_false_l.
      
      rewrite ar_int_in_sb; auto.
      arewrite (ppo ∩ same_loc ⊆ sb) at 2 by (generalize ppo_in_sb; basic_solver).
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
      rewrite <- seqA with (r1 := sb). seq_rewrite sb_invrmw_sbclos; auto.
      rewrite COV_SB'. do 2 rewrite <- seqA. do 2 rewrite dom_seq.
      rewrite seqA. rewrite <- dom_rel_eqv_dom_rel. rewrite tc_rf_C.
      generalize tc_I_ar_rf_ppo_loc_I. basic_solver 10.  
    }
  Qed. 
        

  
  Lemma tcu_same_equiv (tc1 tc2 tc1' tc2': trav_config)
        (SAME1: same_trav_config tc1 tc1') (SAME2: same_trav_config tc2 tc2'):
    tc1 ⊔ tc2 = tc1' ⊔ tc2'.
  Proof.
    red in SAME1, SAME2. destruct tc1, tc2, tc1', tc2'. desc. simpl in *.
    apply trav_config_eq_helper; simpl; apply set_equiv_union; auto.
  Qed.

  Definition empty_tc := mkTC ∅ ∅.

  Lemma tcu_empty_l (tc: trav_config):
    tc ⊔ empty_tc = tc.
  Proof.
    unfold trav_config_union. apply trav_config_eq_helper; simpl; basic_solver.
  Qed.

  Lemma functional_codom {A: Type} (r: relation A) (a: A)
        (FUN: functional r)
        (DOMa: dom_rel r a):
    exists a', codom_rel (⦗eq a⦘ ⨾ r) ≡₁ eq a'.
  Proof.
    destruct DOMa as [a' Raa']. exists a'. split; [| basic_solver].  
    intros x [a_ Ra_x%seq_eqv_l]. desc. subst.
    eapply FUN; eauto.
  Qed.

  Lemma ext_r_helper WF tc r
        (Rr: is_r lab r) (COH: tc_coherent G sc tc):
    set_disjoint (eq r)
                 ((issued tc ∩₁ (is_rel lab) ∪₁
                          codom_rel (⦗covered tc⦘ ⨾ rmw)) \₁ covered tc).
  Proof.
    rewrite set_minus_union_l. apply set_disjoint_union_r. split. 
    { rewrite issuedW; eauto. type_solver. }
    rewrite wf_rmwD; eauto. type_solver.
  Qed.

  Lemma set_eq_helper {A: Type} (s1 s2: A -> Prop) (EQ: s1 = s2):
    s1 ≡₁ s2.
  Proof. by rewrite EQ. Qed.

  Lemma set_minus_disjoint {A: Type} (s1 s2: A -> Prop)
        (DISJ: set_disjoint s1 s2):
    s1 \₁ s2 ≡₁ s1.
  Proof. basic_solver. Qed.


  (* TODO: move upper *)
  Lemma itrav_step_mon_ext_equiv (e: actid)
        (C1 I1 C2 I2 C' I' Cu1 Iu1 Cu2 Iu2: actid -> Prop)
        (STEP: itrav_step G sc e {| covered := C1; issued := I1 |}
                          {| covered := C2; issued := I2 |})
        (EQC1: Cu1 ≡₁ C1 ∪₁ C') (EQI1: Iu1 ≡₁ I1 ∪₁ I')
        (EQC2: Cu2 ≡₁ C2 ∪₁ C') (EQI2: Iu2 ≡₁ I2 ∪₁ I'):
    (itrav_step G sc e)^? (mkTC Cu1 Iu1) (mkTC Cu2 Iu2).
  Proof.
    forward eapply itrav_step_mon_ext with (C' := C') (I' := I') as STEP'; eauto.
    destruct STEP'.
    { left. inversion H. apply trav_config_eq_helper'; simpl.
      { rewrite EQC1, EQC2. rewrite H1. basic_solver. }
      rewrite EQI1, EQI2. rewrite H2. basic_solver. }
    right. eapply itrav_step_more; [done| .. | by apply H].
    all: red; split; simpl; auto.
  Qed. 

  Add Parametric Morphism thread: (isim_trav_step G sc thread)^? with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_refl_more.
  Proof. ins. apply same_tc_extensionality in H, H0. by subst. Qed.
    
  Add Parametric Morphism thread: (isim_trav_step G sc thread)^* with signature
      same_trav_config ==> same_trav_config ==> iff as isim_trav_step_refl_trans_more.
  Proof. ins. apply same_tc_extensionality in H, H0. by subst. Qed.

  Lemma itrav_step_mon_ext_cover e
        (C I C' I': actid -> Prop)
        (STEP: (itrav_step G sc) e (mkTC C I) (mkTC (C ∪₁ eq e) I))
        (NEW: set_disjoint (C ∪₁ C') (eq e)):
          (itrav_step G sc e)
                             (mkTC (C ∪₁ C') (I ∪₁ I'))
                             (mkTC (C ∪₁ C' ∪₁ eq e) (I ∪₁ I')).
  Proof.
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
  Proof.
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
  Proof.
    pose proof (set_disjoint_eq_r a s) as EQ. apply not_iff_compat in EQ. tauto.
  Qed.

  Section CoverClosure.
    Variables (C I: actid -> Prop).
    Variable (e: actid).
    Let tc := {| covered := C; issued := I |}.
    Let tc' := {| covered := C ∪₁ eq e; issued := I |}.
    Let stc := sim_trav_closure tc.
    Let stc' := sim_trav_closure tc'. 
      
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
    Proof.
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
          rewrite stc_alt; auto.
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
        
        (* TODO: introduce them back here? *)
        intros STC STC'. 
        (* TODO: explain why we bother with premises in goal somewhere *)
        
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
        { basic_solver. }
      }
      
      destruct (classic (I w)) as [Iw | NIw].
      { apply rtE. left. red. split; auto.
        apply trav_config_eq_helper; simpl; [basic_solver| ].
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
      { (* TODO: can it be simplified? *)
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
          { specialize (DC_SBw x). specialize_full DC_SBw.
            { exists w. basic_solver. }
            destruct DC_SBw as [| ->]; [repeat left; basic_solver| ].
            type_solver. }
        }
        
        simpl. red. 
        forward eapply ar_rf_ppo_loc_ct_I_in_I as AR_CLOS_INCL.
        { eapply stc_coherent; auto. apply COH'. }
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
        generalize DOMe. basic_solver 10. }
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
    Proof. 
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
           apply trav_config_eq_helper; simpl; [| basic_solver].
           rewrite set_unionA. apply set_equiv_union; [basic_solver| ].
           rewrite <- (set_minus_disjoint (eq w) C) at 1; [| basic_solver]. 
           rewrite <- set_minus_union_l. apply set_equiv_minus; [| basic_solver].
           rewrite <- set_union_strict.
           (* apply set_disjoint_not_eq_r in OLDw. *)
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
    Proof.
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
        |} (sim_trav_closure tc) ->
      same_trav_config {|
          covered :=
            C ∪₁ eq e
              ∪₁ (I ∩₁ (fun a : actid => is_rel lab a)
                    ∪₁ codom_rel (⦗C ∪₁ eq e⦘ ⨾ rmw)) \₁ (C ∪₁ eq e);
          issued := I ∪₁ codom_rel (⦗C ∪₁ eq e⦘ ⨾ rmw) \₁ I
        |} (sim_trav_closure tc') ->
      (isim_trav_step G sc (tid e))＊ (sim_trav_closure tc) (sim_trav_closure tc').
    Proof.
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

  Add Parametric Morphism: sim_trav_closure with signature
      same_trav_config ==> same_trav_config as stc_more. 
  Proof.
    ins. destruct x as [C1 I1], y as [C2 I2]. destruct H. simpl in *.
    rewrite !H, !H0. reflexivity. 
  Qed. 

  Section IssueClosure.
    Variables (C I: actid -> Prop).
    Variable (e: actid).
    Let tc := {| covered := C; issued := I |}.
    Let tc' := {| covered := C; issued := I ∪₁ eq e|}.
    Let stc := sim_trav_closure tc.
    Let stc' := sim_trav_closure tc'. 
      
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
        |} (sim_trav_closure tc) ->
      same_trav_config {|
          covered :=
            C
              ∪₁ ((I ∪₁ eq e) ∩₁ (fun a : actid => is_rel lab a)
                    ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C;
          issued := I ∪₁ eq e ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ (I ∪₁ eq e)
        |} (sim_trav_closure tc') ->
      (isim_trav_step G sc (tid e))＊ (sim_trav_closure tc) (sim_trav_closure tc').
    Proof.
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
    (sim_trav_step G sc)^* (sim_trav_closure tc) (sim_trav_closure tc').
  Proof.    
    red in TRAV_STEP. desc. 
    enough ((isim_trav_step G sc (tid e))^* (sim_trav_closure tc) (sim_trav_closure tc')) as ISIM.
    { apply rtE in ISIM as [[-> _] | ?]; [apply rt_refl| ]. 
      apply rtE. right. induction H.
      { apply ct_step. red. eauto. }
      eapply transitive_ct; eauto. }

    remember (sim_trav_closure tc) as stc. remember (sim_trav_closure tc')as stc'.
    forward eapply same_tc_Reflexive with (x := stc) as STC.
    forward eapply same_tc_Reflexive with (x := stc') as STC'.
    
    rewrite Heqstc in STC at 1. rewrite Heqstc' in STC' at 1.
    destruct tc as [C I] eqn:TC, tc' as [C' I'] eqn:TC'.
    rewrite <- TC in Heqstc. rewrite <- TC' in Heqstc'. 
    rewrite stc_alt in STC, STC'; auto. 
    unfold trav_config_union, Cclos, Iclos in STC, STC'. simpl in *.
    
    cdes TRAV_STEP. revert Heqstc Heqstc' TC TC'. desf; simpl in *; ins. 
    { (* TODO: get rid of unused remembers *)
      subst stc stc' tc tc'. rewrite COVEQ, ISSEQ. 
      apply trav_step_closures_isim_cover; auto.
      { by rewrite <- COVEQ, <- ISSEQ. }
      { rewrite <- COVEQ. rewrite <- ISSEQ at 2. auto. }
      rewrite <- !COVEQ, <- !ISSEQ. by rewrite STC'. }
    { subst stc stc' tc tc'. rewrite COVEQ, ISSEQ.
      apply trav_step_closures_isim_issue; auto.
      { by rewrite <- COVEQ, <- ISSEQ. }
      { rewrite <- COVEQ at 2. rewrite <- ISSEQ. auto. }
      rewrite <- !COVEQ, <- !ISSEQ. by rewrite <- STC'.       
    }
  Qed. 
             

    
  Section Traversal.
    Variable (steps: nat -> t).
    Hypothesis (ENUM: enumerates steps graph_steps).
    Hypothesis (RESP: respects_rel steps iord⁺ graph_steps).
    
    Definition tc_enum (i: nat): trav_config :=
      sim_trav_closure (set2trav_config (trav_prefix steps i)).

    Lemma sim_traversal_next WF COMP WFSC CONS MF:
      forall i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)),
        (sim_trav_step G sc)^* (tc_enum i) (tc_enum (1 + i)).
    Proof.
      ins.
      unfold tc_enum. apply trav_step_closures_isim; auto.
      1, 2: apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. 
      { apply NOmega.lt_le_incl, DOMi. }
      apply trav_prefix_step; auto. 
    Qed. 
          
  End Traversal.

  (* TODO: move upper *)
  Lemma stc_domE WF COMP WFSC CONS MF
        tc (DOMC: covered tc ⊆₁ E) (DOMI: issued tc ⊆₁ E)
        (COH: tc_coherent G sc tc):
    covered (sim_trav_closure tc) ⊆₁ E /\ issued (sim_trav_closure tc) ⊆₁ E.
  Proof.
    rewrite stc_alt; auto. 
    destruct tc. simpl in *.
    unfold Cclos, Iclos. simpl.
    rewrite wf_rmwE; auto. basic_solver.
  Qed.  


  Lemma sim_traversal_inf WF COMP WFSC CONS MF
        (IMM_FAIR: fsupp ar⁺):
    exists (sim_enum: nat -> trav_config),
      ⟪DOM_TC: forall i (DOMi: NOmega.le (NOnum i) (set_size graph_steps)),
          covered (sim_enum i) ⊆₁ E /\ issued (sim_enum i) ⊆₁ E ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size graph_steps)),
          tc_coherent G sc (sim_enum i) ⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)),
          (sim_trav_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
      ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i, covered (sim_enum i) e⟫.
  Proof.
    destruct iord_enum_exists as [steps_enum [ENUM RESP]]; auto.
    exists (tc_enum steps_enum). splits.
    3: { apply sim_traversal_next; auto. }
    2: { ins. unfold tc_enum. apply stc_coherent; auto.
         apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. }
    { intros i DOM. unfold tc_enum. apply stc_domE; auto.
      1, 2: unfold set2trav_config; simpl; basic_solver.
      apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. }
    intros e Ee.
    pose proof ENUM as ENUM'. apply enumeratesE' in ENUM. desc.
    specialize (IND (mkTL TravAction.cover e)). specialize_full IND; [by vauto| ].
    desc. exists (S i).
    unfold tc_enum. rewrite stc_alt; auto.
    2: { apply tc_coherent_alt_implies_tc_coherent, trav_prefix_coherent_alt; auto. }
    unfold trav_config_union. simpl. left. split; [| by apply Ee].
    left. split; [| by apply Ee].
    exists (mkTL TravAction.cover e). split; auto. split; [by vauto| ].
    rewrite <- IND0. apply trav_prefix_ext; auto. basic_solver. 
  Qed. 


End SimTravClosure.   
