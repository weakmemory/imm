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
(* Require Import ExtSimTraversal. *)
(* Require Import ExtSimTraversalProperties. *)

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
    issued tc ∩₁ (is_rel lab) ∪₁ codom_rel (⦗covered tc ∪₁ issued tc ∩₁ is_rel lab⦘ ⨾ rmw).
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

  Lemma stc_alt WF WFSC
        (tc: trav_config) (COH: tc_coherent G sc tc):
    sim_trav_closure tc = tc ⊔ (mkTC (Cclos tc) (Iclos tc)). 
  Proof.
    forward eapply tc_coherent_implies_tc_coherent_alt as COH'; eauto. 
    unfold sim_trav_closure, Iclos, Cclos. destruct tc as [C I]. simpl.
    unfold trav_config_union. simpl. 
    apply trav_config_eq_helper; simpl.
    { basic_solver 10. }
    rewrite !set_inter_union_l.
    rewrite <- !set_unionA. apply set_equiv_union.
    { split; [| basic_solver].
      forward eapply tc_W_C_in_I as CI; eauto.         
      simpl in CI. rewrite CI. basic_solver. }
    rewrite id_union, !seq_union_l. rewrite codom_union, set_inter_union_l.  
    split.
    2: { rewrite wf_rmwD at 1; auto.
         apply set_subset_union_r. left. basic_solver. }
    apply set_subset_union_l. split; [basic_solver| ].
    etransitivity; [| apply set_subset_empty_l].
    forward eapply codom_I_rmw_empty as IW; eauto. simpl in IW.
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
      { eapply traversal_mon; [| | apply COV]; simpl; basic_solver. }
      all: (rewrite COVEQ || rewrite ISSEQ); basic_solver. }

    destruct (classic (I' e)).
    { left. f_equal; apply set_extensionality;
              (rewrite COVEQ || rewrite ISSEQ); basic_solver. }
    right. red. right. splits; simpl. 
    { intros [? | ?]; done. }
    { eapply traversal_mon; [| | apply ISS]; simpl; basic_solver. }
    all: (rewrite COVEQ || rewrite ISSEQ); basic_solver.
  Qed.

  Lemma isim_trav_step_more (tc1 tc2 tc1' tc2': trav_config) (thread: thread_id)
        (EQUIV1: same_trav_config tc1 tc1') (EQUIV2: same_trav_config tc2 tc2')
        (STEP: isim_trav_step G sc thread tc1 tc2):
    isim_trav_step G sc thread tc1' tc2'.
  Proof.
    replace tc1' with tc1; [replace tc2' with tc2| ]; auto.
    all: destruct EQUIV1, EQUIV2; apply trav_config_eq_helper; auto.
  Qed. 

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
    
  Lemma stc_coherent (tc: trav_config) WF WFSC
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
    { admit. }
    { rewrite id_union, seq_union_r, dom_union.
      apply set_subset_union_l. split; [generalize tc_sb_C; basic_solver 10 | ].
      unfold Cclos. simpl. rewrite id_union, seq_union_r, dom_union.
      apply set_subset_union_l. split.
      { apply set_subset_union_r. left.
        replace C with (covered tc); [| by rewrite TC].
        etransitivity.
        2: { eapply dom_sb_W_rel_issued; eauto. rewrite TC. apply COH. }
        rewrite TC. simpl. rewrite <- id_inter. apply dom_rel_mori. basic_solver. }
      rewrite id_union, seq_union_l, codom_union.
      rewrite id_union, seq_union_r, dom_union. 
      rewrite CIR, eqv_empty, seq_false_r, dom_empty, set_union_empty_r. 
      rewrite dom_rel_eqv_codom_rel. rewrite transp_seq, transp_eqv_rel. 
      rewrite <- seqA, sb_invrmw_sbclos; auto.
      rewrite COV_SB'. basic_solver. }
    { rewrite set_inter_union_l. rewrite tc_W_C_in_I.
      unfold Cclos, Iclos. simpl.
      rewrite id_union, seq_union_l, codom_union, CIR.
      basic_solver. }
    { rewrite id_union, seq_union_r, dom_union, tc_rf_C.
      unfold Cclos, Iclos. simpl.
      rewrite !id_union, !seq_union_l, codom_union, CIR.
      rewrite tc_I_in_W at 2. 
      rewrite set_union_empty_r. rewrite wf_rmwD; auto.
      do 3 rewrite codom_seq at 1. rewrite codom_eqv.
      rewrite <- id_union. rewrite wf_rfD; auto. type_solver. }
    { rewrite id_union, seq_union_r, dom_union, tc_sc_C.
      unfold Cclos. simpl.
      rewrite !id_union, !seq_union_l, codom_union, CIR, set_union_empty_r.
      rewrite seq_union_r, dom_union. repeat (apply set_subset_union_l; split).
      { basic_solver. }
      { erewrite (wf_scD WFSC). rewrite tc_I_in_W at 1.
        type_solver. }
      erewrite (wf_scD WFSC). rewrite wf_rmwD at 1; auto.
      do 3 rewrite codom_seq at 1. rewrite codom_eqv. type_solver. }
    { admit. }
    { admit. }
    { rewrite !id_union, seq_union_r, dom_union, tc_fwbob_I.
      unfold Iclos, Cclos. simpl.
      rewrite fwbob_in_sb.
      rewrite dom_rel_eqv_codom_rel. rewrite transp_seq, transp_eqv_rel.
      rewrite <- seqA. rewrite sb_invrmw_sbclos; auto.
      rewrite COV_SB'. basic_solver. }
    { rewrite id_union, !seq_union_r, dom_union, tc_I_ar_rf_ppo_loc_I.
      unfold Iclos. simpl.
      unfold "ar". rewrite ct_end, seqA.
      rewrite !seq_union_l.
      arewrite (sc ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw)⦘ ⊆ ∅₂).
      { rewrite (wf_scD WFSC), (wf_rmwD WF). type_solver. }
      arewrite (rfe ⨾ ⦗codom_rel (⦗C⦘ ⨾ rmw)⦘ ⊆ ∅₂).
      { rewrite wf_rfeD, wf_rmwD; auto. type_solver. }
      rewrite ar_int_in_sb; auto.
      arewrite (ppo ∩ same_loc ⊆ sb) at 2 by (generalize ppo_in_sb; basic_solver).
      rewrite !union_false_l. rewrite !seq_union_r. rewrite dom_union.
      repeat (apply set_subset_union_l; split).
      { basic_solver. }
      { rewrite <- !seqA. rewrite dom_rel_eqv_codom_rel.
        rewrite transp_seq, transp_eqv_rel.
        rewrite !seqA. rewrite <- seqA with (r3 := ⦗C⦘).
        seq_rewrite sb_invrmw_sbclos; auto. 
        rewrite COV_SB'. do 2 rewrite <- seqA. rewrite dom_seq.
        rewrite rtE. rewrite seq_union_r, seq_union_l, dom_union.
        apply set_subset_union_l. split.
        { rewrite <- tc_W_C_in_I. basic_solver. }
        (* TODO: need to restrict C to writes *)
        admit. }
      admit. }
  Admitted. 
        
  Lemma isim_trav_step_mon thread
        (C1 I1 C2 I2 C' I': actid -> Prop)
        (STEP: isim_trav_step G sc thread (mkTC C1 I1) (mkTC C2 I2))
        (* (MON_C: C1 ⊆₁ C1') (MON_I: C1 ⊆₁ C1') *)
        :
    (isim_trav_step G sc thread)^? (mkTC (C1 ∪₁ C') (I1 ∪₁ I'))
                   (mkTC (C2 ∪₁ C') (I2 ∪₁ I')).
  Proof.
    (* TODO: refactor *)
    inversion STEP; subst; simpl in *. 
    { destruct (classic ((C1 ∪₁ C') f)).
      { left. apply trav_config_eq_helper; simpl; basic_solver. }
      right.
      assert (C1 ∪₁ eq f ∪₁ C' ≡₁ C1 ∪₁ C' ∪₁ eq f) as C_ALT by basic_solver. 
      erewrite trav_config_eq_helper'; [| simpl; by apply C_ALT | reflexivity].
      simpl.
      apply fence_trav_step; auto. simpl.
      erewrite trav_config_eq_helper'; [| simpl; by rewrite <- C_ALT | reflexivity].
      simpl.
      eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?].
      2: { eapply itrav_step_more; [reflexivity| .. | apply H0].
           all: by apply same_tc_Symmetric. }
      inversion H0. destruct H. rewrite H2. basic_solver. }
    { destruct (classic ((C1 ∪₁ C') r)).
      { left. apply trav_config_eq_helper; simpl; basic_solver. }
      right.
      assert (C1 ∪₁ eq r ∪₁ C' ≡₁ C1 ∪₁ C' ∪₁ eq r) as C_ALT by basic_solver. 
      erewrite trav_config_eq_helper'; [| simpl; by apply C_ALT | reflexivity].
      simpl.
      apply read_trav_step; auto. simpl.
      erewrite trav_config_eq_helper'; [| simpl; by rewrite <- C_ALT | reflexivity].
      simpl.
      eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?].
      2: { eapply itrav_step_more; [reflexivity| .. | apply H0].
           all: by apply same_tc_Symmetric. }
      inversion H0. destruct H. rewrite H2. basic_solver. }
    { destruct (classic ((I1 ∪₁ I') w)).
      { left. apply trav_config_eq_helper; simpl; basic_solver. }
      right.
      assert (I1 ∪₁ eq w ∪₁ I' ≡₁ I1 ∪₁ I' ∪₁ eq w) as I_ALT by basic_solver. 
      erewrite trav_config_eq_helper'; [| reflexivity| simpl; by apply I_ALT].
      simpl.
      apply rlx_write_promise_step; auto. simpl.
      erewrite trav_config_eq_helper'; [| reflexivity| simpl; by rewrite <- I_ALT].
      simpl.
      eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?].
      2: { eapply itrav_step_more; [reflexivity| .. | apply H0].
           all: by apply same_tc_Symmetric. }
      inversion H0. destruct H. rewrite H2. basic_solver. }
    { rename I2 into I1. 
      destruct (classic ((C1 ∪₁ C') w)).
      { left. apply trav_config_eq_helper; simpl; basic_solver. }
      right.
      assert (C1 ∪₁ eq w ∪₁ C' ≡₁ C1 ∪₁ C' ∪₁ eq w) as C_ALT by basic_solver. 
      erewrite trav_config_eq_helper'; [| simpl; by apply C_ALT | reflexivity].
      simpl.
      apply rlx_write_cover_step; auto.
      { simpl. red. tauto. } 
      erewrite trav_config_eq_helper'; [| simpl; by rewrite <- C_ALT | reflexivity].
      simpl.
      eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?].
      2: { eapply itrav_step_more; [reflexivity| .. | apply H0].
           all: by apply same_tc_Symmetric. }
      inversion H0. destruct H. rewrite H2. basic_solver. }
    { assert (~ C1 w) as NC1w.
      { inversion TS2; red in H; desc; simpl in *; auto.
        destruct NISS0. basic_solver. }
      destruct (classic (C' w)) as [C'w | NC'w], (classic (I' w)) as [I'w | NI'w].
      { left. apply trav_config_eq_helper; simpl; basic_solver. }
      2: { 
        (* TODO: so far it doesn't seem true *)
  Admitted.

  Lemma isim_trav_step_mon_tcu thread
        (tc1 tc2 tc': trav_config)
        (STEP: isim_trav_step G sc thread tc1 tc2):
    (isim_trav_step G sc thread)^? (tc1 ⊔ tc') (tc2 ⊔ tc').
  Proof. 
    destruct tc1, tc2, tc'. apply isim_trav_step_mon; auto. 
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

  Lemma trav_step_closures_isim WF WFSC CONS
        (tc tc': trav_config)
        (COH: tc_coherent G sc tc)
        (COH': tc_coherent G sc tc')
        (TRAV_STEP: trav_step G sc tc tc'):
    (sim_trav_step G sc)^? (sim_trav_closure tc) (sim_trav_closure tc').
  Proof.
    assert (forall tc C1 I1 C2 I2
              (COV: covered tc ≡₁ C1 ∪₁ C2)
              (ISS: issued tc ≡₁ I1 ∪₁ I2),
               tc = (mkTC C1 I1) ⊔ (mkTC C2 I2)) as TCU_HELPER.
    { ins. unfold trav_config_union. apply trav_config_eq_helper; simpl; auto. }
    (* cdes TRAV_STEP. *)
    
    red in TRAV_STEP. desc. 
    enough ((isim_trav_step G sc (tid e))^? (sim_trav_closure tc) (sim_trav_closure tc')) as ISIM.
    { destruct ISIM; [basic_solver| ]. right. by exists (tid e). }
    cdes TRAV_STEP. desf. 
    
    desf.
    { pose proof (lab_rwf lab e) as LABe. des.
      { remember (mkTC (eq e) ∅) as tc''. 

        assert (tc' = tc ⊔ tc'') as TC'_UNION.
        { subst tc''. apply trav_config_eq_helper; simpl; auto.
          generalize ISSEQ. basic_solver. }
        
        assert (sim_trav_closure tc'' =
                mkTC (eq e ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw))
                     (codom_rel (⦗eq e⦘ ⨾ rmw))) as TC''.
        { apply trav_config_eq_helper; subst tc''; simpl.
          { by rewrite !set_inter_empty_l, !set_union_empty_r. }
          rewrite !set_inter_empty_l, !set_union_empty_r, !set_union_empty_l.
          rewrite set_inter_union_l. erewrite set_equiv_union.
          3: { apply set_inter_absorb_r.
               rewrite wf_rmwD; auto; basic_solver. }
          2: { apply set_subset_empty_r. type_solver. }
          basic_solver. }

        forward eapply eq_trans as TC''_UNION; [apply TC''| | ]. 
        { eapply TCU_HELPER; simpl; [reflexivity| ]. 
          symmetry. apply set_union_empty_l. }

        rewrite TC'_UNION, stc_tcu_distribute.
        rewrite TC''_UNION.
        
        destruct (classic (dom_rel rmw e)) as [RMWr | NRMWr].
        2: { assert (codom_rel (⦗eq e⦘ ⨾ rmw) ≡₁ ∅) as NOADD.
             { generalize NRMWr. basic_solver. } 
             
             (* TODO: declare instances for same_trav_config *)
             rewrite <- tcu_assoc. erewrite tcu_same_equiv with (tc2' := empty_tc).
             2: { by apply same_tc_Symmetric. }
             2: { split; auto. }   
             rewrite tcu_empty_l. rewrite <- Heqtc''. 
             rewrite !stc_alt; auto. 
             rewrite tcu_assoc, tcu_symm with (tc2 := tc''), <- tcu_assoc.
             apply isim_trav_step_mon_tcu; auto. 
             subst tc''. destruct tc as [C I], tc' as [C' I']. simpl in *.
             unfold trav_config_union. simpl.
             erewrite trav_config_eq_helper'; cycle 1. 
             { simpl. reflexivity. }
             { simpl. apply set_union_empty_r. }
             eapply read_trav_step; auto. simpl.
             eapply itrav_step_more; eauto; [done| ].
             red. split; simpl; symmetry; auto. }

        rename e into r.
        forward eapply (functional_codom rmw r) as [w RMWD]; auto using wf_rmwf.
        pose proof (proj2 RMWD) as RMW. red in RMW. specialize (RMW w eq_refl).
        red in RMW. desc. apply seq_eqv_l in RMW as [<- RMW].          

        assert (E w /\ W w) as [Ew Ww].
        { eapply same_relation_exp in RMW.
          2: { rewrite wf_rmwD, wf_rmwE; auto. }
          unfolder in RMW. desc. subst. auto. } 
        (* TODO: get rid of previous excessive split of tc'' *)
        erewrite <- TCU_HELPER with (tc := sim_trav_closure tc''); cycle 1.
        1,2: rewrite TC''; simpl; basic_solver.
        rewrite TC''.
        rewrite !stc_alt.

        destruct (classic (is_rel lab w)) as [RELw | NRELw].
        { rewrite <- TC''. 
          rewrite tcu_assoc, tcu_symm with (tc2 := sim_trav_closure tc''), <- tcu_assoc.
          apply isim_trav_step_mon_tcu.
          rewrite TC''. 
          destruct tc as [C I] eqn:TC, tc' as [C' I'] eqn:TC'. simpl in *.
          unfold trav_config_union. simpl. 
          eapply isim_trav_step_more; [apply same_tc_Reflexive| ..]. 
          { erewrite trav_config_eq_helper'; [apply same_tc_Reflexive| ..]; simpl.
            { rewrite RMWD, <- set_unionA. reflexivity. }
            rewrite RMWD. reflexivity. }
          assert (~ I w) as NIw. 
          { intros ISSw. cdes COH. apply II in ISSw.
            red in ISSw. apply proj1, proj2 in ISSw.
            red in ISSw. specialize (ISSw r). specialize_full ISSw; [| done]. 
            apply dom_rel_fun_alt. red. repeat left.
            apply seq_eqv_r. unfolder; splits; auto.
            by apply rmw_in_sb. }
          assert (~ C w) as NCw.
          { intros Cw. destruct NIw.
            forward eapply (w_covered_issued COH (conj Ww Cw)). auto. }

          assert (dom_cond sb (C ∪₁ eq r) w) as DC_SBw. 
          { unfolder. ins. desc. subst z y.
            destruct (classic (x = r)) as [-> | ]; [tauto| ]. left.
            apply wf_rmwi in RMW as [SBrw IMMrw]; auto.
            assert ((sb ⨾ ⦗covered tc'⦘) x r) as SBxr.
            { apply seq_eqv_r. split.
              2: { subst. simpl. apply COVEQ. basic_solver. } 
              eapply sb_semi_total_r in SBrw; eauto.
              2: { eapply read_or_fence_is_not_init; eauto. }
              des; auto. edestruct IMMrw; eauto. }
            forward eapply (@dom_sb_covered G) with (T := tc') as SB_COV; eauto.
            { eapply tc_coherent_more; [| by apply COH'].
              subst tc'. red. simpl. by rewrite COVEQ, ISSEQ. } 
            specialize (SB_COV x). specialize_full SB_COV; [by vauto| ]. 
            rewrite TC' in SB_COV. apply COVEQ in SB_COV.
            destruct SB_COV; vauto. }
          
          econstructor; auto; simpl. 
          { econstructor; eauto. }
          { red. right. red. splits; simpl; auto.
            apply issuable_next_w; auto.
            { eapply tc_coherent_more; [| by apply COH'].
              red. simpl. by rewrite COVEQ, ISSEQ. } 
            split; auto. 
            simpl. red. unfolder. splits; auto.
            apply and_not_or. split; auto. intros ->. type_solver. }
          red. left. red. splits.
          3, 4: basic_solver. 
          { simpl. apply and_not_or. split; auto. intros ->. type_solver. }
          red. split.
          { split; auto. }
          repeat left. split; auto. basic_solver. }
        
        
  Admitted. 
             

    
  Section Traversal.
    Variable (steps: nat -> t).
    Hypothesis (ENUM: enumerates steps graph_steps).
    Hypothesis (RESP: respects_rel steps iord⁺ graph_steps).
    
    Definition tc_enum (i: nat) :=
      sim_trav_closure (set2trav_config (trav_prefix steps i)).


    Lemma sim_traversal WF COMP WFSC CONS MF:
      forall i (DOMi: NOmega.lt_nat_l (S i) (set_size graph_steps)),
        (sim_trav_step G sc)^? (tc_enum i) (tc_enum (1 + i)).
    Proof.
      ins. 
      forward eapply itrav_prefix_step as STEP; eauto.
      forward eapply trav_prefix_extend as PREF'; eauto.
      destruct (steps i) as [a e] eqn:STEPi. simpl in *.
      unfold tc_enum. rewrite PREF'. clear PREF'.

      destruct a.
      { destruct (classic (

      
      pose proof (lab_rwf lab e) as LABe. des.
      3: {
        right.
        exists (tid e).

    
    Lemma sim_traversal WF COMP WFSC CONS MF:
      forall i (DOMi: NOmega.lt_nat_l (S i) (set_size graph_steps)),
        (sim_trav_step G sc)^? (tc_enum i) (tc_enum (1 + i)).
    Proof. 
      ins. unfold tc_enum.
      forward eapply trav_prefix_extend as PREF'; eauto.
      destruct (steps i) as [a e] eqn:STEPi.
      rewrite PREF'. clear PREF'.

      (* remember (if a then eq e else ∅) as Cp. remember (if a then ∅ else eq e) as Ip. *)
      remember ({|
            covered := if a then eq e else ∅; issued := if a then ∅ else eq e
          |}) as TCp. 

      rewrite stc_tcu_distribute.
      remember (set2trav_config (trav_prefix steps i)) as tc.

      apply sim_trav_step_closure.
      forward eapply trav_prefix_step as STEP; eauto.
      red in STEP. destruct STEP as [e' STEP]. 
      right. red. 

      rewrite !stc_alt.
      remember ({| covered := Cclos tc; issued := Iclos tc |}) as TCclos.
      remember ({| covered := Cclos TCp; issued := Iclos TCp |}) as TCclos_p.

      (* rewrite tcu_assoc. rewrite tcu_symm with (tc1 := TCclos). *)
      (* rewrite tcu_assoc. rewrite <- tcu_assoc with (tc2 := TCp). *)
      (* rewrite tcu_symm with (tc1 := TCclos_p).  *)

      apply sim_trav_step_closure. 
      
      
      
  End Traversal. 


End SimTravClosure.   
