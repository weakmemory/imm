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
    (covered tc ∪₁ Cclos tc) ∩₁ W. 

  Lemma stc_alt_unfolded (tc: trav_config):
    let (C, I) := tc in
    let C' := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ is_rel lab⦘ ⨾ rmw) in
    let I' := (C ∪₁ I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C ∪₁ I ∩₁ (is_rel lab)⦘ ⨾ rmw)) ∩₁ W in
    sim_trav_closure tc = trav_conf_union tc (mkTC C' I'). 
  Proof.
    unfold sim_trav_closure. destruct tc as [C I]. simpl.
    apply trav_config_eq_helper; simpl; basic_solver 10.
  Qed.     

  Lemma stc_alt (tc: trav_config):
    sim_trav_closure tc = trav_conf_union tc (mkTC (Cclos tc) (Iclos tc)). 
  Proof.
    unfold sim_trav_closure, Iclos, Cclos. destruct tc as [C I]. simpl.
    apply trav_config_eq_helper; simpl; basic_solver 10. 
  Qed.

  Lemma stc_tcu_distribute (tc1 tc2: trav_config):
    sim_trav_closure (trav_conf_union tc1 tc2) =
    trav_conf_union (sim_trav_closure tc1) (sim_trav_closure tc2).
  Proof. 
    unfold sim_trav_closure, trav_conf_union.
    destruct tc1 as [C1 I1], tc2 as [C2 I2]. simpl.
    apply trav_config_eq_helper; simpl; basic_solver 10. 
  Qed.

  Lemma tcu_assoc (tc1 tc2 tc3: trav_config):
    trav_conf_union (trav_conf_union tc1 tc2) tc3 =
    trav_conf_union tc1 (trav_conf_union tc2 tc3).
  Proof.
    destruct tc1, tc2, tc3. unfold trav_conf_union.
    apply trav_config_eq_helper; simpl; basic_solver.
  Qed.

  Lemma tcu_symm (tc1 tc2: trav_config):
    trav_conf_union tc1 tc2 = 
    trav_conf_union tc2 tc1. 
  Proof.
    destruct tc1, tc2. unfold trav_conf_union.
    apply trav_config_eq_helper; simpl; basic_solver.
  Qed.

  (* Lemma sim_trav_step_closure (tc tc': trav_config) *)
  (*       (SIM_TRAV_STEP: (sim_trav_step G sc)^? tc (trav_conf_union tc tc')): *)
  (*   (sim_trav_step G sc)^? (sim_trav_closure tc) (trav_conf_union (sim_trav_closure tc) (sim_trav_closure tc')). *)
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

  Lemma itrav_step_eq (tc1 tc2 tc1' tc2': trav_config) (e: actid)
        (EQUIV1: same_trav_config tc1 tc1') (EQUIV2: same_trav_config tc2 tc2')
        (STEP: (itrav_step G sc) e tc1 tc2):
    (itrav_step G sc) e tc1' tc2'.
  Proof.
    red in EQUIV1, EQUIV2. desc.
    red in STEP. desf.
    { left. splits.
      { intros ?. destruct NEXT. by apply EQUIV1. }
      { eapply coverable_more; eauto. by apply same_tc_Symmetric. }
      { rewrite <- EQUIV2, <- EQUIV1. auto. }
      { rewrite <- EQUIV0, <- EQUIV3. auto. }
    }
    right. splits.
    { intros ?. destruct NISS. by apply EQUIV3. }
    { eapply issuable_more; eauto. by apply same_tc_Symmetric. }
    { rewrite <- EQUIV2, <- EQUIV1. auto. }
    { rewrite <- EQUIV0, <- EQUIV3. auto. }
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
    


  (* Lemma isim_trav_step_mon' thread *)
  (*       (C1 I1 C2 I2 C' I' C'' I'': actid -> Prop) *)
  (*       (STEP: isim_trav_step G sc thread (mkTC C1 I1) (mkTC C2 I2)) *)
  (*       (MON_C: C' ⊆₁ C'') (MON_I: I' ⊆₁ I'') *)
  (*       : *)
  (*   (isim_trav_step G sc thread)^? (mkTC (C1 ∪₁ C') (I1 ∪₁ I')) *)
  (*                  (mkTC (C2 ∪₁ C'') (I2 ∪₁ I'')). *)
  (* Proof. *)
  (*   inversion STEP; subst; simpl in *. *)
  (*   { destruct (classic ((C1 ∪₁ C') f)). *)
  (*     { left. apply trav_config_eq_helper; simpl. basic_solver. } *)
  (*     right. *)
  (*     assert (C1 ∪₁ eq f ∪₁ C' ≡₁ C1 ∪₁ C' ∪₁ eq f) as C_ALT by basic_solver. *)
  (*     erewrite trav_config_eq_helper'; [| simpl; by apply C_ALT | reflexivity]. *)
  (*     simpl. *)
  (*     apply fence_trav_step; auto. simpl. *)
  (*     erewrite trav_config_eq_helper'; [| simpl; by rewrite <- C_ALT | reflexivity]. *)
  (*     simpl. *)
  (*     eapply itrav_step_mon_ext with (C' := C') (I' := I') in TS as [? | ?]. *)
  (*     2: { eapply itrav_step_eq; [| | by apply H0]; basic_solver. } *)
  (*     inversion H0. destruct H. rewrite H2. basic_solver. } *)
  (* Admitted. *)
  
  Lemma isim_trav_step_mon thread
        (C1 I1 C2 I2 C' I': actid -> Prop)
        (* (C1 I1 C2 I2 C1' I1' C2' I2': actid -> Prop) *)
        (STEP: isim_trav_step G sc thread (mkTC C1 I1) (mkTC C2 I2))
        (* (MON_C: C1 ⊆₁ C1') (MON_I: C1 ⊆₁ C1') *)
        :
    (isim_trav_step G sc thread)^? (mkTC (C1 ∪₁ C') (I1 ∪₁ I'))
                   (mkTC (C2 ∪₁ C') (I2 ∪₁ I')).
  Proof. 
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
      2: { eapply itrav_step_eq; [| | by apply H0]; basic_solver. }
      inversion H0. destruct H. rewrite H2. basic_solver. }
  Admitted.

  Lemma isim_trav_step_mon_tcu thread
        (tc1 tc2 tc': trav_config)
        (STEP: isim_trav_step G sc thread tc1 tc2):
    (isim_trav_step G sc thread)^? (trav_conf_union tc1 tc') (trav_conf_union tc2 tc').
  Proof. 
    destruct tc1, tc2, tc'. apply isim_trav_step_mon; auto. 
  Qed.

  Lemma trav_step_closures_isim WF
        (tc tc': trav_config) 
        (TRAV_STEP: trav_step G sc tc tc'):
    (sim_trav_step G sc)^? (sim_trav_closure tc) (sim_trav_closure tc').
  Proof.
    assert (forall tc C1 I1 C2 I2
              (COV: covered tc ≡₁ C1 ∪₁ C2)
              (ISS: issued tc ≡₁ I1 ∪₁ I2),
               tc = trav_conf_union (mkTC C1 I1) (mkTC C2 I2)) as TCU_HELPER.
    { ins. unfold trav_conf_union. apply trav_config_eq_helper; simpl; auto. }
    red in TRAV_STEP. desc. red in TRAV_STEP. des.
    { pose proof (lab_rwf lab e) as LABe. des.
      { right. exists (tid e).

        (* destruct tc as [C I], tc' as [C' I']. simpl in *. *)
        remember (mkTC (eq e) ∅) as tc''. 
        assert (tc' = trav_conf_union tc tc'') as TC'_UNION.
        { subst tc''. apply trav_config_eq_helper; simpl; auto.
          generalize ISSEQ. basic_solver. }
        rewrite TC'_UNION, stc_tcu_distribute.
                
        assert (sim_trav_closure tc'' =
                mkTC (eq e ∪₁ codom_rel (⦗eq e⦘ ⨾ rmw))
                     (codom_rel (⦗eq e⦘ ⨾ rmw))) as TC''.
        { apply trav_config_eq_helper; subst tc''; simpl.
          { by rewrite !set_inter_empty_l, !set_union_empty_r. }
          { rewrite !set_inter_empty_l, !set_union_empty_r, !set_union_empty_l.
            rewrite set_inter_union_l. erewrite set_equiv_union.
            3: { apply set_inter_absorb_r.
                 rewrite wf_rmwD; auto; basic_solver. }
            2: { apply set_subset_empty_r. type_solver. }
            basic_solver. 
          }
        }

        rewrite TC''. rewrite !stc_alt. simpl.
        remember ({| covered := Cclos tc; issued := Iclos tc |}) as tcc.
        forward eapply eq_trans as TC''_UNION; [apply TC''| | ]. 
        { eapply TCU_HELPER; simpl; [reflexivity| ]. 
          symmetry. apply set_union_empty_l. }
        rewrite <- TC'', TC''_UNION. 
         
        


        rewrite !stc_alt.
        destruct tc as [C I], tc' as [C' I']. simpl in *.
        (* unfold trav_conf_union, Iclos, Cclos. *)
        unfold trav_conf_union. 
        erewrite trav_config_eq_helper'. 
        2: { simpl. rewrite COVEQ, ISSEQ. reflexivity. }
        2: { simpl. rewrite ISSEQ, COVEQ. reflexivity. }
        simpl. 

        unfold Iclos, Cclos. simpl. 
        fold Cclos. 
    
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
