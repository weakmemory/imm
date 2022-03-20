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
Require Import FairExecution.
Require Import TraversalOrder.
Require Import ImmFair.
Require Import AuxRel2.
Require Import SetSize.
Require Import IordTraversal.

Import ListNotations.
Set Implicit Arguments.

(* TODO: move the section somewhere *)
Section TravConfigUnion.

  Definition trav_config_union (tc1 tc2: trav_config) : trav_config :=
    mkTC (covered tc1 ∪₁ covered tc2) (issued tc1 ∪₁ issued tc2).

  Local Notation " tc1 '⊔' tc2 " := (trav_config_union tc1 tc2) (at level 10).

  Lemma tcu_same_equiv (tc1 tc2 tc1' tc2': trav_config)
        (SAME1: same_trav_config tc1 tc1') (SAME2: same_trav_config tc2 tc2'):
    tc1 ⊔ tc2 = tc1' ⊔ tc2'.
  Proof using.
    apply same_tc_extensionality.
    unfold trav_config_union. 
    destruct SAME1 as [-> ->], SAME2 as [-> ->]. reflexivity. 
  Qed.

  Lemma tcu_assoc (tc1 tc2 tc3: trav_config):
     (tc1 ⊔ tc2) ⊔ tc3 = tc1 ⊔ (tc2 ⊔ tc3).
  Proof using.
    apply same_tc_extensionality. 
    unfold trav_config_union. split; simpl; basic_solver. 
  Qed.

  Lemma tcu_symm (tc1 tc2: trav_config):
    tc1 ⊔ tc2 = tc2 ⊔ tc1. 
  Proof using.
    apply same_tc_extensionality. 
    unfold trav_config_union. split; simpl; basic_solver. 
  Qed.

End TravConfigUnion.   

Local Notation " tc1 '⊔' tc2 " := (trav_config_union tc1 tc2) (at level 10). 

Section Set2TravConfig. 
  (* TODO: have to repeat this? *)
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

  Notation "'iord'" := (iord G sc). 
  Notation "'SB'" := (SB G sc). 
  Notation "'RF'" := (RF G). 
  Notation "'AR'" := (AR G sc). 
  Notation "'FWBOB'" := (FWBOB G). 

  Definition set2trav_config (S: trav_label -> Prop) :=
    mkTC
      ((event ↑₁ (action ↓₁ (eq ta_cover) ∩₁ S) \₁ is_init ∪₁ is_init) ∩₁ E)
      ((event ↑₁ (action ↓₁ (eq ta_issue) ∩₁ S) ∩₁ W \₁ is_init ∪₁ is_init) ∩₁ E).

  Global Add Parametric Morphism: set2trav_config with signature
      (@set_equiv trav_label) ==> same_trav_config as set2trav_config_more. 
  Proof using.
    ins. unfold set2trav_config. split; rewrite H; simpl; basic_solver. 
  Qed.

  Lemma set2trav_config_empty:
    set2trav_config ∅ = init_trav G.
  Proof using.
    unfold set2trav_config. apply same_tc_extensionality. unfold init_trav.
    split; basic_solver. 
  Qed. 

(*Local lemma*)
 Lemma s2tc_closed_coherent_alt WF COMP WFSC CONS
        (S: trav_label -> Prop)
        (PREF_CLOS: dom_rel (iord⁺ ;; ⦗S⦘) ⊆₁ S):
    tc_coherent_alt G sc (set2trav_config S).
  Proof using.
    split; simpl. 
    { basic_solver. }
    { basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := sb) (D1 := fun _ => True) (D2 := fun _ => True)
             (a1 := ta_cover) (a2 := ta_cover) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { basic_solver. } 
      { rewrite no_sb_to_init. basic_solver. }
      { rewrite wf_sbE. basic_solver. }
      repeat apply inclusion_union_r1_search. unfold "SB".
      hahn_frame. apply map_rel_mori; [done| ]. by rewrite <- ct_step. }
    { unfolder. intros e De. desc. splits; auto. desf; auto. left. splits; auto.
      destruct y as [a_ e]. simpl in *. subst a_. 
      exists (mkTL ta_issue e). splits; auto.
      apply PREF_CLOS. red. exists (mkTL ta_cover e).
      apply seq_eqv_r. split; auto.
      apply ct_step. do 2 red. splits; try by (unfolder; vauto).
      do 2 left. do 2 left.
      right. red. basic_solver 10. }
    { forward eapply s2tc_coherence_helper
        with (r := rf) (D1 := fun _ => True) (D2 := W)
             (a1 := ta_cover) (a2 := ta_issue) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { rewrite wf_rfD; basic_solver. }
      { rewrite no_rf_to_init; basic_solver. }
      { rewrite wf_rfE; basic_solver. }
      do 2 apply inclusion_union_r1_search. apply inclusion_union_r2_search.
      unfold "RF". hahn_frame. apply map_rel_mori; [done| ].
      rewrite wf_rfD; [| done]. basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := sc) (D1 := fun _ => True) (D2 := fun _ => True)
             (a1 := ta_cover) (a2 := ta_cover) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { basic_solver. }
      { rewrite no_sc_to_init; basic_solver. }
      { rewrite wf_scE; basic_solver. }
      repeat apply inclusion_union_r1_search. unfold "SB". hahn_frame.
      apply map_rel_mori; [done| ]. by rewrite <- ct_step. }      
    { basic_solver. }
    { rewrite set_inter_union_l. apply set_subset_union_l. split; [basic_solver| ].
      rewrite init_w; basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := fwbob ⨾ ⦗W⦘) (D1 := W) (D2 := fun _ => True)
             (a1 := ta_issue) (a2 := ta_cover) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER.
           rewrite <- HELPER. apply dom_rel_mori. rewrite seqA.
           rewrite <- id_inter. hahn_frame. apply eqv_rel_mori.
           rewrite set_inter_union_l. apply set_subset_union_l. split.
           { basic_solver 10. }
           apply set_subset_inter_r. split; [| basic_solver].
           rewrite init_w; basic_solver. }
      { basic_solver. }
      { apply domb_rewrite. rewrite fwbob_in_sb.
        rewrite no_sb_to_init; basic_solver. }
      { rewrite wf_fwbobE; basic_solver. }
      apply inclusion_union_r1_search, inclusion_union_r2_search.
      unfold "FWBOB". basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := ⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘) (D1 := W) (D2 := W)
             (a1 := ta_issue) (a2 := ta_issue) as HELPER; eauto.
      5: { etransitivity; [| apply HELPER].
           apply dom_rel_mori. rewrite !seqA. do 2 hahn_frame_l.
           (* TODO: unify with previous case *)
           rewrite <- id_inter. apply eqv_rel_mori.
           rewrite set_inter_union_l. apply set_subset_union_l. split.
           { basic_solver 10. }
           apply set_subset_inter_r. split; [| basic_solver].
           rewrite init_w; basic_solver. } 
      { basic_solver. }
      { red. intros x y REL%seq_eqv_lr. desc. 
        do 2 apply seqA. apply seq_eqv_r. split; [basic_solver| ]. 
        intros INIT. apply ct_end in REL0 as [z [? REL']]. 
        forward eapply no_ar_rf_ppo_loc_to_init as [NOI _]; eauto.
        apply (NOI z y). basic_solver. }
      { rewrite wf_ar_rf_ppo_locE; auto. rewrite <- !restr_relE. split; auto.
        red in H. desc. apply restr_ct in H. red in H. by desc. }
      { apply inclusion_union_r2_search. unfold "AR". hahn_frame. basic_solver. }
    }
  Qed. 

  Section StepsEnum.
    
    Variable (steps: nat -> trav_label).
    Hypothesis (ENUM: enumerates steps (graph_steps G)).
    Hypothesis (RESP: respects_rel steps iord⁺ (graph_steps G)).

    Lemma trav_prefix_coherent_alt WF COMP WFSC CONS
          (i : nat) (DOMi: NOmega.le (NOnum i) (set_size (graph_steps G))):
      tc_coherent_alt G sc (set2trav_config (trav_prefix steps i)).
    Proof using RESP ENUM.
      apply s2tc_closed_coherent_alt; auto.
      apply trav_prefix_iord_closed; auto. 
    Qed.

    (*Local lemma*)
    Lemma trav_prefix_extend i
          (DOMsi: NOmega.lt_nat_l i (set_size (graph_steps G))):
      let (a, e) := steps i in
      set2trav_config (trav_prefix steps (S i)) =
      (set2trav_config (trav_prefix steps i)) ⊔
      (mkTC (if a then eq e else ∅) (if a then ∅ else eq e)).
    Proof using ENUM.
      destruct (steps i) as [a e] eqn:I.
      replace (trav_prefix (S i)) with (trav_prefix i ∪₁ eq (steps i)).
      2: { apply set_extensionality. symmetry. by apply trav_prefix_ext. }

      assert (eq (steps i) ≡₁ (action ↓₁ eq a ∩₁ event ↓₁ eq e)) as EQ_ALT.
      { rewrite I. split; [basic_solver| ]. unfolder. ins. desc. 
        destruct x. simpl in *. by subst. }
      forward eapply (step_event_dom i) as [[Ee NIe] W'e]; auto.
      rewrite I in Ee, NIe. simpl in *.

      apply same_tc_extensionality. split. 
      { unfold set2trav_config. simpl. etransitivity.
        2: { eapply set_equiv_union; [reflexivity| ].
             apply set_inter_absorb_r with (s' := E). basic_solver. }
        rewrite <- set_inter_union_l. apply set_equiv_inter; [| basic_solver].

        rewrite set_inter_union_r, set_collect_union, set_minus_union_l.
        rewrite !set_unionA. apply set_equiv_union; [basic_solver| ].

        rewrite set_unionC.         
        rewrite set_split_complete with (s' := if a then eq e else ∅) (s := is_init).
        rewrite <- set_unionA. apply set_equiv_union; [basic_solver| ]. 
        rewrite <- set_minusE. apply set_equiv_minus; [| basic_solver].

        rewrite EQ_ALT, <- set_interA, <- set_map_inter.
        destruct a.
        2: { split; [| basic_solver]. unfolder. ins. desc. congruence. }
        rewrite set_interK. split; [basic_solver| ].
        red. intros ? <-.
        red. exists (steps i). by rewrite I. }

      (* TODO: unify with 'covered' case? *)
      { unfold set2trav_config. simpl. etransitivity.
        2: { eapply set_equiv_union; [reflexivity| ].
             apply set_inter_absorb_r with (s' := E). basic_solver. }
        rewrite <- set_inter_union_l. apply set_equiv_inter; [| basic_solver].

        rewrite !set_inter_union_r, !set_collect_union.
        (* a difference from the previous case here *)
        rewrite set_inter_union_l. rewrite set_minus_union_l.
        rewrite !set_unionA. apply set_equiv_union; [basic_solver| ].

        rewrite set_unionC.         
        rewrite set_split_complete with (s' := if a then ∅ else eq e) (s := is_init).
        rewrite <- set_unionA. apply set_equiv_union; [basic_solver| ]. 
        rewrite <- set_minusE. apply set_equiv_minus; [| basic_solver].

        rewrite EQ_ALT, <- set_interA, <- set_map_inter.
        destruct a.
        { split; [| basic_solver]. unfolder. ins. desc. congruence. }
        rewrite set_interK. split; [basic_solver| ].
        red. intros ? <-.
        specialize_full W'e; [by rewrite I| ]. rewrite I in W'e. simpl in *. 
        red. splits; auto. exists (steps i). by rewrite I. }
    Qed.

    (*Local lemma*)
    Lemma itrav_prefix_step WF COMP WFSC CONS
          i (DOMsi: NOmega.lt_nat_l i (set_size graph_steps)):
      itrav_step G sc (event (steps i)) (set2trav_config (trav_prefix i))
                (set2trav_config (trav_prefix (S i))).
    Proof using RESP ENUM.
      red. destruct (steps i) as [a e] eqn:I.
      assert (~ (event ↑₁ (action ↓₁ eq a ∩₁ trav_prefix i)) e) as NOPREF.
      { intros PREFe. 
        red in PREFe. desc. destruct y. simpl in PREFe0. subst event.
        destruct (classic (action = a)) as [-> | ?].
        2: { generalize PREFe; basic_solver. }
          rewrite <- I in PREFe. red in PREFe. 
          desc. eapply prefix_border; eauto. }

      destruct a; [left | right].

      { forward eapply trav_prefix_extend as EQs; eauto. rewrite I in EQs.
        splits.
        3, 4: rewrite EQs; simpl; basic_solver 10.
        { unfold set2trav_config. simpl.
          intros [[[PREFe NIe] | Ie] Ee].
          { by apply NOPREF. }
          forward eapply (step_event_dom i); eauto.
          rewrite I. basic_solver. }
        apply coverable_add_eq_iff; auto.
        apply covered_in_coverable; [| basic_solver].
        apply tc_coherent_alt_implies_tc_coherent.
        erewrite @f_equal. 
        { eapply trav_prefix_coherent_alt; auto. apply DOMsi. }
        rewrite EQs. unfold trav_config_union.
        apply same_tc_extensionality; split; basic_solver. }

      forward eapply trav_prefix_extend as EQs; eauto. rewrite I in EQs.
      splits.
      3, 4: rewrite EQs; simpl; basic_solver 10.
      { unfold set2trav_config. simpl.
        intros [[[PREFe NIe] | Ie] Ee].
        { apply NOPREF. generalize PREFe. basic_solver. }
        forward eapply (step_event_dom i); eauto.
        rewrite I. basic_solver. }
      apply issuable_add_eq_iff; auto.
      apply issued_in_issuable; [| basic_solver].
      apply tc_coherent_alt_implies_tc_coherent.
      erewrite @f_equal. 
      { eapply trav_prefix_coherent_alt; auto. apply DOMsi. }          
      rewrite EQs. unfold trav_config_union.
      apply same_tc_extensionality; split; basic_solver.
    Qed.

    Lemma trav_prefix_step WF COMP WFSC CONS
          i (DOMsi: NOmega.lt_nat_l i (set_size graph_steps)):
      trav_step G sc (set2trav_config (trav_prefix i))
                (set2trav_config (trav_prefix (S i))).
    Proof using RESP ENUM.
      forward eapply itrav_prefix_step; eauto. vauto.
    Qed. 
