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
Require Import ImmFair.

Set Implicit Arguments.

Definition respects_rel {A: Type} (enum: nat -> A) (r: relation A) (S: A -> Prop) :=
  forall i j (DOMi: NOmega.lt_nat_l i (set_size S))
    (DOMj: NOmega.lt_nat_l j (set_size S))
    (Rij: r (enum i) (enum j)),
    i < j.

(* TODO: move to lib, or, better, to hahn *)
Lemma set_extensionality A (s s' : A -> Prop) :
  s ≡₁ s' -> s = s'.
Proof using.
  ins; extensionality x.
  apply propositional_extensionality; split; apply H.
Qed.

(* TODO: move into TraversalConfig *)
(* TODO: rename? *)
Global Add Parametric Morphism : mkTC with signature
    (@set_equiv actid) ==> (@set_equiv actid) ==> same_trav_config as mkTC_more.
Proof using. vauto. Qed.  


(* TODO: move to TraversalConfig? *)
Lemma same_tc_extensionality tc1 tc2 (SAME: same_trav_config tc1 tc2):
  tc1 = tc2.
Proof using.
  destruct SAME.
  destruct tc1, tc2. ins. apply set_extensionality in H, H0.   
  congruence. 
Qed. 

Section TravConfigUnion.

  Definition trav_config_union (tc1 tc2: trav_config) : trav_config :=
    mkTC (covered tc1 ∪₁ covered tc2) (issued tc1 ∪₁ issued tc2).

  Notation " tc1 '⊔' tc2 " := (trav_config_union tc1 tc2) (at level 10).
  
  Lemma tcu_same_equiv (tc1 tc2 tc1' tc2': trav_config)
        (SAME1: same_trav_config tc1 tc1') (SAME2: same_trav_config tc2 tc2'):
    tc1 ⊔ tc2 = tc1' ⊔ tc2'.
  Proof using.
    apply same_tc_extensionality.
    unfold trav_config_union. 
    destruct SAME1 as [-> ->], SAME2 as [-> ->]. reflexivity. 
  Qed.

  Definition empty_tc := mkTC ∅ ∅.

  Lemma tcu_empty_l (tc: trav_config):
    tc ⊔ empty_tc = tc.
  Proof using.
    apply same_tc_extensionality. 
    unfold trav_config_union, empty_tc. simpl.
    rewrite !set_union_empty_r. by destruct tc.  
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

Notation " tc1 '⊔' tc2 " := (trav_config_union tc1 tc2) (at level 10). 

    
(* TODO: move to hahn *)
Lemma set_split_complete {A: Type} (s s': A -> Prop):
  s' ≡₁ s' ∩₁ s ∪₁ s' ∩₁ (set_compl s).
Proof using.
  rewrite <- set_inter_union_r. rewrite <- AuxRel2.set_full_split. basic_solver. 
Qed.


Module IordTraversal. 
  Include TraversalOrder.TravLabel.
  (* TODO: have to repeat this? *)
  Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).

  
  Definition graph_steps: t -> Prop :=
    (action ↓₁ (eq TravAction.cover) ∩₁ event ↓₁ (E \₁ is_init)) ∪₁
    (action ↓₁ (eq TravAction.issue) ∩₁ event ↓₁ ((E \₁ is_init) ∩₁ W)). 
  
  Definition set2trav_config (S: t -> Prop) :=
    mkTC
      ((event ↑₁ (action ↓₁ (eq TravAction.cover) ∩₁ S) \₁ is_init ∪₁ is_init) ∩₁ E)
      ((event ↑₁ (action ↓₁ (eq TravAction.issue) ∩₁ S) ∩₁ W \₁ is_init ∪₁ is_init) ∩₁ E).
  

  Lemma s2tc_coherence_helper WF COMP WFSC CONS
        (a1 a2: TravAction.t)
        (D1 D2: actid -> Prop)
        (r: relation actid)
        (S: t -> Prop)
        (D2R: r ⊆ ⦗D2⦘ ⨾ r)
        (RELNINIT: r ⊆ r ⨾ ⦗set_compl is_init⦘)
        (RELE: r ⊆ restr_rel E r)
        (PREF_CLOS: dom_rel (iord⁺ ;; ⦗S⦘) ⊆₁ S)
        (REL_IORD: ⦗action ↓₁ eq a2⦘ ⨾ event ↓ r ⨾ ⦗action ↓₁ eq a1⦘ ⊆
                                     (SB ∪ RF ∪ FWBOB ∪ AR)):
  dom_rel
    (r
     ⨾ ⦗(event ↑₁ (action ↓₁ eq a1 ∩₁ S) ∩₁ D1 \₁ is_init ∪₁ is_init) ∩₁ E⦘)
    ⊆₁ (event ↑₁ (action ↓₁ eq a2 ∩₁ S) ∩₁ D2 \₁ is_init ∪₁ is_init) ∩₁ E.
  Proof using.
    unfolder. intros x [y REL]. desc. des.
    2: { apply RELNINIT, seq_eqv_r in REL. basic_solver. }
    destruct y0 as [a y_]. simpl in *. subst a y_.
    apply RELE in REL. red in REL. desc. clear REL4. splits; auto.
    destruct (classic (is_init x)); [tauto| left]. splits; auto.
    2: { apply D2R, seq_eqv_l in REL. basic_solver. } 
    exists (mkTL a2 x). splits; auto.
    apply PREF_CLOS. red. eexists. apply seq_eqv_r. split; [| by apply REL5].
    apply ct_step. do 2 red. splits; try by basic_solver.
    apply REL_IORD. basic_solver.
  Qed. 
    
  
  Lemma s2tc_closed_coherent_alt WF COMP WFSC CONS
        (S: t -> Prop)
        (PREF_CLOS: dom_rel (iord⁺ ;; ⦗S⦘) ⊆₁ S):
    tc_coherent_alt G sc (set2trav_config S).
  Proof using.
    split; simpl. 
    { basic_solver. }
    { basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := sb) (D1 := fun _ => True) (D2 := fun _ => True)
             (a1 := TravAction.cover) (a2 := TravAction.cover) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { basic_solver. } 
      { rewrite no_sb_to_init. basic_solver. }
      { rewrite wf_sbE. basic_solver. }
      repeat apply inclusion_union_r1_search. unfold SB.
      hahn_frame. apply map_rel_mori; [done| ]. by rewrite <- ct_step. }
    { unfolder. intros e De. desc. splits; auto. desf; auto. left. splits; auto.
      destruct y as [a_ e]. simpl in *. subst a_. 
      exists (mkTL TravAction.issue e). splits; auto.
      apply PREF_CLOS. red. exists (mkTL TravAction.cover e).
      apply seq_eqv_r. split; auto.
      apply ct_step. do 2 red. splits; try by (unfolder; vauto).
      do 2 left. right. red. basic_solver 10. }
    { forward eapply s2tc_coherence_helper
        with (r := rf) (D1 := fun _ => True) (D2 := W)
             (a1 := TravAction.cover) (a2 := TravAction.issue) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { rewrite wf_rfD; basic_solver. }
      { rewrite no_rf_to_init; basic_solver. }
      { rewrite wf_rfE; basic_solver. }
      do 2 apply inclusion_union_r1_search. apply inclusion_union_r2_search.
      unfold RF. hahn_frame. apply map_rel_mori; [done| ].
      rewrite wf_rfD; [| done]. basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := sc) (D1 := fun _ => True) (D2 := fun _ => True)
             (a1 := TravAction.cover) (a2 := TravAction.cover) as HELPER; eauto.
      5: { rewrite set_inter_full_r in HELPER. auto. }
      { basic_solver. }
      { rewrite no_sc_to_init; basic_solver. }
      { rewrite wf_scE; basic_solver. }
      repeat apply inclusion_union_r1_search. unfold SB. hahn_frame.
      apply map_rel_mori; [done| ]. by rewrite <- ct_step. }      
    { basic_solver. }
    { rewrite set_inter_union_l. apply set_subset_union_l. split; [basic_solver| ].
      rewrite init_w; basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := fwbob ⨾ ⦗W⦘) (D1 := W) (D2 := fun _ => True)
             (a1 := TravAction.issue) (a2 := TravAction.cover) as HELPER; eauto.
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
      unfold FWBOB. basic_solver. }
    { forward eapply s2tc_coherence_helper
        with (r := ⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘) (D1 := W) (D2 := W)
             (a1 := TravAction.issue) (a2 := TravAction.issue) as HELPER; eauto.
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
      { apply inclusion_union_r2_search. unfold AR. hahn_frame. basic_solver. }
    }
  Qed. 

  Lemma iord_graph_steps:
    iord ≡ restr_rel graph_steps iord.
  Proof using.
    split; [| basic_solver].
    unfold iord, graph_steps. unfolder. intros x y REL. desc.
    destruct x as [ax ex], y as [ay ey]. simpl in *.    
    assert (TravAction.cover = ax \/ TravAction.issue = ax /\ is_w lab ex) as AX.
    { destruct ax; auto. right. split; auto.
      des; apply seq_eqv_lr in REL; desc; try by vauto. 
      all: apply seq_eqv_l in REL4; desc; vauto. }
    assert (TravAction.cover = ay \/ TravAction.issue = ay /\ is_w lab ey) as AY.
    { destruct ay; auto. right. split; auto.
      des; apply seq_eqv_lr in REL; desc; try by vauto.
      { apply seq_eqv_r in REL4; desc; vauto. }
      apply seq_eqv_lr in REL4; desc; vauto. }
    tauto.
  Qed. 

  Lemma set2trav_config_union (S1 S2: t -> Prop):
    set2trav_config (S1 ∪₁ S2) =
    (set2trav_config S1) ⊔ (set2trav_config S2).
  Proof using.
    unfold set2trav_config, trav_config_union. simpl.
    f_equal; apply set_extensionality; basic_solver 10.
  Qed.         

  
  Section StepsEnum.
    
    Variable (steps: nat -> t).
    Hypothesis (ENUM: enumerates steps graph_steps).
    Hypothesis (RESP: respects_rel steps iord⁺ graph_steps).

    Definition trav_prefix (i: nat) : t -> Prop :=
      ⋃₁ j < i, eq (steps j).

    Lemma trav_prefix_iord_closed WF COMP WFSC CONS
          i (DOMi: NOmega.le (NOnum i) (set_size graph_steps)):
      dom_rel (iord⁺ ⨾ ⦗trav_prefix i⦘) ⊆₁ trav_prefix i.
    Proof using ENUM RESP.
      unfold trav_prefix. 
      red. intros e' [e DOMe']. apply seq_eqv_r in DOMe' as [REL ENUMe].
      red in ENUMe. destruct ENUMe as [j [LTji STEPje]].
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize (IND e'). specialize_full IND.
      { eapply clos_trans_more in REL.
        2: { symmetry. apply iord_graph_steps. }
        apply restr_ct in REL. apply REL. }
        
      destruct IND as [k [DOMk STEPke']].
      red. exists k. splits; eauto.      
      etransitivity; [| apply LTji].
      red in RESP. apply RESP with (j := j); eauto.
      2: congruence.
      destruct (set_size graph_steps); auto; simpl in *; lia. 
    Qed. 

    Lemma trav_prefix_coherent_alt WF COMP WFSC CONS
          i (DOMi: NOmega.le (NOnum i) (set_size graph_steps)):
      tc_coherent_alt G sc (set2trav_config (trav_prefix i)).
    Proof using RESP ENUM.
      apply s2tc_closed_coherent_alt; auto.
      apply trav_prefix_iord_closed; auto. 
    Qed.

    (* TODO: generalize to arbitrary enumerations? *)
    Lemma prefix_border i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)):
      ~ trav_prefix i (steps i).
    Proof using ENUM.
      unfold trav_prefix. intros [j [LT EQ]]. 
      apply enumeratesE' in ENUM. cdes ENUM.
      forward eapply INJ; [| | apply EQ| lia]; auto. 
      eapply NOmega.lt_lt_nat; eauto.
    Qed.

    Lemma step_event_dom i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)):
      (E \₁ is_init) (event (steps i)) /\
      (action (steps i) = TravAction.issue -> W (event (steps i))). 
    Proof using ENUM. 
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize_full INSET; eauto. red in INSET.
      destruct (steps i) as [a e]. unfolder in INSET. basic_solver. 
    Qed. 

    Lemma trav_prefix_ext i
          (DOMi: NOmega.lt_nat_l i (set_size graph_steps)):
      trav_prefix (S i) ≡₁ trav_prefix i ∪₁ eq (steps i).
    Proof using. 
      unfold trav_prefix.
      arewrite ((fun x => x < S i) ≡₁ (fun x => x < i) ∪₁ eq i).
      { unfolder. split; ins; lia. }
      rewrite set_bunion_union_l. basic_solver.
    Qed.
    
    Lemma trav_prefix_extend i
          (DOMsi: NOmega.lt_nat_l i (set_size graph_steps)):
      let (a, e) := steps i in
      set2trav_config (trav_prefix (S i)) =
      (set2trav_config (trav_prefix i)) ⊔
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

    Lemma itrav_prefix_step WF COMP WFSC CONS
          i (DOMsi: NOmega.lt_nat_l i (set_size graph_steps)):
      itrav_step G sc (event (steps i)) (set2trav_config (trav_prefix i))
                (set2trav_config (trav_prefix (S i))).
    Proof using RESP ENUM.
      red. destruct (steps i) as [a e] eqn:I.
      assert (~ (event ↑₁ (action ↓₁ eq a ∩₁ trav_prefix i)) e) as NOPREF.
      { intros PREFe. 
        red in PREFe. desc. destruct y. simpl in PREFe0. subst event0.
        destruct (classic (action0 = a)) as [-> | ?].
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
    
  End StepsEnum.

  Definition ae2tl (ae: TravAction.t * actid): TravLabel.t
    := mkTL (fst ae) (snd ae). 
  Definition tl2ae (tl: TravLabel.t): TravAction.t * actid
    := (action tl, event tl).

  Lemma ae_tl_isomorphic: isomorphism ae2tl tl2ae.
  Proof using. split; ins; [destruct a | destruct b]; auto. Qed.

   
  
  Lemma ae_countable: countable (@set_full (TravAction.t * actid)).
  Proof using.
    apply countable_prod.
    { apply finite_countable. exists [TravAction.cover; TravAction.issue].
      ins. destruct x; tauto. }
    apply actid_countable. 
  Qed. 
    
  Lemma trav_label_countable: @countable t (@set_full t).
  Proof using.
    eapply countable_isomorphic; [apply ae_tl_isomorphic| apply ae_countable].
  Qed. 

  Lemma iord_enum_exists WF COMP WFSC CONS MF
        (IMM_FAIR: imm_s_fair G sc):
    exists (steps: nat -> t),
      enumerates steps graph_steps /\
      respects_rel steps iord⁺ graph_steps. 
  Proof using.
    edestruct countable_ext with (s := graph_steps) (r := ⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord⁺)
      as [| [steps [ENUM RESP]]].
    { eapply countable_subset; [| by apply set_subset_full_r].
      apply trav_label_countable. }
    { red. split.
      { rewrite inclusion_seq_eqv_l. by apply iord_acyclic. }
      red. intros ? ? ? ?%seq_eqv_l  ?%seq_eqv_l. desc.
      apply seq_eqv_l. split; auto. eapply transitive_ct; eauto. }
    { apply iord_ct_fsupp; auto. }
    { edestruct H. constructor. econstructor; vauto. }
    exists steps. splits; eauto.
    red. ins. apply RESP; auto.
    1, 2: by apply set_lt_size.
    apply seq_eqv_l. split; auto.
    apply enumeratesE' in ENUM. desc. apply INSET in DOMi.
    red in DOMi. destruct DOMi as [T | T]; apply T. 
  Qed.
  
End IordTraversal. 
