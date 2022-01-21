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

Set Implicit Arguments.

Definition respects_rel {A: Type} (enum: nat -> A) (r: relation A) (S: A -> Prop) :=
  forall i j (DOMi: NOmega.lt_nat_l i (set_size S))
    (DOMj: NOmega.lt_nat_l j (set_size S))
    (Rij: r (enum i) (enum j)),
    i < j.

Definition trav_conf_union (tc1 tc2: trav_config) : trav_config :=
  mkTC (covered tc1 ∪₁ covered tc2) (issued tc1 ∪₁ issued tc2).

(* TODO: move to lib, or, better, to hahn *)
Lemma set_extensionality A (s s' : A -> Prop) :
  s ≡₁ s' -> s = s'.
Proof using.
  ins; extensionality x.
  apply propositional_extensionality; split; apply H.
Qed.


Lemma trav_config_eq_helper tc1 tc2
      (EQC: covered tc1 ≡₁ covered tc2) (EQI: issued tc1 ≡₁ issued tc2):
  tc1 = tc2.
Proof using.
  destruct tc1, tc2. simpl in *.  f_equal; apply set_extensionality; auto.
Qed.

(* TODO: move this lemma from promising2ToImm 
   (where it's named set_split_comlete) *)
Lemma set_split_complete {A: Type} (s s': A -> Prop):
  s' ≡₁ s' ∩₁ s ∪₁ s' ∩₁ (set_compl s).
Proof using. Admitted.

(* (* TODO: move upper *) *)
(* Require Import Coq.Logic.FinFun.  *)

(* Lemma add_map_collect {A B: Type} (f : A -> B) (ra : relation A): *)
(*   ra ⊆ map_rel f (collect_rel f ra). *)
(* Proof using. basic_solver 10. Qed.  *)

(* Lemma add_collect_map_rel {A B: Type} (f : B -> A) (ra : relation A) *)
(*       (SUR: Surjective f): *)
(*   ra ⊆ collect_rel f (map_rel f ra). *)
(* Proof using. *)
(*   unfolder. ins. *)
(*   red in SUR. destruct (SUR x), (SUR y).  *)
(*   do 2 eexists. splits; vauto. *)
(* Qed.  *)

(* Lemma add_collect_set_map {A B: Type} (f : B -> A) (sa : A -> Prop) *)
(*       (SUR: Surjective f): *)
(*   sa ⊆₁ set_collect f (set_map f sa). *)
(* Proof using. *)
(*   unfolder. ins. *)
(*   red in SUR. destruct (SUR x).  *)
(*   eexists. splits; vauto. *)
(* Qed.  *)

(* Lemma event_sur: Surjective event. *)
(* Proof using. red. ins. by exists (mkTL TravAction.cover y). Qed. *)

Module IordTraversal. 
  Include TraversalOrder.TravLabel.
  (* TODO: have to repeat this? *)
  Implicit Types (WF : Wf G) (COMP : complete G)
         (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
         (MF : mem_fair G).

  
  (* TODO: unify graph_steps and set2trav_config definitions? *)
  
  Definition graph_steps: t -> Prop :=
    (action ↓₁ (eq TravAction.cover) ∩₁ event ↓₁ (E \₁ is_init)) ∪₁
    (action ↓₁ (eq TravAction.issue) ∩₁ event ↓₁ ((E \₁ is_init) ∩₁ W)). 
  
  Definition set2trav_config (S: t -> Prop) :=
    mkTC
      ((event ↑₁ (action ↓₁ (eq TravAction.cover) ∩₁ S) \₁ is_init ∪₁ is_init) ∩₁ E)
      ((event ↑₁ (action ↓₁ (eq TravAction.issue) ∩₁ S) ∩₁ W \₁ is_init ∪₁ is_init) ∩₁ E).
  
  Lemma s2tc_closed_coherent_alt WF COMP WFSC CONS
        (S: t -> Prop)
        (PREF_CLOS: dom_rel (iord⁺ ;; ⦗S⦘) ⊆₁ S):
    tc_coherent_alt G sc (set2trav_config S).
  Proof using. 
    split; simpl. 
    { basic_solver. }
    { basic_solver. }
    { rewrite set_inter_union_l, id_union.
      rewrite seq_union_r, dom_union.
      apply set_subset_union_l. split.
      2: { rewrite no_sb_to_init. basic_solver. }
      
      rewrite <- seq_id_l with (r := sb) at 1.
      rewrite AuxRel2.set_full_split with (S0 := is_init).
      rewrite id_union, !seq_union_l. rewrite dom_union.  
      apply set_subset_union_l. split.
      { apply set_subset_union_r. right.
        rewrite wf_sbE, <- seqA, <- id_inter. basic_solver. }      

      unfolder. ins. desf. destruct y0 as [? e]. ins. subst. left.
      apply (dom_l (wf_sbE G)), seq_eqv_l in H0. desc.
      splits; auto.

      exists (mkTL TravAction.cover x). splits; auto. apply PREF_CLOS.
      red. eexists. apply seq_eqv_r. split; eauto.
      apply ct_step. red. red. splits; try by (unfolder; basic_solver).
      repeat left. red. apply seq_eqv_lr. splits; try by (unfolder; basic_solver).
      red. simpl. apply ct_step. basic_solver. }
    { admit. }
    { admit. }
    { admit. }
    { basic_solver. }
    { rewrite set_inter_union_l. apply set_subset_union_l. split; [basic_solver| ].
      rewrite init_w; basic_solver. }
    { admit. }
    { admit. }
  Admitted.

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
    trav_conf_union (set2trav_config S1) (set2trav_config S2).
  Proof using.
    unfold set2trav_config, trav_conf_union. simpl.
    f_equal; apply set_extensionality; basic_solver 10.
  Qed.         

  
  Section StepsEnum.
    
    Variable (steps: nat -> t).
    Hypothesis (ENUM: enumerates steps graph_steps).
    Hypothesis (RESP: respects_rel steps iord⁺ graph_steps).

    Definition trav_prefix (i: nat) : t -> Prop :=
      ⋃₁ j < i, eq (steps j). 

    Lemma trav_prefix_coherent_alt WF COMP WFSC CONS
          i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)):
      tc_coherent_alt G sc (set2trav_config (trav_prefix i)).
    Proof using RESP ENUM.
      unfold trav_prefix. 
      apply s2tc_closed_coherent_alt; auto.
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
      eapply NOmega.lt_lt_nat; eauto.
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
          (DOMsi: NOmega.lt_nat_l (S i) (set_size graph_steps)):
      let (a, e) := steps i in
      set2trav_config (trav_prefix (S i)) =
      trav_conf_union (set2trav_config (trav_prefix i))
                      (mkTC (if a then eq e else ∅)
                            (if a then ∅ else eq e)).
    Proof using ENUM.
      assert (NOmega.lt_nat_l i (set_size graph_steps)) as DOMi.
      { eapply NOmega.lt_lt_nat; eauto. }
      destruct (steps i) as [a e] eqn:I.
      replace (trav_prefix (S i)) with (trav_prefix i ∪₁ eq (steps i)).
      2: { apply set_extensionality. symmetry. by apply trav_prefix_ext. }

      assert (eq (steps i) ≡₁ (action ↓₁ eq a ∩₁ event ↓₁ eq e)) as EQ_ALT.
      { rewrite I. split; [basic_solver| ]. unfolder. ins. desc. 
        destruct x. simpl in *. by subst. }
      forward eapply (step_event_dom i) as [[Ee NIe] W'e]; auto.
      rewrite I in Ee, NIe. simpl in *.
      
      apply trav_config_eq_helper.
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

    Lemma trav_prefix_step WF COMP WFSC CONS
          i (DOMsi: NOmega.lt_nat_l (S i) (set_size graph_steps)):
      trav_step G sc (set2trav_config (trav_prefix i))
                (set2trav_config (trav_prefix (S i))).
    Proof using RESP ENUM.
      assert (NOmega.lt_nat_l i (set_size graph_steps)) as DOMi.
      { eapply NOmega.lt_lt_nat; eauto. }
      red. destruct (steps i) as [a e] eqn:I. exists e.
      assert (~ (event ↑₁ (action ↓₁ eq a ∩₁ trav_prefix i)) e) as NOPREF.
      { intros PREFe. 
        red in PREFe. desc. destruct y. simpl in PREFe0. subst event0.
        destruct (classic (action0 = a)) as [-> | ?].
        2: { generalize PREFe; basic_solver. }
          rewrite <- I in PREFe. red in PREFe. 
          desc. eapply prefix_border; eauto. }
        
      red. destruct a; [left | right].

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
        rewrite EQs. unfold trav_conf_union.
        apply trav_config_eq_helper; basic_solver. }

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
      rewrite EQs. unfold trav_conf_union.
      apply trav_config_eq_helper; basic_solver.
    Qed.
    
  End StepsEnum. 

  Lemma iord_enum_exists WF COMP WFSC CONS:
    exists (steps: nat -> t),
      enumerates steps graph_steps /\
      respects_rel steps iord⁺ graph_steps. 
  Proof using.
    edestruct countable_ext with (s := graph_steps) (r := iord⁺)
      as [| [steps [ENUM RESP]]].
    { eapply countable_subset; [| by apply set_subset_full_r].
      admit. }
    { red. split; [apply iord_acyclic | apply transitive_ct]; auto. }
    { apply iord_ct_fsupp; auto.
      all: admit. }
    { edestruct H. constructor. econstructor; vauto. }
    exists steps. splits; eauto.
    red. ins. apply RESP; auto.
    all: by apply set_lt_size. 
  Admitted.
            
       
End IordTraversal. 
