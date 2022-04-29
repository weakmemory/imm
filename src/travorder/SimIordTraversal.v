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
Require Import FairExecution.
Require Import AuxRel2.
Require Import travorder.TraversalOrder.
Require Import travorder.TLSCoherency.
Require Import travorder.IordCoherency.
Require Import travorder.SimClosure.
Require Import AuxRel2.
Require Import ImmFair.

Import ListNotations.

(* TODO: move to lib *)
Ltac liaW no := destruct no; [done| ins; lia]. 

Set Implicit Arguments.

Section IordTraversal. 
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

  Lemma s2tc_coherence_helper WF COMP WFSC CONS
        (a1 a2: trav_action)
        (D1 D2: actid -> Prop)
        (r: relation actid)
        (S: trav_label -> Prop)
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
    do 2 left. apply REL_IORD. basic_solver.
  Qed.

  Section StepsEnum.
    
    Variable (steps: nat -> trav_label).
    Hypothesis (ENUM: enumerates steps (exec_tls G)).
    Hypothesis (RESP: respects_rel steps iord⁺ (exec_tls G)).

    Definition trav_prefix (i: nat) : trav_label -> Prop :=
      ⋃₁ j < i, eq (steps j).

    Lemma trav_prefix_iord_closed WF COMP WFSC CONS
          i (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))):
      dom_rel (iord⁺ ⨾ ⦗trav_prefix i⦘) ⊆₁ trav_prefix i.
    Proof using ENUM RESP.
      unfold trav_prefix. 
      red. intros e' [e DOMe']. apply seq_eqv_r in DOMe' as [REL ENUMe].
      red in ENUMe. destruct ENUMe as [j [LTji STEPje]].
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize (IND e'). specialize_full IND.
      { eapply clos_trans_more in REL.
        2: { symmetry. apply iord_exec_tls. }
        apply restr_ct in REL. apply REL. }
        
      destruct IND as [k [DOMk STEPke']].
      red. exists k. splits; eauto.      
      etransitivity; [| apply LTji].
      red in RESP. apply RESP with (j := j); eauto.
      2: congruence.
      liaW (set_size (exec_tls G)). 
    Qed. 

    (* TODO: generalize to arbitrary enumerations? *)
    Lemma prefix_border i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))):
      ~ trav_prefix i (steps i).
    Proof using ENUM.
      unfold trav_prefix. intros [j [LT EQ]]. 
      apply enumeratesE' in ENUM. cdes ENUM.
      forward eapply INJ; [| | apply EQ| lia]; auto. 
      eapply NOmega.lt_lt_nat; eauto.
    Qed.

    Lemma step_event_dom i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))):
      (E \₁ is_init) (event (steps i)) /\
      (action (steps i) = ta_issue -> W (event (steps i))). 
    Proof using ENUM. 
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize_full INSET; eauto. red in INSET.
      destruct (steps i) as [a e]. unfolder in INSET. basic_solver. 
    Qed. 

    Lemma trav_prefix_ext i
          (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))):
      trav_prefix (S i) ≡₁ trav_prefix i ∪₁ eq (steps i).
    Proof using. 
      unfold trav_prefix.
      arewrite ((fun x => x < S i) ≡₁ (fun x => x < i) ∪₁ eq i).
      { unfolder. split; ins; lia. }
      rewrite set_bunion_union_l. basic_solver.
    Qed.

(* End IordTraversal.  *)

(* Section Traversal. *)
(*   Variable (steps: nat -> trav_label). *)
(*   Hypothesis (ENUM: enumerates steps (exec_tls G)). *)
(*   Hypothesis (RESP: respects_rel steps (iord G sc)⁺ (exec_tls G)). *)
  
  Definition tc_enum (i: nat): trav_label -> Prop  :=
    sim_clos G (trav_prefix i) ∪₁ init_tls G. 
  
  Lemma trav_prefix_init:
    trav_prefix 0 ≡₁ ∅. 
  Proof.
    unfold trav_prefix. apply set_subset_empty_r, set_subset_bunion_l.
    ins. lia. 
  Qed.
    
  Lemma trav_prefix_iord_coherent 
        (i : nat) (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))):
    iord_coherent G sc (trav_prefix i).
  Proof using RESP ENUM.
    induction i.
    { rewrite trav_prefix_init. red. basic_solver. }
    rewrite trav_prefix_ext; eauto. red.
    rewrite id_union, seq_union_r, dom_union.
    apply set_subset_union_l. split. 
    { unfold iord_coherent in IHi. rewrite IHi; [basic_solver| ].
      liaW (set_size (exec_tls G)). }
    red. intros tlj. intros [tli IORD%seq_eqv_r]. desc.
    apply iord_exec_tls in IORD. red in IORD. desc.
    apply enumeratesE' in ENUM. cdes ENUM.
    apply IND in IORD1, IORD2. desc. rename i1 into j.
    assert (i0 = i) as -> by (apply INJ; auto; congruence).
    subst. 
    pose proof (Nat.lt_trichotomy i j) as LT. des; revgoals. 
    { left. red. vauto. }
    { subst. basic_solver. }
    enough (j < i); [lia| ]. eapply RESP; eauto. 
  Qed.
  
  Lemma trav_prefix_step
        i (DOMsi: NOmega.lt_nat_l i (set_size (exec_tls G))):
    iord_step G sc (trav_prefix i) (trav_prefix (S i)).
  Proof using RESP ENUM.
    red. exists (steps i). do 2 red.
    splits; try by (apply trav_prefix_iord_coherent; liaW (set_size (exec_tls G))).
    apply seq_eqv_l. split.
    { eapply prefix_border; eauto. }
    eapply trav_prefix_ext; eauto. 
  Qed.

  Lemma init_tls_sim_coh WF:
    sim_coherent G (init_tls G).
  Proof. 
    unfold sim_coherent, sim_clos. split; [basic_solver| ].
    repeat (apply set_subset_union_l; split); try basic_solver.
    { unfold rmw_clos. rewrite set_pair_alt. etransitivity.
      { red. intro. apply proj2. }
      iord_dom_unfolder. do 2 red in d. desc. red in d. desc.
      apply init_tls_EI in d. red in d.
      apply rmw_non_init_lr, seq_eqv_lr in d0; auto. type_solver. }
    { unfold rel_clos. rewrite set_pair_alt. etransitivity.
      { red. intro. apply proj2. }
      iord_dom_unfolder. do 2 red in d. desc. red in d. desc.
      apply init_tls_EI in d. do 2 red in d. desc.
      destruct y, a0; try by vauto. ins. subst. 
      forward eapply (wf_init_lab WF l) as ?.
      unfold is_rel, Events.mod in c. rewrite H in c. vauto. }
  Qed.

  (* TODO: group similar lemmas about union with init_tls *)
  Lemma trav_prefix_init_tls_iord_coherent i
        (DOMi : NOmega.le (NOnum i) (set_size (exec_tls G))):
    iord_coherent G sc (trav_prefix i ∪₁ init_tls G).
  Proof.
    red. unfold tc_enum. rewrite id_union, seq_union_r, dom_union.
    apply set_subset_union_l. split.
    { apply set_subset_union_r. left. apply trav_prefix_iord_coherent; auto. }
    unfold "iord". rewrite init_tls_EI at 1. basic_solver.
  Qed. 

  (* TODO: move upper *)
  Lemma init_exec_tls_disjoint:
    set_disjoint (init_tls G) (exec_tls G). 
  Proof. unfold init_tls, exec_tls. iord_dom_unfolder. Qed. 

  Lemma trav_prefix_in_exec_tls i
        (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))):
    trav_prefix i ⊆₁ exec_tls G. 
  Proof. 
    apply enumeratesE' in ENUM. cdes ENUM. 
    unfold trav_prefix. apply set_subset_bunion_l. intros.
    apply set_subset_single_l. apply INSET.
    liaW (set_size (exec_tls G)). 
  Qed.

  Lemma trav_prefix_step_ext
        i (DOMsi: NOmega.lt_nat_l i (set_size (exec_tls G))):
    iord_step G sc (trav_prefix i ∪₁ init_tls G)
              (trav_prefix (S i) ∪₁ init_tls G). 
  Proof. 
    forward eapply trav_prefix_step as [l STEP]; eauto.
    red. exists l. do 2 red.
    splits; try by (apply trav_prefix_init_tls_iord_coherent; liaW (set_size (exec_tls G))).
    do 2 red in STEP. desc. apply seq_eqv_l in STEP. desc.  
    apply seq_eqv_l. split.
    2: { rewrite STEP2. basic_solver. }
    apply set_compl_union. split; auto.
    apply set_disjoint_eq_r. eapply set_disjoint_mori; [reflexivity| ..].
    2: by apply init_exec_tls_disjoint.
    red. rewrite <- (@trav_prefix_in_exec_tls (S i)); auto.
    rewrite STEP2. basic_solver. 
  Qed. 
  
  (* TODO: move upper *)
  Lemma exec_tls_sim_coh WF:
    sim_coherent G (exec_tls G).
  Proof. 
    unfold sim_coherent, sim_clos. split; [basic_solver| ].
    repeat (apply set_subset_union_l; split; try basic_solver). 
    { unfold rmw_clos, exec_tls, tl_covered, tl_issued.
      repeat rewrite set_pair_alt.
      rewrite wf_rmwE, wf_rmwD, rmw_non_init_lr; auto. 
      iord_dom_unfolder; [by vauto| ]. 
      right. eauto. }
    { unfold rel_clos, exec_tls, tl_covered, tl_issued.
      repeat rewrite set_pair_alt.
      iord_dom_unfolder. left. vauto. }
  Qed. 

  Lemma tc_enum_tls_coherent WF i
      (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))):
    tls_coherent G (tc_enum i). 
  Proof.
    unfold tc_enum. split; [basic_solver| ].
    apply set_subset_union_l. split; [| basic_solver].
    erewrite sim_clos_mori.
    2: { apply trav_prefix_in_exec_tls. auto. }
    pose proof (exec_tls_sim_coh WF). red in H. rewrite <- H. basic_solver. 
  Qed.

  Lemma trav_prefix_union_init_tls_coherent WF i
      (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))):
    tls_coherent G (trav_prefix i ∪₁ init_tls G). 
  Proof using ENUM. 
    apply tls_coherent_defs_equiv. exists (trav_prefix i). split; [| basic_solver].
    apply trav_prefix_in_exec_tls. auto. 
  Qed. 

  Lemma sim_traversal_next WF CONS:
    forall i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))),
      (sim_clos_step G sc)^* (tc_enum i) (tc_enum (1 + i)). 
  Proof using RESP ENUM.
    ins. unfold tc_enum.
    forward eapply init_tls_sim_coh as INIT_SCOH; auto. red in INIT_SCOH.
    rewrite INIT_SCOH, <- !sim_clos_dist; auto.  
    apply iord_step_implies_sim_clos_step; auto.
    red. splits; try by (apply trav_prefix_union_init_tls_coherent; liaW (set_size (exec_tls G))). 
    apply trav_prefix_step_ext; auto. 
  Qed.

  End StepsEnum.

  Lemma iord_enum_exists WF COMP WFSC CONS MF
        (IMM_FAIR: imm_s_fair G sc):
  exists (steps: nat -> trav_label),
    enumerates steps (exec_tls G) /\
      respects_rel steps iord⁺ (exec_tls G). 
  Proof using.
    edestruct countable_ext with (s := exec_tls G) (r := ⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord⁺)
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
    red in DOMi. clear -DOMi. unfold set_pair in *. unfolder in DOMi. desf; desf.
  Qed.
  
  (* TODO: rename? *)
  Lemma sim_traversal_inf WF CONS
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc):
    exists (sim_enum: nat -> (trav_label -> Prop)),
      ⟪INIT: sim_enum 0 ≡₁ init_tls G ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size (exec_tls G))),
          tls_coherent G (sim_enum i)⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls G))),
          (sim_clos_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
       ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i,
           NOmega.le (NOnum i) (set_size (exec_tls G)) /\
             (sim_enum i) (mkTL ta_cover e)⟫.
  Proof using.
    edestruct iord_enum_exists as [steps_enum [ENUM RESP]]; eauto.
    1, 2: by apply CONS.
    exists (tc_enum steps_enum). splits.
    { unfold tc_enum. rewrite trav_prefix_init.
      rewrite sim_clos_empty. basic_solver. }
    { apply tc_enum_tls_coherent; auto. }
    { apply sim_traversal_next; auto. }
    
    intros e Ee.
    pose proof ENUM as ENUM'. apply enumeratesE' in ENUM. desc.
    specialize (IND (mkTL ta_cover e)). specialize_full IND; [by vauto| ].
    desc. exists (S i). split; [by vauto| ].  
    eapply set_equiv_exp. 
    { unfold tc_enum. rewrite trav_prefix_ext; auto. }
    rewrite IND0. unfold sim_clos. basic_solver 10.  
  Qed.

End IordTraversal.

  

