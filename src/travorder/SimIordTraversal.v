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
Require Import EnumPrefix.
Require Import FinThreads. 

Import ListNotations.

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

  Section IordEnum.
    (* This generalization is used to support traversal 
       of both complete exec_tls and its parts *)

  Variable (steps: nat -> trav_label).
  Variable (dom: trav_label -> Prop).
  Hypothesis (IORD_DOM: iord ⊆ dom × dom).
  Hypothesis (DOM_EXEC: dom ⊆₁ exec_tls G). 
  Hypothesis (ENUM: enumerates steps dom).
  Hypothesis (RESP: respects_rel steps iord⁺ dom).

  Lemma trav_prefix_in_exec_tls i
        (DOMi: NOmega.le (NOnum i) (set_size dom)):
    trav_prefix steps i ⊆₁ exec_tls G. 
  Proof using ENUM DOM_EXEC. 
    apply enumeratesE' in ENUM. cdes ENUM. 
    unfold trav_prefix. apply set_subset_bunion_l. intros.
    rewrite <- DOM_EXEC. apply set_subset_single_l. apply INSET.
    liaW (set_size dom). 
  Qed.

  Lemma trav_prefix_step
        i (DOMsi: NOmega.lt_nat_l i (set_size dom)):
    iord_step G sc (trav_prefix steps i) (trav_prefix steps (S i)).
  Proof using RESP ENUM IORD_DOM.
    red. exists (steps i). do 2 red.
    splits; try by (red; eapply trav_prefix_r_closed; eauto; liaW (set_size dom)).
    apply seq_eqv_l. split.
    { eapply prefix_border; eauto. }
    eapply trav_prefix_ext; eauto.
  Qed.

  Definition tc_enum (i: nat): trav_label -> Prop  :=
    sim_clos G (trav_prefix steps i) ∪₁ init_tls G. 
  
  (* TODO: group similar lemmas about union with init_tls *)
  Lemma trav_prefix_init_tls_iord_coherent i
        (DOMi : NOmega.le (NOnum i) (set_size dom)):
    iord_coherent G sc (trav_prefix steps i ∪₁ init_tls G).
  Proof using RESP IORD_DOM ENUM.
    red. rewrite id_union, seq_union_r, dom_union.
    apply set_subset_union_l. split.
    { apply set_subset_union_r. left. eapply trav_prefix_r_closed; eauto. }
    unfold "iord". rewrite init_tls_EI at 1. basic_solver.
  Qed.

  Lemma tc_enum_tls_coherent WF i
      (DOMi: NOmega.le (NOnum i) (set_size dom)):
    tls_coherent G (tc_enum i). 
  Proof using ENUM DOM_EXEC.
    unfold tc_enum. split; [basic_solver| ].
    apply set_subset_union_l. split; [| basic_solver].
    erewrite sim_clos_mori.
    2: { apply trav_prefix_in_exec_tls; eauto. }
    pose proof (exec_tls_sim_coh WF). red in H. rewrite <- H. basic_solver. 
  Qed.

  Lemma trav_prefix_union_init_tls_coherent WF i
      (DOMi: NOmega.le (NOnum i) (set_size dom)):
    tls_coherent G (trav_prefix steps i ∪₁ init_tls G). 
  Proof using ENUM DOM_EXEC. 
    apply tls_coherent_defs_equiv. exists (trav_prefix steps i).
    split; [| basic_solver]. now apply trav_prefix_in_exec_tls.
  Qed. 

  Lemma trav_prefix_step_ext
        i (DOMsi: NOmega.lt_nat_l i (set_size dom)):
    iord_step G sc (trav_prefix steps i ∪₁ init_tls G)
              (trav_prefix steps (S i) ∪₁ init_tls G). 
  Proof using RESP IORD_DOM ENUM DOM_EXEC. 
    forward eapply trav_prefix_step as [l STEP]; eauto.
    red. exists l. do 2 red.
    splits; try by (apply trav_prefix_init_tls_iord_coherent; liaW (set_size dom)).
    do 2 red in STEP. desc. apply seq_eqv_l in STEP. desc.  
    apply seq_eqv_l. split.
    2: { rewrite STEP2. basic_solver. }
    apply set_compl_union. split; auto.
    apply set_disjoint_eq_r. eapply set_disjoint_mori; [reflexivity| ..].
    2: by apply init_exec_tls_disjoint.
    red. rewrite <- DOM_EXEC.
    forward eapply @trav_prefix_in_dom with (i := S i) as XX; eauto.
    rewrite <- XX. rewrite STEP2. basic_solver. 
  Qed. 

  Lemma sim_traversal_next WF CONS:
    forall i (DOMi: NOmega.lt_nat_l i (set_size dom)),
      (sim_clos_step G sc)^* (tc_enum i) (tc_enum (1 + i)). 
  Proof using RESP ENUM IORD_DOM DOM_EXEC.
    ins. unfold tc_enum.
    forward eapply init_tls_sim_coh as INIT_SCOH; eauto. red in INIT_SCOH.
    rewrite INIT_SCOH, <- !sim_clos_dist; auto.  
    apply iord_step_implies_sim_clos_step; auto.
    red. splits; try by (apply trav_prefix_union_init_tls_coherent; liaW (set_size dom)). 
    apply trav_prefix_step_ext; auto. 
  Qed.

  End IordEnum. 

  Lemma iord_enum_exists WF COMP WFSC CONS MF
        (IMM_FAIR: imm_s_fair G sc)
        (TB: fin_threads G)
        dom:
  exists (steps: nat -> trav_label),
    enumerates steps dom /\
    respects_rel steps iord⁺ dom. 
  Proof using.
    edestruct countable_ext with (s := dom) (r := ⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord⁺)
      as [| [steps [ENUM RESP]]].
    { eapply countable_subset; [| by apply set_subset_full_r].
      apply trav_label_countable. }
    { red. split.
      { rewrite inclusion_seq_eqv_l. by apply iord_acyclic. }
      red. intros ? ? ? ?%seq_eqv_l  ?%seq_eqv_l. desc.
      apply seq_eqv_l. split; auto. eapply transitive_ct; eauto. }
    { eapply iord_ct_fsupp; eauto. }
    { edestruct H. constructor. econstructor; vauto. }
    exists steps. splits; eauto.
    red. ins. apply RESP; auto.
    1, 2: by apply set_lt_size.
    apply seq_eqv_l. split; auto.
    apply enumeratesE' in ENUM. desc. apply INSET in DOMi.
    apply ct_begin in Rij. generalize Rij. unfold iord. basic_solver. 
  Qed.

  Lemma sim_traversal_inf WF CONS
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (TB: fin_threads G)
        (dom: trav_label -> Prop)
        (IORD_DOM: iord ⊆ dom × dom)
        (DOM_EXEC: dom ⊆₁ exec_tls G)
        (DOM_COVERS: eq ta_cover <*> (E \₁ is_init) ⊆₁ dom)
        (DOM_SIM_CLOSURE: forall (S: trav_label -> Prop) (S_DOM: S ⊆₁ dom),
            (@sim_clos G S) ⊆₁ dom):
    exists (sim_enum: nat -> (trav_label -> Prop)),
      ⟪INIT: sim_enum 0 ≡₁ init_tls G ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size dom)),
          tls_coherent G (sim_enum i)⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size dom)),
          (sim_clos_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
      ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i,
           NOmega.le (NOnum i) (set_size dom) /\
             (sim_enum i) (mkTL ta_cover e)⟫ /\
      ⟪DOM: forall i (DOMi: NOmega.le (NOnum i) (set_size dom)),
          sim_enum i ⊆₁ init_tls G ∪₁ dom⟫.
  Proof using.
    edestruct iord_enum_exists as [steps_enum [ENUM RESP]]; eauto.
    1, 2: by apply CONS.
    exists (tc_enum steps_enum). splits.
    { unfold tc_enum. rewrite trav_prefix_init.
      rewrite sim_clos_empty. basic_solver. }
    { apply tc_enum_tls_coherent; eauto. }
    { apply sim_traversal_next; auto. }
    { intros e Ee.
      pose proof ENUM as ENUM'. apply enumeratesE' in ENUM. desc.
      specialize (IND (mkTL ta_cover e)). specialize_full IND. 
      { apply DOM_COVERS. vauto. } 
      desc. exists (S i). split; [by vauto| ].  
      eapply set_equiv_exp. 
      { unfold tc_enum. rewrite trav_prefix_ext; eauto. }
      rewrite IND0. unfold sim_clos. basic_solver 10.  }
    ins. unfold tc_enum. rewrite set_unionC. apply set_subset_union; [done| ]. 
    rewrite <- DOM_SIM_CLOSURE; [reflexivity| ]. 
    eapply trav_prefix_in_dom; eauto.
  Qed.

  Lemma sim_traversal_inf_cip WF CONS
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (TB: fin_threads G) :
    exists (sim_enum: nat -> (trav_label -> Prop)),
      ⟪INIT: sim_enum 0 ≡₁ init_tls G ⟫ /\
      ⟪COH: forall i (DOMi: NOmega.le (NOnum i) (set_size (exec_tls_cip G))),
          tls_coherent G (sim_enum i)⟫ /\
      ⟪STEPS: forall i (DOMi: NOmega.lt_nat_l i (set_size (exec_tls_cip G))),
          (sim_clos_step G sc)^* (sim_enum i) (sim_enum (1 + i)) ⟫ /\
      ⟪ENUM: forall e (Ee: (E \₁ is_init) e), exists i,
           NOmega.le (NOnum i) (set_size (exec_tls_cip G)) /\
             (sim_enum i) (mkTL ta_cover e)⟫ /\
      ⟪DOM: forall i (DOMi: NOmega.le (NOnum i) (set_size (exec_tls_cip G))),
          sim_enum i ⊆₁ init_tls G ∪₁ exec_tls_cip G⟫.
  Proof using.
    forward eapply sim_traversal_inf with (dom := exec_tls_cip G) as TRAV; eauto.
    { apply dom_helper_3. rewrite <- restr_relE. apply iord_exec_tls_cip. }
    { unfold exec_tls_cip, exec_tls. rewrite !set_pair_alt. basic_solver 10. }
    { unfold exec_tls_cip, exec_tls. rewrite !set_pair_alt. basic_solver 10. }
    ins. rewrite exec_tls_cip_alt, set_minusE. apply set_subset_inter_r. split.
    { apply sim_clos_exec_tls; auto. rewrite S_DOM.
      rewrite exec_tls_cip_alt. basic_solver. }
    unfold sim_clos. repeat (apply set_subset_union_l; split).
    2, 3: unfold rmw_clos, rel_clos; iord_dom_solver. 
    rewrite S_DOM, exec_tls_cip_alt. basic_solver. 
  Qed.

  Lemma sim_traversal_inf_full WF CONS
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc)
        (TB: fin_threads G) :
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
    forward eapply sim_traversal_inf with (dom := exec_tls G) as TRAV; eauto.
    { rewrite iord_exec_tls. basic_solver. }
    { unfold exec_tls. basic_solver. }
    { ins. apply sim_clos_exec_tls; auto. }
    desc. eexists. splits; eauto. 
  Qed.

End IordTraversal.
