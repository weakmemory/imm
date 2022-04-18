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
Require Import travorder.TraversalOrder.
Require Import ImmFair.
Require Import AuxRel2.
Require Import SetSize.

Import ListNotations.
Set Implicit Arguments.

Section IordTraversal. 
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

  Definition init_tls :=
    (eq ta_cover ∪₁ eq ta_issue ∪₁ is_ta_propagate_to_G G) <*> (E ∩₁ is_init). 

  Definition exec_tls: trav_label -> Prop :=
   (eq ta_cover) <*> (E \₁ is_init) ∪₁
   (eq ta_issue ∪₁ is_ta_propagate_to_G G) <*> ((E \₁ is_init) ∩₁ W). 
  
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

  Lemma set_pair_alt {A B: Type} (Sa: A -> Prop) (Sb: B -> Prop ):
    Sa <*> Sb ≡₁ (fst ↓₁ Sa) ∩₁ (snd ↓₁ Sb). 
  Proof using. unfold set_pair. basic_solver. Qed.

  Lemma restr_rel_cross_inter {A: Type} (d1 d2 d: A -> Prop):
    (d1 ∩₁ d) × (d2 ∩₁ d) ≡ restr_rel d (d1 × d2).
  Proof using. basic_solver. Qed.  

  Lemma iord_exec_tls:
    iord ≡ restr_rel exec_tls iord.
  Proof using.
    rewrite restr_relE. apply dom_helper_3.
    unfold "iord", exec_tls.
    rewrite !set_pair_alt.
    rewrite set_interC with (s' := W), set_map_inter, <- set_interA.
    rewrite <- set_inter_union_l. rewrite restr_rel_cross_inter.
    apply restr_rel_mori; [basic_solver| ].
    unfold "SB", "RF", "FWBOB", "AR", IPROP, PROP.
    repeat apply inclusion_union_l; try basic_solver.
    all: unfolder; ins; destruct x, y; ins; desc; subst; intuition. 
  Qed.

  Section StepsEnum.
    
    Variable (steps: nat -> trav_label).
    Hypothesis (ENUM: enumerates steps exec_tls).
    Hypothesis (RESP: respects_rel steps iord⁺ exec_tls).

    Definition trav_prefix (i: nat) : trav_label -> Prop :=
      ⋃₁ j < i, eq (steps j).

    Lemma trav_prefix_iord_closed WF COMP WFSC CONS
          i (DOMi: NOmega.le (NOnum i) (set_size exec_tls)):
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
      destruct (set_size exec_tls); auto; simpl in *; lia. 
    Qed. 

    (* TODO: generalize to arbitrary enumerations? *)
    Lemma prefix_border i (DOMi: NOmega.lt_nat_l i (set_size exec_tls)):
      ~ trav_prefix i (steps i).
    Proof using ENUM.
      unfold trav_prefix. intros [j [LT EQ]]. 
      apply enumeratesE' in ENUM. cdes ENUM.
      forward eapply INJ; [| | apply EQ| lia]; auto. 
      eapply NOmega.lt_lt_nat; eauto.
    Qed.

    Lemma step_event_dom i (DOMi: NOmega.lt_nat_l i (set_size exec_tls)):
      (E \₁ is_init) (event (steps i)) /\
      (action (steps i) = ta_issue -> W (event (steps i))). 
    Proof using ENUM. 
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize_full INSET; eauto. red in INSET.
      destruct (steps i) as [a e]. unfolder in INSET. basic_solver. 
    Qed. 

    Lemma trav_prefix_ext i
          (DOMi: NOmega.lt_nat_l i (set_size exec_tls)):
      trav_prefix (S i) ≡₁ trav_prefix i ∪₁ eq (steps i).
    Proof using. 
      unfold trav_prefix.
      arewrite ((fun x => x < S i) ≡₁ (fun x => x < i) ∪₁ eq i).
      { unfolder. split; ins; lia. }
      rewrite set_bunion_union_l. basic_solver.
    Qed.
  End StepsEnum.

  Lemma iord_enum_exists WF COMP WFSC CONS MF
        (IMM_FAIR: imm_s_fair G sc):
    exists (steps: nat -> trav_label),
      enumerates steps exec_tls /\
      respects_rel steps iord⁺ exec_tls. 
  Proof using.
    edestruct countable_ext with (s := exec_tls) (r := ⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord⁺)
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
  
End IordTraversal. 

