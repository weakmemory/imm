Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_bob.
Require Import AuxDef.
Require Import travorder.TraversalOrder.
Require Import ImmFair.
Require Import AuxRel2.
Require Import SetSize.

Import ListNotations.
Set Implicit Arguments.
    

Definition init_tls (G: execution):=
  (eq ta_cover ∪₁ eq ta_issue ∪₁ eq ta_reserve ∪₁ is_ta_propagate_to_G G) <*>
  (acts_set G ∩₁ is_init). 

Definition exec_tls (G: execution): trav_label -> Prop :=
  (eq ta_cover) <*> (acts_set G \₁ is_init) ∪₁
  (eq ta_issue ∪₁ eq ta_reserve ∪₁ is_ta_propagate_to_G G) <*> ((acts_set G \₁ is_init) ∩₁ is_w (lab G)). 

Definition exec_tls_cip (G: execution): trav_label -> Prop :=
  (eq ta_cover) <*> (acts_set G \₁ is_init) ∪₁
  (eq ta_issue ∪₁ is_ta_propagate_to_G G) <*> ((acts_set G \₁ is_init) ∩₁ is_w (lab G)). 

Record tls_coherent (G: execution) (tc: trav_label -> Prop): Prop :=
  {
    tls_coh_init: init_tls G ⊆₁ tc;
    tls_coh_exec: tc ⊆₁ init_tls G ∪₁ exec_tls G
  }.

Definition tls_coherent_alt (G: execution) (tc: trav_label -> Prop) :=
  exists tc', tc' ⊆₁ exec_tls G /\ tc ≡₁ init_tls G ∪₁ tc'. 

Lemma tls_coherent_defs_equiv (G: execution) (tc: trav_label -> Prop):
  tls_coherent G tc <-> tls_coherent_alt G tc. 
Proof using. 
  split; intros COH. 
  2: { red in COH. desc. split; rewrite ?COH0, ?COH; basic_solver. }
  destruct COH. red. exists (tc \₁ init_tls G). split.
  { rewrite tls_coh_exec0. basic_solver. }
  split; [| basic_solver]. 
  rewrite (set_split_complete (init_tls G) tc) at 1. basic_solver.
Qed.


Global Add Parametric Morphism G: (@tls_coherent G) with signature
       @set_equiv trav_label ==> iff as tls_coherent_more.
Proof using.
  ins.
  etransitivity; [apply tls_coherent_defs_equiv| ].
  etransitivity; [| symmetry; apply tls_coherent_defs_equiv].
  split; ins; red; red in H0; desc; exists tc'; [rewrite <- H | rewrite H]; auto.
Qed.


Section TLSCoherency. 
  Variable (G: execution) (sc: relation actid). 
  Variable (tc: trav_label -> Prop). 

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
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).

  Implicit Types (WF : Wf G) (COMP : complete G)
           (* (WFSC : wf_sc G sc) *)
           (* (CONS : imm_consistent G sc) *)
           (TCOH: tls_coherent G tc).

  Lemma tlsc_I_in_W WF TCOH:
    tc ∩₁ (action ↓₁ eq ta_issue) ⊆₁ event ↓₁ W. 
  Proof using .
    apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
    rewrite TC', set_inter_union_l. apply set_subset_union_l. split.
    { etransitivity; [red; intro; apply proj1| ].
      unfold init_tls. erewrite set_pair_alt, init_w; eauto. basic_solver. }
    rewrite INE. unfold exec_tls. rewrite !set_pair_alt.
    unfold action, event. unfolder. ins; desf; congruence.  
  Qed.
  
  Lemma tlsc_P_in_E thread (WF: Wf G) (TCOH: tls_coherent G tc) :
    tc ∩₁ (action ↓₁ eq (ta_propagate thread)) ⊆₁ event ↓₁ acts_set G. 
  Proof using. 
    apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
    rewrite TC', set_inter_union_l. apply set_subset_union_l. split.
    { etransitivity; [red; intro; apply proj1| ].
      unfold init_tls. erewrite set_pair_alt, init_w; eauto. basic_solver. }
    rewrite INE. unfold exec_tls. rewrite !set_pair_alt.
    unfold action, event. unfolder. ins; desf; congruence.  
  Qed.
  
  Lemma tlsc_P_in_W thread WF TCOH:
    tc ∩₁ (action ↓₁ eq (ta_propagate thread)) ⊆₁ event ↓₁ W. 
  Proof using. 
    apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
    rewrite TC', set_inter_union_l. apply set_subset_union_l. split.
    { etransitivity; [red; intro; apply proj1| ].
      unfold init_tls. erewrite set_pair_alt, init_w; eauto. basic_solver. }
    rewrite INE. unfold exec_tls. rewrite !set_pair_alt.
    unfold action, event. unfolder. ins; desf; congruence.  
  Qed. 

  Lemma exec_tls_ENI:
    exec_tls G ⊆₁ event ↓₁ (E \₁ is_init).
  Proof using. unfold exec_tls. rewrite !set_pair_alt. basic_solver. Qed.

  Lemma init_tls_EI:
    init_tls G ⊆₁ event ↓₁ (E ∩₁ is_init).
  Proof using. unfold init_tls. rewrite !set_pair_alt. basic_solver. Qed.

  Lemma tlsc_E WF TCOH:
    tc ⊆₁ event ↓₁ E.
  Proof using.
    destruct TCOH. rewrite tls_coh_exec0, exec_tls_ENI, init_tls_EI. basic_solver.
  Qed. 

  Lemma tls_coherent_ext TCOH lbl
        (ENI: exec_tls G lbl):
    tls_coherent G (tc ∪₁ eq lbl). 
  Proof using.
    destruct TCOH. split; try basic_solver.
  apply set_subset_union_l. split; auto. basic_solver.
  Qed. 
  
  Lemma exec_tls_cip_alt:
    exec_tls_cip G ≡₁ exec_tls G \₁ action ↓₁ eq ta_reserve. 
  Proof using. 
    unfold exec_tls_cip, exec_tls. rewrite !set_pair_alt.
    split; try basic_solver 10.
    rewrite set_minus_union_l.
    unfolder. ins. destruct x; ins; des; subst; splits; try by vauto.
    { right. splits; vauto. }
    do 2 red in H. desc. subst. right. splits; vauto. 
  Qed. 

  Lemma iord_exec_tls:
    iord G sc ≡ restr_rel (exec_tls G) (iord G sc).
  Proof using.
    rewrite restr_relE. apply dom_helper_3.
    unfold iord, exec_tls.
    rewrite !set_pair_alt.
    rewrite set_interC with (s' := W), set_map_inter, <- set_interA.
    rewrite <- set_inter_union_l. rewrite restr_rel_cross_inter.
    apply restr_rel_mori; [basic_solver| ].
    iord_parts_unfolder. 
    repeat apply inclusion_union_l; try basic_solver.
    all: unfolder; ins; destruct x, y; ins; desc; subst; intuition. 
  Qed.

  Lemma iord_exec_tls_cip:
    iord G sc ≡ restr_rel (exec_tls_cip G) (iord G sc).
  Proof using.
    rewrite restr_relE. apply dom_helper_3.
    rewrite exec_tls_cip_alt, set_minusE.
    rewrite restr_rel_cross_inter.
    split.
    { eapply iord_exec_tls; eauto. }
    do 2 red in H. desc. clear -H. unfolder in H. des.
    all: apply seq_eqv_lr in H as (X & _ & Y); red in X, Y; vauto;
      split; red; intros [=]; try congruence.
    all: do 2 red in Y; desc; congruence. 
  Qed. 

  Lemma init_exec_tls_disjoint:
    set_disjoint (init_tls G) (exec_tls G). 
  Proof using. unfold init_tls, exec_tls. iord_dom_unfolder. Qed. 

Lemma init_tls_tls_coherent : tls_coherent G (init_tls G). 
Proof using. apply tls_coherent_defs_equiv. exists ∅. basic_solver. Qed. 

Lemma tls_coherent_ext_union T1 T2
  (TCOH1: tls_coherent G T1)
  (EXEC2: T2 ⊆₁ init_tls G ∪₁ exec_tls G):
  tls_coherent G (T1 ∪₁ T2).
Proof using. 
  destruct TCOH1. split; try basic_solver.
  apply set_subset_union_l; auto.
Qed.         

End TLSCoherency. 
