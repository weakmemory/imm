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
Require Import ImmFair.
Require Import AuxRel2.
Require Import TraversalOrder.
Require Import travorder.IordTraversal.
Require Import AuxRel2.
(* Require Import SimTravClosure. *)


Import ListNotations.

Set Implicit Arguments.

Definition iord_coherent (G: execution) (sc: relation actid) (tc: trav_label -> Prop) 
  := dom_rel (iord G sc ;; <|tc|>) ⊆₁ tc.

Record tls_coherent (G: execution) (tc: trav_label -> Prop): Prop :=
  {
    tls_coh_init: init_tls G ⊆₁ tc;
    (* tls_coh_exec: tc \₁ event ↓₁ is_init ⊆₁ exec_tls G *)
    tls_coh_exec: tc ⊆₁ init_tls G ∪₁ exec_tls G
  }.

Definition tls_coherent_alt (G: execution) (tc: trav_label -> Prop) :=
  exists tc', tc' ⊆₁ exec_tls G /\ tc ≡₁ init_tls G ∪₁ tc'. 

Lemma tls_coherent_defs_equiv (G: execution) (tc: trav_label -> Prop):
  tls_coherent G tc <-> tls_coherent_alt G tc. 
Proof. 
  split; intros COH. 
  2: { red in COH. desc. split; rewrite ?COH0, ?COH; basic_solver. }
  destruct COH. red. exists (tc \₁ init_tls G). split.
  { rewrite tls_coh_exec0. basic_solver. }
  split; [| basic_solver]. 
  rewrite (set_split_complete (init_tls G) tc) at 1. basic_solver.
Qed.
    

Section CoherentConfigs. 
  Variable (G: execution) (sc: relation actid). 
  Variable (tc: trav_label -> Prop). 

  (* Hypothesis (FITS: fits_graph G tc).  *)
  (* Hypothesis (COH: iord_coherent G sc tc). *)
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
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).

  Implicit Types (WF : Wf G) (COMP : complete G)
           (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
           (TCOH: tls_coherent G tc)
           (ICOH: iord_coherent G sc tc).
  
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
  
  Lemma tlsc_P_in_W thread WF TCOH:
    tc ∩₁ (action ↓₁ eq (ta_propagate thread)) ⊆₁ event ↓₁ W. 
  Proof. 
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

  (* Lemma tlsc_E WF TCOH: *)
  (*   tc ⊆₁ event ↓₁ E.  *)
  (* Proof. Admitted.  *)

  Definition tlsI := tc ∩₁ (action ↓₁ eq ta_issue).
  Definition tlsC := tc ∩₁ (action ↓₁ eq ta_cover).

  
  Lemma tlsc_w_covered_issued TCOH ICOH:
    (* (* event ↑₁ (tc ∩₁ (action ↓₁ eq ta_cover)) ∩₁ W ⊆₁ event ↑₁ (tc ∩₁ (action ↓₁ eq ta_issue)). *) *)
    (* ts_covered ∩₁ W ⊆₁ ts_issued. *)

    (* tc ∩₁ (event ↓₁ W) ∩₁ (action ↓₁ eq ta_cover) ⊆₁ event ↓₁ (event ↑₁ (tc ∩₁ action ↓₁ eq ta_issue)). *)

    tlsC ∩₁ (event ↓₁ W) ⊆₁ event ↓₁ (event ↑₁ tlsI).
    (* (fun ae => mkTL ta_issue (event ae)) ↓₁ (tlsC ∩₁ (event ↓₁ W)) ⊆₁ tlsI. *)
  Proof using.
    destruct TCOH. unfold tlsC, tlsI.
    unfolder. ins. desc. destruct x as [a e]. ins. subst.
    
    exists (mkTL ta_issue e). splits; eauto.
    destruct (tls_coh_exec0 _ H) as [Il | EXl].
    { apply tls_coh_init0. split; [basic_solver| ]. 
      apply init_tls_EI in Il. auto. }
    red in ICOH. apply ICOH.     
    red. eexists. apply seq_eqv_r. split; eauto.
    red. apply exec_tls_ENI in EXl. red. splits; try by vauto.
    do 4 left. right. red. basic_solver 10. 
  Qed.


End CoherentConfigs. 



Section TravOrderConfig.
  Context (G : execution) (sc : relation actid).
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

(* Notation "'Rel'" := (is_rel lab). *)
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).

  
Definition iiord_step (tl : trav_label) : relation (trav_label -> Prop) :=
  restr_rel (iord_coherent G sc)
            (<|fun tc => set_compl tc tl|> ;;
             (fun tc tc' => tc' ≡₁ tc ∪₁ eq tl)).
  
Definition iord_step (tc tc' : trav_label -> Prop) :=
  exists tl, iiord_step tl tc tc'.

Definition tl_issued   tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_issue)).
Definition tl_covered  tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_cover)).
Definition tl_reserved tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_reserve)).
  
Definition rmw_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover ∪₁ eq ta_issue) <*> codom_rel (<|tl_covered tc|> ;; rmw).

Definition rel_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover) <*> (Rel ∩₁ tl_issued tc).
  
Definition sim_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
  
Definition sim_coherent (tc : trav_label -> Prop) :=
  tc ≡₁ sim_clos tc.

Definition isim_clos_step (tll : list trav_label)
  : relation (trav_label -> Prop) :=
  match tll with 
  | [tl] => iiord_step tl
  | [(ta_issue, e); (ta_cover, e')] =>
      (fun _ _ => e = e' /\ Rel e) ∩
      (iiord_step (ta_issue, e) ;; 
       iiord_step (ta_cover, e'))
  | [(ta_cover, e); (ta_cover, e')] =>
      (fun _ _ => rmw e e') ∩
      (iiord_step (ta_cover, e) ;; 
       iiord_step (ta_cover, e'))
  | [(ta_cover, e); (ta_issue, e'); (ta_cover, e'')] =>
      (fun _ _ => rmw e e' /\ e' = e'' /\ Rel e') ∩
      (iiord_step (ta_cover, e) ;; 
       iiord_step (ta_issue, e') ;;
       iiord_step (ta_cover, e''))
  | _ => fun _ _ => False
  end.
  
Definition sim_clos_step :=
  restr_rel sim_coherent 
            (fun tc tc' => exists tll, isim_clos_step tll tc tc').

Lemma rmw_clos_dist (tc1 tc2: trav_label -> Prop):
  rmw_clos (tc1 ∪₁ tc2) ≡₁ rmw_clos tc1 ∪₁ rmw_clos tc2. 
Proof. 
  unfold rmw_clos. rewrite !set_pair_alt. unfold tl_covered. basic_solver 10.
Qed. 

Lemma rel_clos_dist (tc1 tc2: trav_label -> Prop):
  rel_clos (tc1 ∪₁ tc2) ≡₁ rel_clos tc1 ∪₁ rel_clos tc2. 
Proof. 
  unfold rel_clos. rewrite !set_pair_alt. unfold tl_issued. basic_solver 10.
Qed. 

Lemma sim_clos_dist (tc1 tc2: trav_label -> Prop):
  sim_clos (tc1 ∪₁ tc2) ≡₁ sim_clos tc1 ∪₁ sim_clos tc2. 
Proof. 
  unfold sim_clos. rewrite rel_clos_dist, rmw_clos_dist. basic_solver. 
Qed. 

Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_equiv A ==> @set_equiv B ==> @set_equiv (A * B) as set_pair_more.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_subset A ==> @set_subset B ==> @set_subset (A * B) as set_pair_mori.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

Lemma rmw_clos_once WF (tc: trav_label -> Prop):
  rmw_clos (rmw_clos tc) ⊆₁ ∅.
Proof using. 
  unfold rmw_clos.
  unfold tl_covered. rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3].
  ins. subst x0 x1 z. subst.
  eapply wf_rmwD, seq_eqv_lr in H5, H1; eauto. type_solver. 
Qed.

Lemma rmw_rel_clos_none WF (tc: trav_label -> Prop) (TCOH: tls_coherent G tc):
  rmw_clos (rel_clos tc) ⊆₁ ∅.
Proof using.
  unfold rmw_clos, rel_clos. unfold tl_covered, tl_issued.
  rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3]. ins. subst x0. subst.
  forward eapply tlsc_I_in_W with (x := (ta_issue, e1)); eauto; [basic_solver| ].
  intros [=We1]. apply wf_rmwD, seq_eqv_lr in H1; eauto. type_solver.
Qed. 

Lemma rel_rmw_clos_rmw WF (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  rel_clos (rmw_clos tc) ⊆₁ rmw_clos tc. 
Proof using.
  unfold rmw_clos, rel_clos. unfold tl_covered, tl_issued.
  rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3]. ins. subst x0. subst.
  splits; [by vauto| ]. repeat (eexists; eauto). 
Qed. 

Lemma rel_clos_idemp WF (tc: trav_label -> Prop):
  rel_clos (rel_clos tc) ⊆₁ rel_clos tc.
Proof using. 
  unfold rel_clos.
  unfold tl_issued. rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3].
  ins. subst. splits; eauto. 
Qed.

Lemma sim_clos_sim_coherent WF (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  sim_coherent (sim_clos tc). 
Proof using.
  unfold sim_coherent.
  unfold sim_clos. split; [basic_solver 10| ].
  rewrite !rmw_clos_dist, !rel_clos_dist. 
  repeat (apply set_subset_union_l; split; try basic_solver).
  { rewrite rmw_clos_once; basic_solver. }
  { rewrite rmw_rel_clos_none; basic_solver. }
  { rewrite rel_rmw_clos_rmw; basic_solver. }
  rewrite rel_clos_idemp; basic_solver. 
Qed. 

Lemma map_rel_seq_ext {A B : Type} (f : A -> B) (r r' : relation B)
      (SUR: forall b, exists a, f a = b):
  f ↓ r ⨾ f ↓ r' ≡ f ↓ (r ⨾ r'). 
Proof. 
  split; [apply map_rel_seq| ].
  unfolder. ins. desc. specialize (SUR z). desc.
  exists a. vauto. 
Qed.

Lemma set_map_codom_ext {A B : Type} (f : A -> B) (rr : relation B)
      (SUR: forall b, exists a, f a = b):
  codom_rel (f ↓ rr) ≡₁ f ↓₁ codom_rel rr. 
Proof. 
  split; [apply set_map_codom| ].
  unfolder. ins. desc. specialize (SUR x0). desc.
  exists a. congruence. 
Qed.  

Lemma event_sur:
  forall y : actid, exists x : trav_label, y = event x. 
Proof. ins. exists (mkTL ta_cover y). vauto. Qed.

Lemma action_sur:
  forall y : trav_action, exists x : trav_label, y = action x. 
Proof. ins. exists (mkTL y (InitEvent tid_init)). vauto. Qed.

Lemma sim_clos_iord_coherent WF WFSC (tc: trav_label -> Prop)
      (ICOH: iord_coherent G sc tc)
      :
      iord_coherent G sc (sim_clos tc). 
Proof using.
  unfold sim_clos, iord_coherent.
  rewrite !id_union, !seq_union_r, !dom_union.
  repeat (apply set_subset_union_l; split).
  { red in ICOH. rewrite ICOH. basic_solver. }
  { unfold rmw_clos at 1. unfold iord.
    rewrite restr_relE. rewrite set_pair_alt.
    rewrite !seqA, <- id_inter.
    repeat case_union _ _. rewrite !dom_union.
    repeat (apply set_subset_union_l; split).
    { unfold SB.
      rewrite ct_end. erewrite <- map_rel_seq2; [| apply event_sur]. 
      rewrite map_rel_union. rewrite !seqA, seq_union_l.
      etransitivity.
      { apply dom_rel_mori.
        do 3 (apply seq_mori; [reflexivity| ]).
        apply union_mori; [reflexivity| ]. Unshelve. 2: exact (fun _ _ => False).
        rewrite wf_scD, wf_rmwD; eauto. unfold event, action. type_solver 10. }
      rewrite union_false_r. rewrite <- id_inter.
      
      (* ??  *)
      do 3 (erewrite eqv_rel_mori with (x := _ ↓₁ _ ∩₁ _); [| red; intro; apply proj2]). 
      (* ?? *)

      fold event action.
      rewrite <- set_map_codom_ext.
      2: { ins. pose proof (event_sur b). desc. eauto. }
      rewrite <- !seqA. rewrite dom_rel_eqv_codom_rel.
      rewrite <- map_rel_transp, transp_seq, transp_eqv_rel.
      rewrite !seqA. rewrite map_rel_seq_ext.
      (* TODO: add to db / list of hyps *)
      2: { ins. pose proof (event_sur b). desc. eauto. }
      sin_rewrite sb_transp_rmw; auto.
      foobar. 
Admitted.       


Section IssueClosure.
  Variable (tc: trav_label -> Prop). 
  Variable (e: actid).
  Let lbl := (ta_issue, e). 
  Let tc' := tc ∪₁ eq lbl. 
  Let stc := sim_clos tc.
  Let stc' := sim_clos tc'. 
  
  Hypothesis (ICOH: iord_coherent G sc tc). 
  Hypothesis (ICOH': iord_coherent G sc tc').
  Hypothesis (TCOH: tls_coherent G tc). 
  Hypothesis (TCOH': tls_coherent G tc'). 
  (* Hypothesis (TRAV_STEP : itrav_step G sc e tc tc').  *)
  Hypothesis (NISS: ~ tc lbl).
  (* Hypothesis (ISS: issuable G sc tc e). *)
  
  (* Let irel_crmw := I ∩₁ (is_rel lab) ∪₁ codom_rel (⦗C⦘ ⨾ rmw). *)
    
  Global Add Parametric Morphism : sim_clos with signature
      set_equiv ==> set_equiv as sim_clos_more.
  Proof using.
    unfold sim_clos. ins. unfold rmw_clos, rel_clos, tl_issued, tl_covered.
    rewrite !set_pair_alt. rewrite H. basic_solver.
  Qed.

  Global Add Parametric Morphism : sim_clos_step with signature
         set_equiv ==> set_equiv ==> iff as sim_clos_step_more.
  Proof using. ins. apply set_extensionality in H, H0. by subst. Qed.

  Global Add Parametric Morphism
         {A: Type} (r: relation (A -> Prop)):
    r with signature
         @set_equiv A ==> @set_equiv A ==> iff as set_equiv_rel_more. 
  Proof using. ins. apply set_extensionality in H, H0. by subst. Qed.

  
  Lemma trav_step_closures_isim_issue
        WF
        (* WFSC CONS COMP *)
    :
    (* same_trav_config {| *)
    (*     covered := *)
    (*     C *)
    (*       ∪₁ (I ∩₁ (fun a : actid => is_rel lab a) ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C; *)
    (*     issued := I ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ I *)
    (*   |} (sim_trav_closure G tc) -> *)
    (* same_trav_config {| *)
    (*     covered := *)
    (*     C *)
    (*       ∪₁ ((I ∪₁ eq e) ∩₁ (fun a : actid => is_rel lab a) *)
    (*                       ∪₁ codom_rel (⦗C⦘ ⨾ rmw)) \₁ C; *)
    (*     issued := I ∪₁ eq e ∪₁ codom_rel (⦗C⦘ ⨾ rmw) \₁ (I ∪₁ eq e) *)
    (*   |} (sim_trav_closure G tc') -> *)
    sim_clos_step＊ stc stc'.
  Proof using. 
    rename e into w.
    assert (W w) as Ww.
    { replace w with (event lbl); auto. eapply (@tlsc_I_in_W _ tc'); eauto. 
      subst tc'. basic_solver. }
    assert (~ tc (mkTL ta_cover w)) as NCw.
    { intros Cw. forward eapply (@tlsc_w_covered_issued _ _ tc) as WCI; eauto.
      destruct NISS. specialize (WCI (mkTL ta_cover w)). specialize_full WCI.
      { basic_solver. }
      unfolder in WCI. desc. subst lbl. destruct y. simpl in *. subst.
      red in WCI. unfolder in WCI. desc. simpl in *. congruence. }
    
  (*   rewrite set_inter_union_l, set_unionA. *)
  (*   rewrite set_unionC with (s := eq w ∩₁ _), <- set_unionA. *)
  (*   rewrite set_minus_union_l with (s' := eq w ∩₁ _). *)
  (*   rewrite set_minus_disjoint with (s1 := eq w ∩₁ _); [| basic_solver]. *)
  (*   rewrite <- set_minus_minus_l, set_unionA. *)
  (*   rewrite <- set_union_strict with (s1 := eq w). *)

    assert (rmw_clos (eq lbl) ≡₁ ∅) as NO_RMWC.
    { apply set_subset_empty_r. unfold rmw_clos.
      rewrite set_pair_alt. erewrite wf_rmwD; eauto. 
      subst lbl. unfold tl_covered. type_solver. }

    generalize (set_equiv_refl2 stc),  (set_equiv_refl2 stc').
    unfold stc at 2, stc' at 2. unfold sim_clos, tc'.
    rewrite rmw_clos_dist, rel_clos_dist. rewrite NO_RMWC, set_union_empty_r.
    rewrite set_unionA with (s'' := _ ∪₁ _), set_unionC with (s := rmw_clos _).
    rewrite set_unionA with (s' := rel_clos _).

    (***)
    arewrite (rel_clos (eq lbl) ≡₁ (event ↓₁ Rel) ∩₁ eq (mkTL ta_cover w)).
    { unfold rel_clos, tl_issued. rewrite set_pair_alt.
      red. subst lbl. split; unfolder; ins; desc; destruct x; ins. 
      { subst. vauto. }
      inv H0. splits; vauto. }
    (***)
        
    destruct (classic (codom_rel (⦗tl_covered tc⦘ ⨾ rmw) w)) as [CRMWw | NCRMWw].
    { apply set_subset_single_l in CRMWw. 
      rewrite set_union_absorb_l with (s := _ ∩₁ _).
      2: { unfold rel_clos, rmw_clos, tl_issued. rewrite !set_pair_alt.
           rewrite <- CRMWw. basic_solver. }
      rewrite set_unionA with (s' := eq _).
      rewrite set_union_absorb_l with (s := eq _).
      2: { apply set_subset_union_r. right. unfold rmw_clos.
           rewrite set_pair_alt. rewrite <- CRMWw. basic_solver. }
      intros -> ->. rewrite set_unionC with (s := rel_clos _), <- set_unionA.
      apply rt_refl. }
          
    destruct (classic (Rel w)) as [RELw | NRELw].
    2: { erewrite (proj1 (set_disjointE _ _)), set_union_empty_l; [|basic_solver].
         (* rewrite (proj1 (set_disjointE (eq w) Rel)); [| basic_solver]. *)
         (* rewrite set_union_empty_r. *)
         
         (* rewrite set_unionA with (s' := eq _), set_unionC with (s := eq _). *)
         (* rewrite <- !set_unionA.  *)
         intros STC STC'. 
         apply rt_step. red. red. splits.
         2, 3: subst stc stc'; by apply sim_clos_sim_coherent.
         exists [lbl]. simpl. red. red. 

         apply rlx_write_promise_step; auto.
         { simpl. intros [? | [?]]; basic_solver. }
         simpl. apply itrav_step_mon_ext_issue.
         { by fold tc tc'. }
         simpl. apply set_disjoint_eq_r. intros [? | [?]]; basic_solver. }
    
  (*   rewrite set_inter_absorb_r with (s := eq w); [| basic_solver]. *)
  (*   fold irel_crmw. *)
    
  (*   rewrite set_unionC with (s := eq w), <- !set_unionA. *)
  (*   intros STC STC'. rewrite <- STC, <- STC'. *)
  (*   apply rt_step. apply rel_write_step; auto. *)
  (*   { intros [r RMW]. apply NCRMWw. exists r. apply seq_eqv_l. split; auto. *)
  (*     cdes ISS. apply proj1, proj2 in ISS0. red in ISS0. apply ISS0. *)
  (*     red. exists w. apply seq_eqv_r. split; auto. *)
  (*     red. repeat left. apply seq_eqv_r. split; [| basic_solver]. *)
  (*     by apply rmw_in_sb. } *)
  (*   { simpl. intros [? | [?]]; basic_solver. } *)
  (*   { simpl. apply itrav_step_mon_ext_issue. *)
  (*     { by fold tc tc'. } *)
  (*     simpl. apply set_disjoint_eq_r. intros [? | [?]]; basic_solver. } *)
    
  (*   simpl. red. left. splits. *)
  (*   3, 4: simpl; basic_solver. *)
  (*   { simpl. unfold irel_crmw. intros [? | IC]; [by auto| ]. *)
  (*     red in IC. desc. destruct IC as [IC | IC]; auto. *)
  (*     destruct NISS. apply IC. } *)
  (*   simpl. apply coverable_add_eq_iff; auto. *)
  (*   simpl. apply covered_in_coverable; [| simpl; basic_solver]. *)
  (*   rewrite STC'. apply stc_coherent; auto. *)
  (* Qed. *)
  Admitted. 
  
End IssueClosure.

Lemma iord_step_implies_sim_clos_step :
  iord_step ⊆ sim_clos ↓ sim_clos_step^*.
Proof using.
  unfolder; intros tc tc' STEP.
  red in STEP. destruct STEP as [[a e] STEP]. 
  do 2 red in STEP. desc. apply seq_eqv_l in STEP. desc.

  destruct a.
  2: { replace tc' with (tc ∪₁ eq (ta_issue, e)) by admit. 
       apply trav_step_closures_isim_issue; auto. }
  

  (* use trav_step_closures_isim from SimTravClosure.v  *)
Admitted.
  

End TravOrderConfig.
