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
Proof using. 
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
           (SCPL: sc_per_loc G)
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
Proof using. 
  unfold rmw_clos. rewrite !set_pair_alt. unfold tl_covered. basic_solver 10.
Qed. 

Lemma rel_clos_dist (tc1 tc2: trav_label -> Prop):
  rel_clos (tc1 ∪₁ tc2) ≡₁ rel_clos tc1 ∪₁ rel_clos tc2. 
Proof using. 
  unfold rel_clos. rewrite !set_pair_alt. unfold tl_issued. basic_solver 10.
Qed. 

Lemma sim_clos_dist (tc1 tc2: trav_label -> Prop):
  sim_clos (tc1 ∪₁ tc2) ≡₁ sim_clos tc1 ∪₁ sim_clos tc2. 
Proof using. 
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
Proof using. 
  split; [apply map_rel_seq| ].
  unfolder. ins. desc. specialize (SUR z). desc.
  exists a. vauto. 
Qed.

Lemma set_map_codom_ext {A B : Type} (f : A -> B) (rr : relation B)
      (SUR: forall b, exists a, f a = b):
  codom_rel (f ↓ rr) ≡₁ f ↓₁ codom_rel rr. 
Proof using. 
  split; [apply set_map_codom| ].
  unfolder. ins. desc. specialize (SUR x0). desc.
  exists a. congruence. 
Qed.  

(* Lemma map_rel_eqv_ext [A B : Type] [f : A -> B] [d : B -> Prop] *)
(*       (SUR: forall b, exists a, f a = b): *)
(*   ⦗f ↓₁ d⦘ ≡ f ↓ ⦗d⦘. *)
(* Proof using. *)
(*   split; [apply map_rel_eqv| ]. *)
(*   unfolder. ins. desc. specialize (SUR x0). desc. *)
(*   exists a. congruence. *)
(* Qed. *)

Lemma event_sur:
  forall y : actid, exists x : trav_label, event x = y. 
Proof using. ins. exists (mkTL ta_cover y). vauto. Qed.

Lemma action_sur:
  forall y : trav_action, exists x : trav_label, action x = y. 
Proof using. ins. exists (mkTL y (InitEvent tid_init)). vauto. Qed.

(* Lemma rmw_cover_simpl WF tc *)
(*       (* (ICOH: iord_coherent G sc tc): *) *)
(*       : *)
(*       (* action ↓₁ eq ta_cover ∩₁ *) *)
(*              codom_rel (⦗tl_covered tc⦘ ⨾ rmw) ⊆₁ *)
(*       codom_rel (⦗event ↑₁ (tc ∩₁ action ↓₁ eq ta_cover)⦘ ⨾ rmw).  *)
(* Proof using.  *)
(*   unfolder. ins.  *)
(* Qed.   *)

Lemma rmw_cover_simpl WF tc
      (* (ICOH: iord_coherent G sc tc): *)
      :
      (* action ↓₁ eq ta_cover ∩₁ *)
             codom_rel (event ↓ (⦗tl_covered tc⦘ ⨾ rmw)) ⊆₁
      codom_rel (⦗(tc ∩₁ action ↓₁ eq ta_cover)⦘ ⨾ event ↓ rmw). 
Proof using. 
  unfolder. ins. desc.
  do 2 red in H. desc. red in H. desc.
  destruct x as [a2 e2], x0 as [a1 e1], y as [a3 e3]. red in H2. ins. subst.
  eexists. splits; eauto. 
Qed.  

(* Lemma rmw_cover_simpl WF tc *)
(*       (* (ICOH: iord_coherent G sc tc): *) *)
(*       : *)
(*       action ↓₁ eq ta_cover ∩₁ codom_rel (event ↓ (⦗tl_covered tc⦘ ⨾ rmw)) ⊆₁ *)
(*       codom_rel (⦗(tc ∩₁ action ↓₁ eq ta_cover)⦘ ⨾ event ↓ rmw).  *)
(* Proof using.  *)
(*   unfolder. ins. desc. *)
(*   do 2 red in H0. desc. red in H0. desc. *)
(*   destruct x as [a2 e2], x0 as [a1 e1], y as [a3 e3]. red in H3. ins. subst. *)
(*   eexists. splits; eauto.  *)
(* Qed.   *)

Lemma eqv_rel_alt {A: Type} (S: A -> Prop):
  ⦗S⦘ ≡ S × S ∩ eq.
Proof using. basic_solver. Qed.

Lemma icoh_clos_refl tc (ICOH: iord_coherent G sc tc):
  dom_rel ((iord G sc)^? ⨾ ⦗tc⦘) ⊆₁ tc. 
Proof using.
  rewrite crE, seq_union_l, seq_id_l, dom_union.
  red in ICOH. rewrite ICOH. basic_solver.
Qed.

Lemma set_compl_set_mapC {A B: Type} (d: B -> Prop) (f: A -> B):
  set_compl (f ↓₁ d) ≡₁  (f ↓₁ set_compl d).
Proof using. basic_solver. Qed. 

Lemma doma_alt {A: Type} (r: relation A) (d: A -> Prop):
  doma r d <-> dom_rel r ⊆₁ d. 
Proof using. unfolder. split; ins; basic_solver. Qed. 

Lemma sb_cr_tc_cover (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  ⦗action ↓₁ eq ta_cover⦘ ⨾ event ↓ sb^? ⨾ ⦗tc ∩₁ action ↓₁ eq ta_cover⦘ ⊆
  ⦗tc ∩₁ action ↓₁ eq ta_cover⦘ ⨾ event ↓ sb^? ⨾ ⦗tc ∩₁ action ↓₁ eq ta_cover⦘.
Proof using.
  rewrite crE, map_rel_union, seq_union_l. repeat case_union _ _.
  apply union_mori.
  { iord_dom_solver. }
  rewrite id_inter, seqA. apply doma_helper, doma_alt.
  rewrite set_split_complete with (s' := action ↓₁ _) (s := event ↓₁ is_init)at 1.
  rewrite id_union. repeat case_union _ _.
  rewrite dom_union. apply set_subset_union_l. split.
  { rewrite wf_sbE. rewrite <- map_rel_seq_ext; [| by apply event_sur].
    rewrite <- !seqA. do 3 rewrite dom_seq. 
    destruct TCOH. rewrite <- tls_coh_init0. unfold init_tls.
    rewrite set_pair_alt. unfolder. ins. desc. splits; vauto. }

  red in ICOH. rewrite <- ICOH at 2. apply dom_rel_mori.
  rewrite seq_eqvC. hahn_frame_r. unfold iord.
  rewrite !unionA, restr_union. etransitivity; [| apply inclusion_union_r1].
  rewrite id_inter. rewrite set_compl_set_mapC.
  rewrite seqA. rewrite <- seqA with (r2 := _ ↓ sb).   
  unfold SB. rewrite <- !restr_relE. rewrite restrC. apply restr_rel_mori; [done|].
  rewrite <- ct_step, <- inclusion_union_r1.
  rewrite wf_sbE, no_sb_to_init at 1. rewrite restr_relE. basic_solver. 
Qed. 


(* Lemma clos_trans_restr_sur {A B: Type} (r: relation B) (d: A -> Prop) (f: A -> B) *)
(*       (SUR_D: forall b, exists a, f a = b /\ d a): *)
(*   (* f ↓₁ r^* ≡ (f ↓₁ r)^*.  *) *)
(*   f ↓ r^* ≡ (f ↓ r)^*. *)
(* Proof using.  *)
(*   split. *)
(*   2: { rewrite rtEE. apply inclusion_bunion_l. ins. induction x. *)
(*        { simpl. basic_solver. } *)
(*        rewrite pow_S_end, IHx. rewrite map_rel_seq, rt_unit. reflexivity. } *)
(*   rewrite rtEE. apply inclusion_bunion_l. ins. induction x. *)
(*   { unfolder. ins. red in H0. desc.  *)

(* map_rel *)
(* Lemma map_rel_dom_exact {A B: Type} (f: A -> B) (r: relation B) (d: A -> Prop) *)
(*       (SUR_D: forall b, exists a, f a = b /\ d a): *)
(*   f ↓ r ≡ restr_rel d (f ↓ r).  *)
(* Proof using.  *)
(*   split; [| basic_solver 10].  *)
(*   unfolder. ins.  *)
  

(* Lemma map_rel_dom_exact {A B: Type} (f: A -> B) (r: relation B): *)
(*   @set_full A ≡₁ f ↓₁ (@set_full B). *)
(* Proof using. basic_solver. Qed. *)
  
Lemma map_rel_seq_insert_exact {A B: Type} (r1 r2: relation B)
      (f: A -> B) (d: A -> Prop)
      (SUR_D: forall b, exists a, f a = b /\ d a):
  f ↓ (r1 ⨾ r2) ⊆ f ↓ r1 ⨾ ⦗d⦘ ⨾ f ↓ r2. 
Proof using.
  unfolder. ins. desc.
  specialize (SUR_D z). desc. eexists. splits; eauto; congruence. 
Qed. 


(* Lemma ar_rf_ppo_loc_ct_coverable_issuable_in_I  : *)
    (* dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗coverable T ∪₁ issuable T⦘) ⊆₁ issued T. *)
(* Lemma ar_rf_ppo_loc_ct_tls_cov_tls_iss tc: *)
(*   dom_rel (event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) ⨾ ⦗tc ∩₁ action ↓₁ eq ta_cover⦘) ⊆₁ tc ∩₁ action ↓₁ eq ta_issue. *)
(* Proof using. *)
(*   rewrite map_rel_seq_insert_exact with (d := action ↓₁ eq ta_issue). *)
(*   2: { ins. exists (mkTL ta_issue b). vauto. } *)
(*   intros [a1 e1] [[a2 e2] REL%seq_eqv_r]. desc. *)
(*   destruct REL0 as [TC2 [=<-]]. *)
(*   red in REL. apply seq_eqv_l in REL as [We1 REL_CT]. ins.  *)

Lemma rel_map_bunionC {A B C: Type} (f: A -> B)
      (cdom: C -> Prop) (ss: C -> relation B):
  f ↓ (⋃ c ∈ cdom, ss c) ≡ (⋃ c ∈ cdom, f ↓ (ss c)).
Proof using. basic_solver. Qed. 

Lemma dom_rel_bunion {B C: Type}
      (cdom: C -> Prop) (ss: C -> relation B):
  dom_rel (⋃ c ∈ cdom, ss c) ≡₁ (⋃₁ c ∈ cdom, dom_rel (ss c)).
Proof using. basic_solver. Qed.

(* Lemma dom_rel_restr_relC {A: Type} (r: relation A) (d: A -> Prop): *)
(*   dom_rel (restr_rel d r) ≡ restr_rel d (d *)

Lemma restr_rel_seq_same {A: Type} (r1 r2: relation A) (d: A -> Prop)
      (DOMB1: domb (⦗d⦘ ⨾ r1) d):
  restr_rel d (r1 ⨾ r2) ≡ restr_rel d r1 ⨾ restr_rel d r2. 
Proof using.
  split; [| apply restr_seq].
  unfolder. unfolder in DOMB1. ins. desc.
  eexists. splits; eauto.
Qed. 

Definition iord_simpl : relation trav_label :=
  SB G sc ∪ RF G ∪ FWBOB G ∪ AR G sc ∪ IPROP G ∪ PROP G sc.

Definition E_ENI := E × (E \₁ is_init).

Lemma sb_E_ENI: sb ⊆ E_ENI. 
Proof using. rewrite wf_sbE, no_sb_to_init. basic_solver. Qed. 

Lemma co_E_ENI WF (SCPL: sc_per_loc G): co ⊆ E_ENI. 
Proof using. rewrite wf_coE, no_co_to_init; auto. basic_solver. Qed. 

Lemma rf_E_ENI WF : rf ⊆ E_ENI. 
Proof using. rewrite wf_rfE, no_rf_to_init; auto. basic_solver. Qed. 

Lemma fr_E_ENI WF (SCPL: sc_per_loc G) : fr ⊆ E_ENI. 
Proof using. rewrite wf_frE, no_fr_to_init; auto. basic_solver. Qed. 

Lemma no_ar_to_init_alt CONS WF:
  ar ≡ ar ⨾ ⦗set_compl is_init⦘. 
Proof using.
  forward eapply no_ar_to_init; eauto. basic_solver 10.
  Unshelve. all: eauto.
Qed. 

Lemma ar_E_ENI WF WFSC CONS : ar ⊆ E_ENI. 
Proof using. rewrite wf_arE, no_ar_to_init_alt; auto. basic_solver. Qed.

Lemma sc_E_ENI WF WFSC: sc ⊆ E_ENI. 
Proof using. rewrite wf_scE, (@no_sc_to_init _ WF _ WFSC); eauto. basic_solver. Qed.

Lemma E_ENI_trans: transitive E_ENI.
Proof using. unfold E_ENI. basic_solver. Qed.

Lemma iord_simpl_E_ENI WF WFSC CONS:
  iord_simpl ⊆ event ↓ E_ENI^?.
Proof using. 
  unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
  rewrite ppo_in_sb, fwbob_in_sb; auto. rewrite inclusion_inter_l1 with (r := sb).
  rewrite ?sb_E_ENI, ?rf_E_ENI, ?co_E_ENI, ?fr_E_ENI, ?ar_E_ENI, ?sc_E_ENI; auto.
  2: { cdes CONS. by apply imm_s_hb.coherence_sc_per_loc. }
  rewrite <- !seqA. 
  repeat (rewrite ?(@rt_of_trans _ E_ENI), ?(@rewrite_trans _ E_ENI),
           ?unionK, ?(@rewrite_trans _ E_ENI),
           ?(@rewrite_trans_seq_cr_cr _ E_ENI), ?(@ct_of_trans _ E_ENI)
         ); auto using E_ENI_trans.
  repeat rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r. basic_solver 10.
Qed.

(* Lemma iord_simpl_E_ENI_tc WF WFSC CONS tc: *)
(*   iord_simpl ⨾ ⦗tc⦘ ⊆ event ↓ E_ENI ∪ ⦗tc⦘.  *)
(* Proof using. *)
(*   rewrite iord_simpl_E_ENI; auto. rewrite crE, map_rel_union, seq_union_l. *)
(*   basic_solver 10.  *)

Lemma iord_simpl_tc_doma WF WFSC CONS tc (TCOH: tls_coherent G tc):
  doma (iord_simpl ⨾ ⦗tc⦘) (event ↓₁ E).
Proof using.
  rewrite iord_simpl_E_ENI; auto. rewrite crE, map_rel_union, seq_union_l.
  apply union_doma.
  { rewrite tlsc_E; eauto. unfolder. ins. desc. congruence. }
  unfold E_ENI. basic_solver.
Qed. 
  

Lemma iord_coh_simpl WF WFSC CONS tc
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  dom_rel (iord_simpl ⨾ ⦗tc⦘) ⊆₁ tc. 
Proof using.
  rewrite set_split_complete with (s' := dom_rel _) (s := event ↓₁ is_init).
  forward eapply iord_simpl_tc_doma as IS_DOM%doma_rewrite; eauto.

  apply set_subset_union_l. split.
  { rewrite IS_DOM.     
    destruct TCOH. rewrite <- tls_coh_init0 at 2. unfold init_tls.
    rewrite set_pair_alt, set_map_inter.
    rewrite <- set_interA. apply set_subset_inter; [| reflexivity].  
    rewrite dom_eqv1, set_interC. apply set_subset_inter; [| reflexivity].
    unfold iord_simpl. unfold SB, RF, FWBOB, AR, IPROP, PROP.
    basic_solver 10. }
  
  rewrite set_interC, <- dom_eqv1.
  red in ICOH. rewrite <- ICOH at 2. apply dom_rel_mori.
  unfold iord. fold iord_simpl.
  rewrite restr_relE. rewrite !seqA, seq_eqvC. 
  rewrite set_minusE, set_map_inter, id_inter.
  rewrite !seqA, seq_eqvC.
  rewrite <- seqA with (r3 := ⦗_⦘ ⨾ ⦗_⦘). rewrite <- seqA with (r2 := _ ⨾ ⦗tc⦘).
  rewrite set_compl_set_mapC.
  etransitivity.
  2: { apply seq_mori; [reflexivity| ].
       rewrite <- id_inter. apply domb_rewrite.
       rewrite iord_simpl_E_ENI; auto.
       rewrite crE, map_rel_union. repeat case_union _ _. apply union_domb.
       { rewrite (@tlsc_E G tc) at 1; eauto.
         unfolder. ins. desc. split; congruence. }
       unfold E_ENI. basic_solver. }
  apply doma_rewrite. rewrite IS_DOM. basic_solver.
Qed. 
       
Lemma iord_coherent_AR_ext_cover WF CONS tc
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  dom_rel (((⦗action ↓₁ eq ta_issue⦘ ⨾ event ↓ (⦗W⦘ ⨾
                (ar ∪ rf ⨾ ppo ∩ same_loc)^*) ⨾ ⦗action ↓₁ eq ta_cover⦘)) ⨾ ⦗tc⦘)
             ⊆₁ tc.
Proof using.
  rewrite rtEE. rewrite seq_bunion_r, rel_map_bunionC.
  repeat seq_rewrite seq_bunion_r. repeat seq_rewrite seq_bunion_l.
  rewrite dom_rel_bunion.
  apply set_subset_bunion_l. intros n _. induction n.
  { simpl. unfolder. ins. desc. destruct x, y; ins; vauto.
    forward eapply tlsc_w_covered_issued with (x := (ta_cover, a0)); eauto.
    { basic_solver. }
    unfold event, action, tlsI. unfolder. ins. desc. destruct y; ins; vauto. } 
  
  rewrite pow_S_end. rewrite <- seqA.
  arewrite (ar ∪ rf ⨾ ppo ∩ same_loc ⊆ (sb ∪ sc)^+ ∪ rfe ⨾ (sb ∪ sc)^*) at 2.
  { unfold "ar". rewrite rfi_union_rfe, inclusion_inter_l1.
    rewrite ppo_in_sb, ar_int_in_sb, rfi_in_sb; auto.
    case_union _ _. rewrite sb_sb. rewrite <- ct_step.
    repeat (apply inclusion_union_l); try basic_solver 10.
    apply inclusion_union_r2_search. hahn_frame.
    rewrite <- inclusion_union_r1. basic_solver. }
  repeat case_union _ _. rewrite map_rel_union. rewrite <- !seqA. rewrite seqA with (r2 := rfe). 
  rewrite map_rel_seq_insert_exact with (r2 := rfe ⨾ _) (d := action ↓₁ eq ta_issue). 
  2: { ins. exists (mkTL ta_issue b). vauto. }
  rewrite map_rel_seq_insert_exact with (d := action ↓₁ eq ta_cover) at 1.
  2: { ins. exists (mkTL ta_cover b). vauto. }
  apply iord_coh_simpl in ICOH; auto; [| by apply CONS]. 
  repeat case_union _ _. rewrite dom_union. apply set_subset_union_l. split.

  { erewrite dom_rel_mori.
    2: { rewrite !seqA. do 2 (apply seq_mori; [reflexivity| ]).
         rewrite <- seq_eqvK at 1. rewrite seqA. apply seq_mori; [reflexivity| ].  
         apply dom_rel_helper_in in ICOH. etransitivity; [| apply ICOH].
         unfold iord_simpl, SB. basic_solver 10. }
    rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
    erewrite dom_rel_mori; [by apply IHn| ]. basic_solver. }

  rewrite map_rel_seq_insert_exact with (r1 := rfe) (d := action ↓₁ eq ta_cover).
  2: { ins. exists (mkTL ta_cover b). vauto. }
  rewrite !seqA. erewrite dom_rel_mori.
  2: { do 4 (apply seq_mori; [reflexivity| ]).
       apply dom_rel_helper_in with (d := tc). 
       rewrite rtE, map_rel_union. repeat case_union _ _.
       rewrite dom_union. apply set_subset_union_l. split.  
       { iord_dom_solver. }
       etransitivity; [| by apply ICOH].
       unfold iord_simpl, SB. basic_solver 10. }
  rewrite <- !seqA. do 3 rewrite dom_seq. rewrite !seqA.
  erewrite dom_rel_mori.
  2: { do 2 (apply seq_mori; [reflexivity| ]). rewrite seq_eqvC.
       apply dom_rel_helper_in with (d := tc). 
       etransitivity; [| by apply ICOH]. apply dom_rel_mori. hahn_frame.
       transitivity (RF G); [| unfold iord_simpl; basic_solver 10]. 
       unfold RF. hahn_frame. 
       rewrite rfe_in_rf, (dom_l (wf_rfD WF)). basic_solver. }
  rewrite <- !seqA. do 3 rewrite dom_seq. rewrite !seqA, seq_eqvC.
  erewrite dom_rel_mori.
  2: { apply seq_mori; [reflexivity| ]. apply seq_mori; [| reflexivity].
       apply map_rel_mori; [done| ]. apply seq_mori; [reflexivity | ].
       apply pow_rt. }
  rewrite rtE. case_union _ _ . rewrite map_rel_union. repeat case_union _ _.
  rewrite dom_union. apply set_subset_union_l. split.
  { iord_dom_solver. }
  rewrite <- id_inter, set_interC.
  erewrite <- set_inter_absorb_r with (s := _ ∩₁ _); [| apply tlsc_I_in_W; eauto].
  rewrite set_interA, set_interC, !id_inter. 
  etransitivity; [| by apply ICOH]. apply dom_rel_mori. hahn_frame.
  transitivity (AR G sc); [| unfold iord_simpl; basic_solver 10].
  unfold AR. basic_solver 10.
Qed.   

Lemma iord_simpl_clos_implies_iord_clos WF WFSC (tc: trav_label -> Prop)
      (SIMPL_CLOS: dom_rel (iord_simpl ⨾ ⦗tc⦘) ⊆₁ tc):
  iord_coherent G sc tc. 
Proof using. 
  red. erewrite dom_rel_mori; [by apply SIMPL_CLOS| ].
  unfold iord, iord_simpl. basic_solver 10.
Qed.

Lemma iord_simpl_clos_refl WF WFSC CONS tc
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  dom_rel ((iord_simpl)^? ⨾ ⦗tc⦘) ⊆₁ tc. 
Proof using.
  rewrite crE, seq_union_l, seq_id_l, dom_union.
  red in ICOH. rewrite iord_coh_simpl; auto. basic_solver.
Qed.

Lemma sim_clos_iord_simpl_rmw_clos WF WFSC CONS (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      :
  dom_rel (iord_simpl ⨾ ⦗rmw_clos tc⦘) ⊆₁ tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
Proof using.
  unfold iord_simpl. repeat case_union _ _. rewrite !dom_union.
  unfold rmw_clos. rewrite !set_pair_alt. 
  repeat (apply set_subset_union_l; split). 
  
  { etransitivity; [| do 2 (apply set_subset_union_r; left); reflexivity].
    fold action event. unfold SB.
    rewrite ct_end at 1.
    erewrite <- map_rel_seq2.
    2: { ins. generalize (event_sur y). ins. desc. eauto. }
    rewrite map_rel_union. rewrite !seqA, seq_union_l.
    etransitivity.
    { apply dom_rel_mori.
      do 2 (apply seq_mori; [reflexivity| ]).
      apply union_mori; [reflexivity| ]. Unshelve. 2: exact (fun _ _ => False).
      rewrite wf_scD, wf_rmwD; eauto. unfold event, action. type_solver 10. }
    rewrite union_false_r. rewrite <- !id_inter.
    rewrite <- !set_interA.
    rewrite set_inter_absorb_r with (s' := _ ↓₁ (_ ∪₁ _)); [| basic_solver].
    
    rewrite <- set_map_codom_ext; [| apply event_sur].
    
    rewrite rmw_cover_simpl; auto.
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| red; intro; apply proj2].
    
    rewrite <- !seqA, dom_rel_eqv_codom_rel.
    
    rewrite transp_seq, <- map_rel_transp, !transp_eqv_rel.
    rewrite !seqA. seq_rewrite !map_rel_seq_ext; try by apply event_sur.
    rewrite seqA. sin_rewrite sb_transp_rmw; auto.
    
    arewrite ((sb ∪ sc)＊ ⨾ sb^? ⊆ (sb ∪ sc)＊).
    { rewrite crE, seq_union_r. apply inclusion_union_l; [basic_solver| ].
      rewrite <- rt_unit at 2. apply seq_mori; basic_solver. }
    rewrite rtE, map_rel_union. repeat case_union _ _. rewrite dom_union.
    apply set_subset_union_l. split.
    { iord_dom_solver. }
    apply iord_coh_simpl in ICOH; auto. rewrite <- ICOH at 2. apply dom_rel_mori.
    rewrite set_interC, id_inter.
    unfold iord_simpl, SB. basic_solver 10. }
  { unfold RF. rewrite crE, seq_union_r, map_rel_union.
    rewrite !seqA, !seq_union_l. etransitivity.
    { apply dom_rel_mori. apply seq_mori; [reflexivity| ].
      apply union_mori; [reflexivity| ]. Unshelve. 2: exact (fun _ _ => False).
      rewrite wf_rfD, wf_rmwD; auto. unfold action, event. type_solver 10. }
    
    apply set_subset_union_r. left. apply set_subset_union_r. right.
    unfold action, event. iord_dom_solver. vauto. }
  { do 2 (apply set_subset_union_r; left).
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| red; intro; apply proj2].
    fold event action. rewrite <- set_map_codom_ext; [| apply event_sur].
    rewrite rmw_cover_simpl; auto.
    rewrite dom_rel_eqv_codom_rel.
    rewrite transp_seq, transp_eqv_rel, <- map_rel_transp.
    
    etransitivity; [| apply iord_simpl_clos_refl; auto]. apply dom_rel_mori.
    unfold iord_simpl. 
    repeat rewrite unionA. etransitivity.
    2: { apply seq_mori; [| reflexivity]. apply clos_refl_mori.
         apply inclusion_union_r1. }
    unfold FWBOB, SB. rewrite fwbob_in_sb.
    rewrite inclusion_seq_eqv_r with (dom := W).
    rewrite inclusion_seq_eqv_r with (dom := action ↓₁ _) at 1.
    rewrite seqA. seq_rewrite map_rel_seq_ext; [| apply event_sur].
    rewrite sb_transp_rmw; auto.
    rewrite crE, map_rel_union. repeat case_union _ _. apply inclusion_union_l.
    { rewrite crE. case_union _ _ . etransitivity; [| apply inclusion_union_r1].
      iord_dom_solver; vauto. }
    rewrite crE. case_union _ _ . etransitivity; [| apply inclusion_union_r2].
    rewrite id_inter, seq_eqvC. hahn_frame.
    rewrite <- inclusion_union_r1. basic_solver. }
  { unfold AR. fold event action.
    rewrite ct_end, !seqA. unfold "ar" at 2.
    repeat rewrite seq_union_l with (r := ⦗W⦘).
    arewrite (sc ⨾ ⦗W⦘ ∪ rfe ⨾ ⦗W⦘ ⊆ ∅₂); [| rewrite union_false_l].
    { rewrite (wf_scD WFSC), wf_rfeD; eauto. type_solver. }
    
    rewrite ar_int_in_sb; auto. arewrite (ppo ∩ same_loc ⊆ sb) at 2.
    { rewrite ppo_in_sb; basic_solver. }
    rewrite <- cr_seq.
    
    arewrite (rf^? ⨾ sb ⊆ rfe^? ⨾ sb).
    { rewrite rfi_union_rfe. rewrite crE. repeat case_union _ _.
      rewrite rfi_in_sb, sb_sb. basic_solver. }
    rewrite <- seqA with (r2 := rfe^?). 
    erewrite inclusion_seq_trans with (r' := rfe^?); [| | reflexivity| ]. 
    2: { apply transitive_rt. }
    2: { rewrite <- inclusion_r_rt; [| reflexivity]. apply clos_refl_mori.
         unfold "ar". basic_solver. }
    
    rewrite <- seqA with (r1 := ⦗W⦘).
    rewrite map_rel_seq_insert_exact with (d := action ↓₁ eq ta_cover).
    2: { ins. by exists (mkTL ta_cover b). }
    
    rewrite <- set_map_codom_ext, rmw_cover_simpl at 1; auto; [|by apply event_sur].
    rewrite id_inter with (s := action ↓₁ _).
    rewrite <- !seqA, dom_rel_eqv_codom_rel.
    
    do 2 rewrite inclusion_seq_eqv_r.
    rewrite transp_seq, transp_eqv_rel, <- map_rel_transp.
    rewrite inclusion_seq_eqv_r with (dom := W). rewrite seqA.
    seq_rewrite map_rel_seq_ext; [| apply event_sur]. rewrite sb_transp_rmw; auto.
    rewrite seqA, sb_cr_tc_cover; auto.
    rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
    rewrite rtE. case_union _ _. rewrite map_rel_union.
    repeat case_union _ _. rewrite dom_union.
    
    etransitivity; [| rewrite set_unionA; apply set_subset_union_r1].
    apply set_subset_union_l. split.
    { unfolder. ins. desc. destruct x, y. ins. subst.
      forward eapply tlsc_w_covered_issued with (x := (ta_cover, a0)); eauto.
      { basic_solver. }
      unfold tlsI. unfolder. ins. desc. destruct y. ins. vauto. }
    
    etransitivity; [| apply iord_coherent_AR_ext_cover]; auto.
    basic_solver 10. }
  { iord_dom_solver. }
  iord_dom_solver.
Qed. 

Lemma sim_clos_iord_simpl_rel_clos WF WFSC (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      :
  dom_rel (iord_simpl ⨾ ⦗rel_clos tc⦘) ⊆₁ tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
Proof using.
Admitted. 

Lemma sim_clos_iord_coherent WF WFSC CONS (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      :
      iord_coherent G sc (sim_clos tc). 
Proof using.
  apply iord_simpl_clos_implies_iord_clos; auto. 
  unfold sim_clos, iord_coherent.
  rewrite !id_union, !seq_union_r, !dom_union.
  do 2 (try (apply set_subset_union_l; split)). 
  { rewrite iord_coh_simpl; auto. basic_solver. }
  { apply sim_clos_iord_simpl_rmw_clos; auto. }
  apply sim_clos_iord_simpl_rel_clos; auto.
Qed.

      

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
        WF CONS
        (* WFSC COMP *)
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
         exists [lbl]. simpl. do 2 red. splits.
         2, 3: by apply sim_clos_iord_coherent; auto; apply CONS.

         apply seq_eqv_l. split.
         2: { rewrite STC, STC'. basic_solver. } 
         eapply set_equiv_compl; [apply STC| ]. subst lbl.
         repeat (apply set_compl_union; split); try basic_solver.
         { intros RMWC. eapply set_subset_empty_r; [apply NO_RMWC| ].
           basic_solver. }
         apply set_subset_compl with (s := event ↓₁ Rel); auto.
         unfold rel_clos. rewrite set_pair_alt. basic_solver. }
             

    
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

Lemma iord_step_implies_sim_clos_step WF CONS:
  iord_step ⊆ sim_clos ↓ sim_clos_step^*.
Proof using.
  unfolder; intros tc tc' STEP.
  red in STEP. destruct STEP as [[a e] STEP]. 
  do 2 red in STEP. desc. apply seq_eqv_l in STEP. desc.

  destruct a.
  2: { eapply set_equiv_rel_more; [reflexivity | ..].
       { rewrite STEP2. reflexivity. }
       apply trav_step_closures_isim_issue; auto. }
  all: admit. 
Admitted.
  

End TravOrderConfig.
