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
Require Import AuxRel2.

Import ListNotations.

Set Implicit Arguments.



Section SimClosure.
  Context (G : execution) (sc : relation actid).
  Implicit Types (WF : Wf G) (COMP : complete G)
           (CONS : imm_consistent G sc)
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

(* TODO: move upper *)
Lemma tl_covered_single e:
  tl_covered (eq (mkTL ta_cover e)) ≡₁ eq e. 
Proof.
  unfold tl_covered. rewrite set_inter_absorb_r; basic_solver.
Qed.
  

  
Definition rmw_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover ∪₁ eq ta_issue) <*> codom_rel (<|tl_covered tc|> ;; rmw).

Definition rel_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover) <*> (Rel ∩₁ tl_issued tc).
  
Definition sim_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
  
Definition sim_coherent (tc : trav_label -> Prop) :=
  tc ≡₁ sim_clos tc.

Global Add Parametric Morphism : sim_clos with signature
       set_equiv ==> set_equiv as sim_clos_more.
Proof using.
  unfold sim_clos. ins. unfold rmw_clos, rel_clos, tl_issued, tl_covered.
  rewrite !set_pair_alt. rewrite H. basic_solver.
Qed.

(* TODO: move upper *)
Global Add Parametric Morphism : sim_clos with signature
       set_subset ==> set_subset as sim_clos_mori.
Proof using.
  unfold sim_clos. ins. unfold rmw_clos, rel_clos, tl_issued, tl_covered.
  rewrite !set_pair_alt. rewrite H. basic_solver.
Qed.

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

Lemma sim_clos_union (tc1 tc2: trav_label -> Prop):
  sim_clos (tc1 ∪₁ tc2) ≡₁ sim_clos tc1 ∪₁ sim_clos tc2. 
Proof using. 
  unfold sim_clos. rewrite rel_clos_dist, rmw_clos_dist. basic_solver. 
Qed. 

Lemma sim_clos_empty:
  sim_clos ∅ ≡₁ ∅. 
Proof.
  unfold sim_clos, rmw_clos, rel_clos, tl_issued, tl_covered.
  rewrite !set_pair_alt. basic_solver.
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

Lemma rel_rmw_clos_rmw (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  rel_clos (rmw_clos tc) ⊆₁ rmw_clos tc. 
Proof using.
  unfold rmw_clos, rel_clos. unfold tl_covered, tl_issued.
  rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3]. ins. subst x0. subst.
  splits; [by vauto| ]. repeat (eexists; eauto). 
Qed. 

Lemma rel_clos_idemp (tc: trav_label -> Prop):
  rel_clos (rel_clos tc) ⊆₁ rel_clos tc.
Proof using. 
  unfold rel_clos.
  unfold tl_issued. rewrite !set_pair_alt. unfolder. ins. desc.
  destruct y as [a1 e1], y0 as [a2 e2], x as [a3 e3].
  ins. subst. splits; eauto. 
Qed.

Lemma sim_clos_dist (tc1 tc2: trav_label -> Prop):
  sim_clos (tc1 ∪₁ tc2) ≡₁ sim_clos tc1 ∪₁ sim_clos tc2.
Proof. 
  unfold sim_clos. rewrite rmw_clos_dist, rel_clos_dist. basic_solver. 
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

(* TODO: move to lib *)
Lemma map_rel_seq_ext {A B : Type} (f : A -> B) (r r' : relation B)
      (SUR: forall b, exists a, f a = b):
  f ↓ r ⨾ f ↓ r' ≡ f ↓ (r ⨾ r'). 
Proof using. 
  split; [apply map_rel_seq| ].
  unfolder. ins. desc. specialize (SUR z). desc.
  exists a. vauto. 
Qed.

(* TODO: move to lib *)
Lemma set_map_codom_ext {A B : Type} (f : A -> B) (rr : relation B)
      (SUR: forall b, exists a, f a = b):
  codom_rel (f ↓ rr) ≡₁ f ↓₁ codom_rel rr. 
Proof using. 
  split; [apply set_map_codom| ].
  unfolder. ins. desc. specialize (SUR x0). desc.
  exists a. congruence. 
Qed.  


(* TODO: add to auto lib *)
Lemma event_sur:
  forall y : actid, exists x : trav_label, event x = y. 
Proof using. ins. exists (mkTL ta_cover y). vauto. Qed.

(* TODO: add to auto lib *)
Lemma action_sur:
  forall y : trav_action, exists x : trav_label, action x = y. 
Proof using. ins. exists (mkTL y (InitEvent tid_init)). vauto. Qed.

Lemma rmw_cover_simpl WF tc:
  codom_rel (event ↓ (⦗tl_covered tc⦘ ⨾ rmw)) ⊆₁
  codom_rel (⦗(tc ∩₁ action ↓₁ eq ta_cover)⦘ ⨾ event ↓ rmw). 
Proof using. 
  unfolder. ins. desc.
  do 2 red in H. desc. red in H. desc.
  destruct x as [a2 e2], x0 as [a1 e1], y as [a3 e3]. red in H2. ins. subst.
  eexists. splits; eauto. 
Qed.  

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
    destruct TCOH. rewrite <- tls_coh_init. unfold init_tls.
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
    unfold event, action. unfolder. ins. desc. destruct y; ins; vauto. } 
  
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
  apply iord_coh_implies_iord_simpl_coh in ICOH; auto. 
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
  arewrite ((ar ∪ rf ⨾ ppo ∩ same_loc) ^^ n ⊆ (ar ∪ rf ⨾ ppo ∩ same_loc)^*).
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

Lemma sim_clos_iord_simpl_rmw_clos WF CONS (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  dom_rel (iord_simpl G sc ⨾ ⦗rmw_clos tc⦘) ⊆₁ tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
Proof using.
  unfold iord_simpl. repeat case_union _ _. rewrite !dom_union.
  unfold rmw_clos. rewrite !set_pair_alt. 
  repeat (apply set_subset_union_l; split).
  5,6: iord_dom_solver.
  
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
      cdes CONS. rewrite wf_scD, wf_rmwD; eauto. unfold event, action. type_solver. }
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
    apply iord_coh_implies_iord_simpl_coh in ICOH; auto. rewrite <- ICOH at 2. 
    apply dom_rel_mori.
    rewrite set_interC, id_inter.
    unfold iord_simpl, SB. basic_solver 10. }
  { unfold RF. rewrite crE, seq_union_r, map_rel_union.
    rewrite !seqA, !seq_union_l. etransitivity.
    { apply dom_rel_mori. apply seq_mori; [reflexivity| ].
      apply union_mori; [reflexivity| ]. Unshelve. 2: exact (fun _ _ => False).
      rewrite wf_rfD, wf_rmwD; auto. unfold action, event. type_solver 10. }
    
    apply set_subset_union_r. left. apply set_subset_union_r. right.
    unfold action, event. iord_dom_unfolder. vauto. }
  { do 2 (apply set_subset_union_r; left).
    erewrite eqv_rel_mori with (x := _ ∩₁ _); [| red; intro; apply proj2].
    fold event action. rewrite <- set_map_codom_ext; [| apply event_sur].
    rewrite rmw_cover_simpl; auto.
    rewrite dom_rel_eqv_codom_rel.
    rewrite transp_seq, transp_eqv_rel, <- map_rel_transp.
    
    etransitivity; [| apply iord_simpl_coh_clos_refl].
    2: { eapply iord_coh_implies_iord_simpl_coh; eauto. } 

    apply dom_rel_mori.
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
  unfold AR. fold event action.
  rewrite ct_end, !seqA. unfold "ar" at 2.
  repeat rewrite seq_union_l with (r := ⦗W⦘).
  arewrite (sc ⨾ ⦗W⦘ ∪ rfe ⨾ ⦗W⦘ ⊆ ∅₂); [| rewrite union_false_l].
  { cdes CONS. rewrite (wf_scD Wf_sc), wf_rfeD; eauto. type_solver. }
  
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
    unfolder. ins. desc. destruct y. ins. vauto. }
  
  etransitivity; [| apply iord_coherent_AR_ext_cover]; auto.
  basic_solver 10.
Qed.

Lemma sim_clos_iord_simpl_rel_clos WF CONS (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc):
  dom_rel (iord_simpl G sc ⨾ ⦗rel_clos tc⦘) ⊆₁ tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
Proof using.  
  pose proof ICOH as ICOH'. apply iord_coh_implies_iord_simpl_coh in ICOH; auto.
  unfold rel_clos at 1. rewrite !set_pair_alt. unfold iord_simpl. fold action event.
  repeat (case_union _ _; rewrite dom_union; apply set_subset_union_l; split).
  all: try by iord_dom_solver. 
  { 
    unfold tl_issued, SB. unfolder. ins. desc. destruct x, y, y0; ins; vauto.
    left. left. 
    (* TODO: how to transform into this without unfolding? *)
    enough (dom_rel (⦗action ↓₁ eq ta_cover⦘ ⨾ (event ↓ (sb ∪ sc)^+)⨾ ⦗event ↓₁ Rel⦘ ⨾ ⦗action ↓₁ eq ta_issue⦘⨾ ⦗tc⦘) ⊆₁ tc) as ALT.
    { rewrite <- !id_inter in ALT. apply ALT.
      eexists. apply seq_eqv_lr. splits; basic_solver. }
    clear dependent a. clear dependent a0. clear H2.

    rewrite ct_end.
    rewrite map_rel_seq_insert_exact with (d := action ↓₁ eq ta_cover). 
    2: { ins. by exists (mkTL ta_cover b). }
    rewrite !seqA. 
    rewrite map_rel_union. repeat case_union _ _.
    erewrite union_mori with (y0 := ∅₂); [rewrite union_false_r| reflexivity| ].
    2: { unfold tl_issued. rewrite <- !id_inter.
         erewrite eqv_rel_mori with (x := _ ∩₁ _).
         2: { etransitivity; [| apply tlsc_I_in_W]; basic_solver. } 
         cdes CONS. rewrite (wf_scD Wf_sc). iord_dom_unfolder. type_solver. }
    rewrite dom_rel_helper_in with (r := _ ⨾ _ ⨾ _ ⨾ _ ⨾ ⦗tc⦘) (d := tc).
    2: { rewrite <- ICOH at 2. apply dom_rel_mori.
         transitivity (FWBOB G ⨾ ⦗tc⦘); [| unfold iord_simpl; basic_solver 10].
         unfold FWBOB. rewrite <- sb_to_w_rel_in_fwbob.
         iord_dom_unfolder. splits; vauto.
         forward eapply tlsc_I_in_W with (x := (ta_issue, d)) as I_W; eauto.
         { basic_solver. }
         eexists. splits; eauto. }
    rewrite <- !seqA. do 4 rewrite dom_seq. rewrite !seqA. rewrite seq_eqvC.
    rewrite rtE, map_rel_union. repeat case_union _ _. rewrite dom_union.
    apply set_subset_union_l. split; [iord_dom_solver| ].
    rewrite <- ICOH at 2. unfold iord_simpl, SB. basic_solver 10. }
  { unfold RF. rewrite crE, seq_union_r, map_rel_union. repeat case_union _ _.
    rewrite union_mori; [rewrite union_false_r| reflexivity| ].
    2: { rewrite wf_rfD; auto.
         unfold tl_issued. rewrite tlsc_I_in_W; eauto.
         iord_dom_unfolder. type_solver. }
    iord_dom_unfolder. left. left.
    do 2 red in d4. desc. destruct y; ins; vauto.
    unfolder in d4. desc. ins; vauto. } 
Qed. 

Lemma sim_clos_iord_coherent WF CONS (tc: trav_label -> Prop)
      (TCOH: tls_coherent G tc) (ICOH: iord_coherent G sc tc)
      :
      iord_coherent G sc (sim_clos tc). 
Proof using.
  apply iord_simpl_coh_implies_iord_coh; auto. 
  unfold sim_clos, iord_coherent.
  red. rewrite !id_union, !seq_union_r, !dom_union.
  do 2 (try (apply set_subset_union_l; split)). 
  { apply iord_coh_implies_iord_simpl_coh in ICOH; auto.
    rewrite ICOH. basic_solver. }
  { apply sim_clos_iord_simpl_rmw_clos; auto. }
  apply sim_clos_iord_simpl_rel_clos; auto.
Qed.

Lemma sim_clos_tls_coherent WF tc
      (TCOH: tls_coherent G tc):
  tls_coherent G (sim_clos tc). 
Proof.
  pose proof TCOH as TCOH'.
  apply tls_coherent_defs_equiv. apply tls_coherent_defs_equiv in TCOH.
  red in TCOH. desc.
  red. unfold sim_clos. exists (tc' ∪₁ rmw_clos tc ∪₁ rel_clos tc). split.
  2: { rewrite TCOH0 at 1. basic_solver. }
  repeat (apply set_subset_union_l; split); auto.
  { unfold rmw_clos, exec_tls. rewrite !set_pair_alt.
    arewrite (codom_rel (⦗tl_covered tc⦘ ⨾ rmw) ⊆₁ (E \₁ is_init) ∩₁ W).
    2: { basic_solver 10. }
    rewrite wf_rmwD, wf_rmwE, rmw_in_sb, no_sb_to_init; auto. basic_solver. }
  unfold rel_clos, exec_tls. rewrite !set_pair_alt.
  apply set_subset_union_r. left. apply set_subset_inter; [done| ].
  apply set_map_mori; [done| ]. unfold tl_issued.
  unfolder. ins. desc. split.
  { eapply tlsc_E in H0; eauto. vauto. }
  eintros INIT%init_pln; eauto. mode_solver. 
Qed. 

Lemma iord_coh_intermediate WF CONS tc s1 s2
      (ICOH: iord_coherent G sc tc)
      (ICOH2: iord_coherent G sc (tc ∪₁ s1 ∪₁ s2))
      (TCOH: tls_coherent G tc)
      (TCOH2: tls_coherent G (tc ∪₁ s1 ∪₁ s2))
      (NO_INTER: dom_rel (iord_simpl G sc ⨾ ⦗s1⦘) ∩₁ s2 ⊆₁ ∅):
  iord_coherent G sc (tc ∪₁ s1). 
Proof using.
  apply iord_simpl_coh_implies_iord_coh; auto.
  
  red. rewrite id_union, seq_union_r, dom_union.
  apply set_subset_union_l. split.
  { rewrite iord_coh_implies_iord_simpl_coh; auto using ICOH,TCOH. basic_solver. }
  
  apply iord_coh_implies_iord_simpl_coh in ICOH2; auto. 
  rewrite <- set_subset_union_r1, <- set_subset_union_r2 in ICOH2 at 1.
  rewrite set_subset_inter_exact in ICOH2. 
  rewrite set_inter_union_r, NO_INTER, set_union_empty_r in ICOH2.
  rewrite set_subset_inter_exact. auto. 
Qed.

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

Global Add Parametric Morphism : sim_clos_step with signature
       set_equiv ==> set_equiv ==> iff as sim_clos_step_more.
Proof using. ins. apply set_extensionality in H, H0. by subst. Qed.


Section ClosureSteps. 
Variable (tc: trav_label -> Prop). 
Variable (a: trav_action) (e: actid) .
Let lbl := (a, e). 

Let tc' := tc ∪₁ eq lbl. 
Let stc := sim_clos tc.
Let stc' := sim_clos tc'. 
Hypothesis (ICOH: iord_coherent G sc tc). 
Hypothesis (ICOH': iord_coherent G sc tc').
Hypothesis (TCOH: tls_coherent G tc). 
Hypothesis (TCOH': tls_coherent G tc'). 
Hypothesis (NEW: ~ tc lbl).

Hypothesis (WF : Wf G)
           (CONS : imm_consistent G sc).
  
Lemma ICOHs: iord_coherent G sc stc.
Proof using WF TCOH ICOH CONS.
  subst stc. apply sim_clos_iord_coherent; auto; apply CONS. 
Qed. 
Lemma ICOHs': iord_coherent G sc stc'.
Proof using WF TCOH' ICOH' CONS.
  subst stc'. apply sim_clos_iord_coherent; auto; apply CONS.
Qed. 
Lemma TCOHs: tls_coherent G stc.
Proof using WF TCOH. 
  subst stc. apply sim_clos_tls_coherent; auto; apply CONS. 
Qed. 
Lemma TCOHs': tls_coherent G stc'.
Proof using WF TCOH'. 
  subst stc'. apply sim_clos_tls_coherent; auto; apply CONS.
Qed. 

Section CoverClosure.
  Hypothesis COVER: a = ta_cover. 
  
  Lemma sim_clos_steps_cover_fence (FENCE: F e):
    sim_clos_step＊ stc stc'.
  Proof using WF TCOH' TCOH NEW ICOH' ICOH CONS COVER.
    rename e into f.
    generalize (set_equiv_refl2 stc),  (set_equiv_refl2 stc').
    unfold stc at 2, stc' at 2. unfold sim_clos, tc'.
    rewrite rmw_clos_dist, rel_clos_dist. 
    arewrite (rmw_clos (eq lbl) ≡₁ ∅).
    { apply set_subset_empty_r.
      unfold rmw_clos, tl_covered. subst lbl. 
      rewrite wf_rmwD; auto. iord_dom_unfolder; try type_solver. }
    assert (rel_clos (eq lbl) ⊆₁ eq lbl) as REL_LBL. 
    { unfold rel_clos, tl_issued. subst lbl. iord_dom_unfolder. }
    
    intros STC STC'. apply rt_step.
    do 2 red. splits; try by (subst stc stc'; apply sim_clos_sim_coherent; auto).
    exists [lbl]. simpl. rewrite COVER. 
    do 2 red. splits; try by (subst stc stc'; apply sim_clos_iord_coherent; auto).
    apply seq_eqv_l. split; [| rewrite STC, STC'; basic_solver].
    eapply set_equiv_compl; [apply STC| ].
    repeat (apply set_compl_union; split); try done.
    { unfold rmw_clos. subst lbl. apply set_disjoint_eq_r.
      rewrite wf_rmwD; auto. iord_dom_unfolder. type_solver. }
    unfold rel_clos. subst lbl. apply set_disjoint_eq_r.
    unfold tl_issued. rewrite tlsc_I_in_W; eauto.
    iord_dom_unfolder. type_solver.  
  Qed. 
    
  Lemma sim_clos_steps_cover_write (WRITE: W e):
    sim_clos_step＊ stc stc'.
  Proof using WF TCOH' TCOH NEW ICOH' ICOH CONS COVER. 
    rename e into w.
    remember (stc ∪₁ eq (mkTL ta_issue w)) as stc_w.

    assert (tc (mkTL ta_issue w)) as Iw.
    { apply iord_coh_implies_iord_simpl_coh in ICOH'; auto.
      specialize (@ICOH' (mkTL ta_issue w)). specialize_full ICOH'.
      { exists (mkTL ta_cover w). apply seq_eqv_r. split; [| red; basic_solver].
        apply hahn_inclusion_exp with (r := RF G); [unfold iord_simpl; basic_solver 10| ].
        red. apply seq_eqv_lr. splits; try by vauto. red. simpl.
        apply seq_eqv_l; auto. }
      do 2 red in ICOH'. destruct ICOH'; try done. vauto. }
    
    generalize (set_equiv_refl2 stc),  (set_equiv_refl2 stc').
    unfold stc at 2, stc' at 2. unfold sim_clos, tc'.
    
    rewrite rmw_clos_dist, rel_clos_dist.
    assert (rmw_clos (eq lbl) ≡₁ ∅) as NOWRMW.
    { unfold rmw_clos. rewrite wf_rmwD; auto. subst lbl.
      apply set_subset_empty_r. unfold tl_covered. iord_dom_unfolder; type_solver 10. }    
    rewrite NOWRMW, set_union_empty_r.
    assert (rel_clos (eq lbl) ⊆₁ eq lbl) as REL_CLOS.
    { unfold rel_clos. unfold tl_issued. subst lbl. iord_dom_unfolder. }
    intros STC STC'. 
    assert (stc' ≡₁ stc ∪₁ eq lbl) as STC'_ALT. 
    { rewrite STC, STC'. split; [| basic_solver].
      rewrite REL_CLOS. basic_solver. }
    
    destruct (classic (set_disjoint (rmw_clos tc ∪₁ rel_clos tc) (eq lbl))) as [NEWw | OLDw].
    2: { rewrite STC, STC'. 
         eapply set_equiv_rel_more; [reflexivity | | apply rt_refl].
         split; [| basic_solver]. rewrite REL_CLOS.
         edestruct @set_disjoint_not_eq_r as [SD _]. specialize (SD OLDw).
         apply set_subset_eq in SD. rewrite !SD. basic_solver. } 
    
    apply rt_step.
    do 2 red. splits; try by (subst stc stc'; apply sim_clos_sim_coherent; auto).
    exists [lbl]. simpl. rewrite COVER. 
    do 2 red. splits; try by (subst stc stc'; apply sim_clos_iord_coherent; auto).
    apply seq_eqv_l. split; [| done].
    eapply set_equiv_compl; [rewrite STC; apply set_unionA| ].
    apply set_compl_union; split; try done.
    by apply set_disjoint_eq_r. 
  Qed. 

  Lemma sim_clos_steps_cover_read (READ: R e):
    sim_clos_step＊ stc stc'.
  Proof using WF TCOH' TCOH NEW ICOH' ICOH CONS COVER. 
    generalize (set_equiv_refl2 stc),  (set_equiv_refl2 stc').
    unfold stc at 2, stc' at 2. unfold sim_clos, tc'.
    
    rename e into r. 
      
    assert (set_disjoint (rmw_clos tc ∪₁ rel_clos tc) (eq lbl)) as NCLOS.
    { apply set_disjoint_union_l. split.
      { unfold rmw_clos. rewrite set_pair_alt.
        rewrite wf_rmwD; auto. subst lbl.
        unfolder. ins. subst. type_solver. }
      unfold rel_clos. unfold tl_issued. iord_dom_unfolder. subst lbl. inv IN'.
      forward eapply tlsc_I_in_W with (x := (ta_issue, a1)) (tc := tc); eauto.
      all: type_solver. }

    rewrite rmw_clos_dist, rel_clos_dist.
    arewrite (rel_clos (eq lbl) ≡₁ ∅); [| rewrite set_union_empty_r]. 
    { apply set_subset_empty_r. unfold rel_clos, tl_issued. iord_dom_unfolder. } 

    unfold rmw_clos at 3. unfold lbl at 2.
    rename r into e. rewrite COVER, tl_covered_single. rename e into r.

    destruct (classic (dom_rel rmw r)) as [RMWr | NRMWr].
    2: { arewrite (codom_rel (⦗eq r⦘ ⨾ rmw) ≡₁ ∅). 
         { generalize NRMWr. basic_solver. }
         rewrite set_pair_alt, set_map_empty,set_inter_empty_r, set_union_empty_r.
         intros STC STC'. apply rt_step.
         do 2 red. splits; try by (subst stc stc'; apply sim_clos_sim_coherent).
         exists [mkTL ta_cover r]. simpl.
         do 2 red. splits; try by (subst stc stc'; apply sim_clos_iord_coherent).
         apply seq_eqv_l. split; [| rewrite STC, STC'; basic_solver].
         eapply set_equiv_compl; [rewrite STC; apply set_unionA| ].
         apply set_compl_union.
         rewrite <- COVER. unfold mkTL. fold lbl. split; auto.
         apply set_disjoint_eq_r; vauto. }
      
    forward eapply (functional_codom rmw r) as [w RMWD]; auto using wf_rmwf.
    pose proof (proj2 RMWD) as RMW. red in RMW. specialize (RMW w eq_refl).
    red in RMW. desc. apply seq_eqv_l in RMW as [<- RMW].
    rewrite RMWD.

    assert ((E \₁ is_init) r) as ENIr.
    { eapply same_relation_exp in RMW.
      2: { rewrite rmw_from_non_init, wf_rmwE; auto. }
      generalize RMW. basic_solver. }

    arewrite ((eq ta_cover ∪₁ eq ta_issue) <*> eq w ≡₁ eq (mkTL ta_issue w) ∪₁ eq (mkTL ta_cover w)).
    { rewrite set_pair_alt. split; try basic_solver 10.
      iord_dom_unfolder; intuition. }
      
    assert (~ tc (mkTL ta_cover w)) as NCw.
    { intros COVw. apply NEW.
      apply iord_coh_implies_iord_simpl_coh in ICOH; auto. apply ICOH.
      eexists. apply seq_eqv_r. split; eauto.
      red. do 4 apply unionA. left.
      red. subst lbl. apply seq_eqv_lr. splits; try by vauto.
      apply ct_step. left. apply rmw_in_sb; auto. }
      
    assert ((E \₁ is_init) w /\ W w) as (ENIw & Ww).
    { eapply same_relation_exp in RMW.
      2: { rewrite wf_rmwD, wf_rmwE, rmw_non_init_lr; auto. }
      unfolder in RMW. desc. subst. vauto. }

    assert (set_disjoint (event ↓₁ eq w) (rmw_clos tc)) as DISJW.
    { intros [?a w_] [=<-] INTER. red in INTER. red in INTER. desc.
      red in INTER0. desc. apply seq_eqv_l in INTER0. desc.
      forward eapply (wf_rmw_invf WF w r x) as ->; eauto.
      apply NEW. red in INTER0. unfolder in INTER0. desc.
      subst lbl. destruct y; ins; vauto. } 
      
    intros STC STC'.
    assert (stc' ≡₁ stc ∪₁ eq lbl ∪₁ (eq (mkTL ta_issue w) ∪₁ eq (mkTL ta_cover w))) as STC'_ALT.
    { rewrite STC, STC'. basic_solver 10. } 

    remember (stc ∪₁ eq lbl) as stc_r.
    assert (iord_coherent G sc stc_r) as ICOHsr.
    { rename r into e. generalize ICOHs, ICOHs', TCOHs, TCOHs'. ins. 
      rewrite STC'_ALT in *. subst stc_r. eapply iord_coh_intermediate; eauto.
      rewrite set_interC, <- dom_eqv1, id_union.
      unfold iord_simpl. repeat case_union _ _. repeat rewrite dom_union.
      subst lbl. rewrite COVER. 
      repeat (apply set_subset_union_l; split).
      all: try by iord_dom_solver.
      2: { cdes CONS. iord_dom_unfolder.
           edestruct sb_sc_acyclic with (x := b); eauto.
           apply ct_unit. exists a1. split; auto.
           left. inv d. apply rmw_in_sb; auto. }
      iord_dom_unfolder; [type_solver| ].
      cdes CONS. apply imm_s_hb.coherence_sc_per_loc in Cint.
      red in Cint. destruct (Cint a1). exists z. inv d. split.
      { apply rmw_in_sb; auto. }
      apply rf_in_eco; auto. }
    assert (tls_coherent G stc_r) as TCOHsr.
    { subst stc_r. apply tls_coherent_ext; auto using TCOHs.
      red. subst lbl. left. split; auto. }
    
    remember (stc_r ∪₁ eq (mkTL ta_issue w)) as stc_rw1.
    assert (iord_coherent G sc stc_rw1) as ICOHsrw1.
    { rename r into e. generalize ICOHs, ICOHs', TCOHs, TCOHs'. ins.
      rewrite <- set_unionA in STC'_ALT. rewrite STC'_ALT in *. 
      subst stc_rw1. eapply iord_coh_intermediate; eauto.
      rewrite set_interC, <- dom_eqv1.
      unfold iord_simpl. repeat case_union _ _. repeat rewrite dom_union.
      repeat (apply set_subset_union_l; split).
      all: try by iord_dom_solver.
      iord_dom_unfolder. inv d. inv d2.
      apply fwbob_in_sb in d0. edestruct sb_irr; eauto. }

    assert (iiord_step (ta_cover, w) stc_rw1 stc') as ISTEP'.
    { rename r into e. do 2 red. splits; auto using ICOHs'.
      apply seq_eqv_l. split. 
      2: { subst stc_rw1. rewrite STC'_ALT. basic_solver. }
      eapply set_equiv_compl; [rewrite Heqstc_rw1, Heqstc_r, STC; reflexivity| ].
      subst lbl. repeat (apply set_compl_union; split); try by vauto.
      { apply set_disjoint_eq_l.
        eapply set_disjoint_mori; [..| apply DISJW]; red; basic_solver. }
      { unfold rel_clos, tl_issued. intros [RCcw]. unfolder in H. desc.
        destruct y; ins. subst. 
        apply NEW.
        apply iord_coh_implies_iord_simpl_coh in ICOH; auto. apply ICOH.
        exists (ta_issue, w). apply seq_eqv_r. split; auto.
        red. do 3 left. right. red. apply seq_eqv_lr. splits; try by vauto.
        red. simpl. apply seq_eqv_r. split; auto.
        apply sb_to_w_rel_in_fwbob. apply rmw_in_sb in RMW; basic_solver. }
      intros [=]. type_solver. }

    destruct (classic (Rel w)) as [RELw | NRELw].
    { assert (~ tc (mkTL ta_issue w)) as NIw.
      { intros ISSw. apply NEW.
        apply iord_coh_implies_iord_simpl_coh in ICOH; auto. apply ICOH.
        eexists. apply seq_eqv_r. split; eauto.
        red. do 3 left. right.
        red. unfold lbl. apply seq_eqv_lr. splits; try by vauto. red. simpl.
        apply seq_eqv_r. split; auto.
        apply sb_to_w_rel_in_fwbob. apply seq_eqv_r. split; [| basic_solver].
        apply rmw_in_sb; auto. }

      apply rt_step. do 2 red. splits; try by (subst stc stc'; apply sim_clos_sim_coherent).
      exists [mkTL ta_cover r; mkTL ta_issue w; mkTL ta_cover w]. simpl.
      split; auto.
      exists stc_r. split.
      { do 2 red. splits; auto using ICOHs. apply seq_eqv_l. split; [|basic_solver].
        eapply set_equiv_compl; [rewrite STC; apply set_unionA| ].
        apply set_compl_union. split; try by vauto.
        rewrite <- COVER. by apply set_disjoint_eq_r. }
      
      exists stc_rw1. split; auto. 
      do 2 red. splits; auto. apply seq_eqv_l. split.
      2: { subst stc_rw1 stc_r. basic_solver. }
      eapply set_equiv_compl; [rewrite Heqstc_r, STC; reflexivity| ].
      subst lbl. repeat (apply set_compl_union; split); try by vauto.
      2: { by intros [?]. }
      apply set_disjoint_eq_l.
      eapply set_disjoint_mori; [..| apply DISJW]; red; basic_solver. }

    remember (stc ∪₁ eq (mkTL ta_issue w)) as stc_w1.
    assert (sim_coherent stc_w1) as SCOHw1.
    { red. subst stc_w1.
      (* TODO: remove WF premise? *)      
      rewrite sim_clos_dist; auto.
      arewrite (sim_clos stc ≡₁ stc).
      { symmetry. unfold stc at 2. apply sim_clos_sim_coherent; auto. }
      unfold sim_clos. split; [basic_solver| ].
      repeat (apply set_subset_union_l; split; try basic_solver).
      { unfold rmw_clos. unfold tl_covered. iord_dom_unfolder. } 
      unfold rel_clos. unfold tl_issued. iord_dom_unfolder. inv d0. }
    assert (iord_coherent G sc stc_w1) as ICOHw1.
    { assert (stc_rw1 ≡₁ stc_w1 ∪₁ eq lbl) as STCrw1.
      { subst stc_w1 stc_rw1 stc_r. basic_solver. }
      rewrite STCrw1 in *. subst stc_w1.
      eapply iord_coh_intermediate; eauto using ICOHs, TCOHs.
      { apply tls_coherent_ext; [| by vauto]. 
        apply tls_coherent_ext; [by apply TCOHs | ]. 
        red. right. split; [by vauto| ]. split; vauto. }
        
      rewrite set_interC, <- dom_eqv1. unfold iord_simpl.
      repeat case_union _ _. rewrite !dom_union. subst lbl a. 
      repeat (apply set_subset_union_l; split); try by iord_dom_solver.
      unfold FWBOB. iord_dom_unfolder. inv d2.
      red in d0. unfold union in d0. des.
      all: (apply seq_eqv_r in d0 || apply seq_eqv_l in d0); mode_solver. }
                                      
    enough (sim_clos_step^* stc stc_w1) as ISS_W_STEP. 
    { eapply rt_unit. eexists. split; [by apply ISS_W_STEP| ].
      do 2 red. splits; eauto.
      2: { unfold stc'. apply sim_clos_sim_coherent; auto. }
      exists [lbl; mkTL ta_cover w]. simpl. rewrite COVER. split; auto.
      exists stc_rw1. split; auto. 
      do 2 red. splits; auto. apply seq_eqv_l. split.
      2: { subst stc_rw1 stc_w1 stc_r. basic_solver. }
      eapply set_equiv_compl.
      { subst stc_w1. rewrite STC. reflexivity. }
      repeat (apply set_compl_union; split); try by vauto.
      all: apply set_disjoint_eq_r; eapply set_disjoint_mori; [..| apply NCLOS];
        red; basic_solver. }
          
    destruct (classic (stc (mkTL ta_issue w))) as [Iw | NIw].
    { subst. rewrite set_union_absorb_r; [apply reflexive_rt| basic_solver]. }
      
    apply rt_step. do 2 red. splits; auto.
    2: { unfold stc'. apply sim_clos_sim_coherent; auto. }
    exists [mkTL ta_issue w]. simpl. do 2 red. splits; auto using ICOHs.
    apply seq_eqv_l. split; subst; basic_solver. 
Qed. 

  Lemma sim_clos_steps_cover:
    sim_clos_step＊ stc stc'.
  Proof using WF TCOH' TCOH NEW ICOH' ICOH CONS COVER.
    pose proof (lab_rwf lab e) as LABe.
    des; auto using sim_clos_steps_cover_read,
      sim_clos_steps_cover_write,
      sim_clos_steps_cover_fence. 
  Qed.

End CoverClosure.


Section IssueClosure.
  Hypothesis ISSUE: a = ta_issue. 

  Lemma sim_clos_steps_issue:
    sim_clos_step＊ stc stc'.
  Proof using WF TCOH' TCOH ICOH' ICOH CONS ISSUE NEW.
    (* TODO: replace NEW with more general name  *)
    rename e into w. 
    assert (W w) as Ww.
    { replace w with (event lbl); auto. eapply (@tlsc_I_in_W _ tc'); eauto. 
      subst tc'. basic_solver. }
    assert (~ tc (mkTL ta_cover w)) as NCw.
    { intros Cw.
      forward eapply (@tlsc_w_covered_issued tc) as WCI; eauto.
      destruct NEW. specialize (WCI (mkTL ta_cover w)). specialize_full WCI.
      { basic_solver. }
      unfolder in WCI. desc. subst lbl. destruct y. ins. vauto. }
    
    assert (rmw_clos (eq lbl) ≡₁ ∅) as NO_RMWC.
    { apply set_subset_empty_r. unfold rmw_clos.
      rewrite set_pair_alt. erewrite wf_rmwD; eauto. 
      subst lbl. unfold tl_covered. type_solver. }

    generalize (set_equiv_refl2 stc),  (set_equiv_refl2 stc').
    unfold stc at 2, stc' at 2. unfold sim_clos, tc'.
    rewrite rmw_clos_dist, rel_clos_dist. rewrite NO_RMWC, set_union_empty_r.
    rewrite set_unionA with (s'' := _ ∪₁ _), set_unionC with (s := rmw_clos _).
    rewrite set_unionA with (s' := rel_clos _).

    arewrite (rel_clos (eq lbl) ≡₁ (event ↓₁ Rel) ∩₁ eq (mkTL ta_cover w)).
    { unfold rel_clos, tl_issued. rewrite set_pair_alt.
      red. subst lbl. split; unfolder; ins; desc; destruct x; ins. 
      { subst. vauto. }
      inv H0. splits; vauto. }
        
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

    intros STC STC'.
    assert (set_compl stc lbl) as LBL_NEW.
    { eapply set_equiv_compl; [apply STC| ]. subst lbl.
      repeat (apply set_compl_union; split); try basic_solver.
      { intros RMWC. eapply set_subset_empty_r; [apply NO_RMWC| ]; basic_solver. }
      unfold rel_clos, tl_issued, set_pair.
      red. rewrite ISSUE. intuition discriminate. Unshelve. econstructor; vauto. }
      
    destruct (classic (Rel w)) as [RELw | NRELw].
    2: { erewrite (proj1 (set_disjointE _ _)), set_union_empty_l in STC'; [|basic_solver].
         apply rt_step. red. red. splits.
         2, 3: subst stc stc'; by apply sim_clos_sim_coherent.
         exists [lbl]. simpl. rewrite ISSUE. do 2 red. splits.
         2, 3: by apply sim_clos_iord_coherent; auto; apply CONS.

         apply seq_eqv_l. split; auto. 
         rewrite STC, STC'. basic_solver. }
        
    rewrite set_inter_absorb_l in STC'; [| basic_solver].
    apply rt_step.
    do 2 red. splits; try by subst stc stc'; apply sim_clos_sim_coherent.
    exists [mkTL ta_issue w; mkTL ta_cover w]. simpl.
    split; [by vauto| ]. exists (stc ∪₁ eq (mkTL ta_issue w)).

    assert (stc' ≡₁ stc ∪₁ eq (mkTL ta_issue w) ∪₁ eq (mkTL ta_cover w)) as STC'_ALT.
    { rewrite STC, STC'. basic_solver 10. } 

    forward eapply iord_coh_intermediate with (tc := stc) as ICOHs_; eauto using TCOHs, ICOHs. 
    1, 2: rewrite <- STC'_ALT; rename w into e; auto using TCOHs', ICOHs'.
    { rewrite set_interC, <- dom_eqv1. unfold iord_simpl.
      repeat case_union _ _. rewrite !dom_union.
      repeat (apply set_subset_union_l; split); try by iord_dom_solver.
      iord_dom_unfolder. inv d. inv d2.
      edestruct sb_irr. eapply fwbob_in_sb; eauto. } 

    unfold iiord_step. split; red; splits; auto.
    all: try by subst stc stc'; apply sim_clos_iord_coherent; auto; apply CONS.
    { apply seq_eqv_l. split; basic_solver. }
    apply seq_eqv_l. split.
    2: { rewrite STC, STC'. basic_solver 10. } 
    apply set_compl_union. split; vauto.
    intros STC_LBL'. apply LBL_NEW.
    forward eapply tlsc_w_covered_issued with (x := (ta_cover, w))(tc := stc).
    1, 2: subst stc; eauto using sim_clos_iord_coherent, sim_clos_tls_coherent.
    { basic_solver. }
    unfolder. ins. desc. destruct y; ins; vauto.
Qed.
      
End IssueClosure.

End ClosureSteps. 
            
Lemma iord_step_implies_sim_clos_step WF CONS:
  restr_rel (tls_coherent G) iord_step ⊆ sim_clos ↓ sim_clos_step^*.
Proof using.
  unfolder; intros tc tc' (STEP & TCOH & TCOH').
  red in STEP. destruct STEP as [[a e] STEP]. 
  remember STEP as AA. clear HeqAA.
  do 2 red in AA. destruct AA as [AA [ICOHT ICOHT']].
  apply seq_eqv_l in AA. destruct AA as [COMPL AA].
  rewrite AA in *. clear dependent tc'.

  assert (iord_coherent G sc (sim_clos tc)) as SIMCOH.
  { apply sim_clos_iord_coherent; auto. }
  assert (sim_coherent (sim_clos tc)) as SIMSIM.
  { apply sim_clos_sim_coherent; auto. }

  destruct a.
  { now apply sim_clos_steps_cover. }
  { now apply sim_clos_steps_issue. }

  { apply rt_step.
    do 2 red. splits; auto.
    2: now apply sim_clos_sim_coherent.
    exists [(ta_propagate tid, e)].
    do 3 red. splits; auto.
    2: now apply sim_clos_iord_coherent.
    apply seq_eqv_l. splits.
    { unfold sim_clos.
      repeat (apply set_compl_union; split); auto.
      all: unfold rel_clos, rmw_clos, set_pair, tl_covered, tl_issued.
      all: clear; intros AA; desf; unfolder in AA; desf. }
    rewrite sim_clos_union.
    apply set_union_more; auto.
    unfold sim_clos.
    split; eauto with hahn.
    unfold rel_clos, rmw_clos, set_pair, tl_covered, tl_issued.
    clear. unfolder; ins; do 2 desf. }

  apply rt_step.
  do 2 red. splits; auto.
  2: now apply sim_clos_sim_coherent.
  exists [(ta_reserve, e)].
  do 3 red. splits; auto.
  2: now apply sim_clos_iord_coherent.
  apply seq_eqv_l. splits.
  { unfold sim_clos.
    repeat (apply set_compl_union; split); auto.
    all: unfold rel_clos, rmw_clos, set_pair, tl_covered, tl_issued.
    all: clear; intros AA; desf; unfolder in AA; desf. }
  rewrite sim_clos_union.
  apply set_union_more; auto.
  unfold sim_clos.
  split; eauto with hahn.
  unfold rel_clos, rmw_clos, set_pair, tl_covered, tl_issued.
  clear. unfolder; ins; do 2 desf.
Qed. 
  
End SimClosure.
