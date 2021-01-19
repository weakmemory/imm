Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_bob imm_s_ppo.
Require Import CombRelations.
Require Import AuxDef.
Require Import AuxRel2.
Require Import TraversalConfig.
Require Import imm_s_rfppo.

Set Implicit Arguments.

Section Traversal.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := (acts G).
  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'eco'" := (eco G).

  Notation "'bob'" := (bob G).
  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).
  Notation "'release'" := (release G).
  Notation "'sw'" := (sw G).
  Notation "'hb'" := (hb G).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := (S_tm G).
  Notation "'S_tmr'" := (S_tmr G).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'R_ex'" := (R_ex G).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

  Definition itrav_step e T T' :=
    ⟪ COVER :
      ⟪ NEXT : ~ covered T e ⟫ /\
      ⟪ COV  : coverable G sc T e ⟫ /\
      ⟪ COVEQ: covered T' ≡₁ covered T ∪₁ (eq e) ⟫ /\
      ⟪ ISSEQ: issued  T' ≡₁ issued  T ⟫
    ⟫ \/
    ⟪ ISSUE :
      ⟪ NISS : ~ issued T e ⟫ /\
      ⟪ ISS  : issuable G sc T e ⟫ /\
      ⟪ COVEQ: covered T' ≡₁ covered T ⟫ /\
      ⟪ ISSEQ: issued  T' ≡₁ issued  T ∪₁ (eq e) ⟫
    ⟫.

  Add Parametric Morphism : itrav_step with signature
      eq ==> same_trav_config ==> same_trav_config ==> iff as
          itrav_step_more.
  Proof using.
    intros e.
    unfold same_trav_config, itrav_step; ins; desf.
    rename y0 into y.
    split; ins; desf; simpls; unnw.
    all: first [rewrite <- H, <- H2, <- H0, <- H1 | rewrite H, H2, H0, H1].
    - assert (~ covered y e) by (intro; eapply NEXT, H; done).
      assert (coverable G sc y e ) by (eapply traversal_mon; [apply H| apply H2| done]).
      eauto 20.
    - assert (~ issued y e) by (intro; eapply NISS, H2; done).
      assert (issuable G sc y e).
      { eapply traversal_mon; [apply H|apply H2|done]. }
      eauto 20.
    - assert (~ covered x e) by (intro; eapply NEXT, H; done).
      assert (coverable G sc x e ) by (eapply traversal_mon; [apply H| apply H2| done]).
      eauto 20.
    - assert (~ issued x e) by (intro; eapply NISS, H2; done).
      assert (issuable G sc x e ) by (eapply traversal_mon; [apply H| apply H2| done]).
      eauto 20.
  Qed.

  Definition trav_step T T' := exists e, itrav_step e T T'.

  Definition traverse := clos_trans trav_step.

  Definition init_trav :=
    {| covered := Init ∩₁ E;
       issued := Init ∩₁ E;
    |}.

  Add Parametric Morphism : trav_step with signature
      same_trav_config ==> same_trav_config ==> iff as
          trav_step_more.
  Proof using.
    unfold trav_step; ins; desf.
    split; intros [e HH]; exists e.
    all: eapply itrav_step_more; eauto.
    all: by apply same_tc_Symmetric.
  Qed.

  Add Parametric Morphism : traverse with signature
      same_trav_config ==> same_trav_config ==> iff as
          traverse_more.
  Proof using.
    intros x y H x' y' H'; desf; unnw.
    split; intros IND;
      [generalize dependent y'; generalize dependent y |
       generalize dependent x'; generalize dependent x ];
      induction IND; ins.
    1,3: by apply t_step; eapply trav_step_more; eauto;
      apply same_trav_config_sym.
    all: eapply t_trans; [eapply IHIND1 | eapply IHIND2]; auto;
        eapply same_trav_config_refl.
  Qed.

  Lemma step_mon C C' (T : trav_step C C') :
  covered C ⊆₁ covered C' /\ issued C ⊆₁ issued C'.
  Proof using.
    destruct T as [e [STEP | STEP]]; auto.
    unnw; unfolder in *; basic_solver 21.
    unnw; unfolder in *; basic_solver 21.
  Qed.

  Lemma trav_step_coherence (C C' : trav_config) (T : trav_step C C')
        (H : tc_coherent G sc C):
    tc_coherent G sc C'.
  Proof using.
  assert (coverable G sc C ⊆₁ coverable G sc C' /\ issuable G sc C ⊆₁ issuable G sc C').
  by apply traversal_mon; apply step_mon; eauto.
  destruct T as [e [STEP | STEP]]; auto; unnw; desf.
  - unfold tc_coherent in *; splits; desf.
    unfolder in *; basic_solver 12.
    rewrite STEP1, <- H0; basic_solver 21.
    unfolder in *; basic_solver 12.
  - unfold tc_coherent in *; splits; desf.
    unfolder in *; basic_solver 12.
    rewrite STEP1, <- H0; basic_solver 21.
    rewrite STEP2, <- H1; basic_solver 21.
  Qed.
  
  Lemma trav_coherence (C C' : trav_config) (T : traverse C C')
        (H : tc_coherent G sc C):
    tc_coherent G sc C'.
  Proof using.
    apply clos_trans_tn1 in T.
    induction T; eapply trav_step_coherence; eauto.
  Qed.
  
  Lemma init_trav_coherent : tc_coherent G sc init_trav.
  Proof using WF IMMCON.
    unfold init_trav.
    red; splits; ins.
    { unfold coverable; ins.
      repeat (splits; try apply set_subset_inter_r).
      basic_solver.
      rewrite no_sb_to_init; unfold dom_cond; basic_solver.
      generalize (init_w WF); basic_solver 12. }
    unfold issuable; ins.
    repeat (splits; try apply set_subset_inter_r).
    { basic_solver. }
    { generalize (init_w WF); basic_solver 12. }
    { rewrite fwbob_in_bob, bob_in_sb, no_sb_to_init; unfold dom_cond; basic_solver. }
    eapply dom_cond_in with (r' := fun _ _ => False).
    rewrite id_inter. rewrite ct_end, !seqA.
    arewrite ((ar G sc ∪ rf ⨾ ppo ∩ same_loc) ⨾ ⦗Init⦘ ⊆ ∅₂).
    { by apply no_ar_rf_ppo_loc_to_init. }
    basic_solver.
  Qed.

(******************************************************************************)
(**  **   *)
(******************************************************************************)

  Lemma exists_next P e 
        (ACTS : E e)
        (N_COV : ~ P e) :
    exists e', sb^? e' e /\ next G P e'.
  Proof using.
    generalize dependent e.
    set (Q e := E e -> ~ P e ->
                exists e' : actid, sb^? e' e /\ next G P e').
    apply (@well_founded_ind _ sb (wf_sb G) Q).
    ins; subst Q; simpls.
    destruct (classic (exists e', sb e' x /\ ~ P e')) as
        [[e' [H' COV]]| H']; ins.
    { assert (E e') as ACTS.
      { apply seq_eqv_l in H'; desf. }
      specialize (H e' H' ACTS COV).
      destruct H as [z [X Y]].
      exists z; split; auto.
      right.
      red in X; desf.
      eapply sb_trans; eauto. }
    exists x; splits; [by left|]; red; splits; auto.
unfolder; splits; eauto.
unfold dom_cond; unfolder.
ins; desc; subst.
    destruct (classic (P x0)); auto.
    exfalso; apply H'; vauto.
  Qed.
  
  Lemma exists_trav_step T (TCCOH : tc_coherent G sc T)
        e (N_FIN : next G (covered T) e) :
    exists T', trav_step T T'.
  Proof using WF IMMCON.
    assert (wf_sc G sc) as WFSC by apply IMMCON.
    assert (complete G) as COM by apply IMMCON.

    rename e into e'.
    destruct (forall_not_or_exists (next G (covered T)) W)
      as [WNEXT|NWNEXT].
    { desf.
      destruct (classic (issued T e)).
      { exists (mkTC (covered T ∪₁ (eq e)) (issued T)).
        destruct T as [C I]; simpls.
        exists e; left; unnw; splits; simpls.
        { apply WNEXT. }
        unfold coverable. split; [by apply WNEXT|].
        left; unnw; basic_solver. }
      exists (mkTC (covered T) (issued T ∪₁ (eq e))).
      destruct T as [C I]; simpl in *.
      exists e; right; unnw; splits; simpls; try basic_solver.
      eapply issuable_next_w; eauto.
      by unfolder. }
    destruct (forall_not_or_exists (next G (covered T)) (coverable G sc T)) 
      as [COV|NCOV].
    { desf.
      exists (mkTC (covered T ∪₁ (eq e)) (issued T)).
      exists e; left; splits; simpls; auto.
      apply COV. }

    assert ((exists w, W w /\ ~ issued T w /\ E w) ->
            exists w, W w /\ ~ issued T w /\
                      dom_cond (⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) (issued T) w /\
                      E w) as WMIN.
    { intros P; desf.
      induction w using (well_founded_ind (wf_ar_rf_ppo_loc_ct WF COM IMMCON WFSC)).
      destruct (classic (dom_cond (⦗W⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺) (issued T) w)); eauto.
      unfolder in H0. unfold dom_rel in H0.
      apply not_all_ex_not in H0; desf.
      apply not_all_ex_not in H0; desf.
      eapply H; eauto. 
      cdes IMMCON.
      apply wf_ar_rf_ppo_loc_ctE in n3; auto. by destruct_seq_l n3 as AA. }

    assert ((exists f, (F∩₁Sc) f  /\ ~ covered T f /\ E f) ->
            exists f, (F∩₁Sc) f /\ ~ covered T f /\
                      doma (⦗F∩₁Sc⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗eq f⦘) (covered T) /\
                      E f) as FMIN.
    { intros P; desf.
      induction f using (well_founded_ind (wf_ar_rf_ppo_loc_ct WF COM IMMCON WFSC)).
      destruct (classic (doma (⦗F∩₁Sc⦘ ⨾ (ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗eq f⦘) (covered T)))
        as [H0 | H0]; eauto.
      rewrite seq_eqv_r, seq_eqv_l in H0.
      unfold doma in H0.
      apply not_all_ex_not in H0; desf.
      apply not_all_ex_not in H0; desf.
      apply imply_to_and in H0; desf.
      eapply H; eauto.
      cdes IMMCON.
      apply wf_ar_rf_ppo_loc_ctE in H2; auto. by destruct_seq_l H2 as AA. }

    assert (forall n, next G (covered T) n ->
                      R n \/ (F∩₁Sc) n) as RorF.
    { intros; destruct (lab_rwf lab n); auto.
      desf.
      { by apply NWNEXT in H. }
      right. split; auto.
      destruct (classic (is_sc lab n)) as [|NEQ]; [done|exfalso].
      set (NN := H).
      apply NCOV in NN.
      unfold coverable in NN.
      apply not_and_or in NN; desf; apply NN.
      { apply H. }
      right; split; auto.
      cdes IMMCON.
      unfold dom_cond. rewrite (wf_scD Wf_sc).
      type_solver. }
    
    assert (forall r, R r -> next G (covered T) r ->
                      ~ coverable G sc T r ->
      exists w, W w /\ rf w r /\ ~ issued T w) as WIS.
    { clear NCOV. intros r RR RNEXT NCOV.
      unfold coverable in NCOV.
      apply not_and_or in NCOV; desf.
      { exfalso; apply NCOV. apply RNEXT. }
      apply not_or_and in NCOV; desf.
      apply not_or_and in NCOV; desf.
      apply not_and_or in NCOV1; desf.
      assert (exists w, rf w r) as [w RF].
      { edestruct COM; esplit; eauto.
        apply RNEXT. }
      exists w; splits; auto.
      { apply (wf_rfD WF) in RF.
        apply seq_eqv_l in RF; desf. }
      intros II. apply NCOV1.
      intros x [y H]. apply seq_eqv_r in H; desf.
      assert (w = x); [|by subst].
      eapply (wf_rff WF); eauto. }

    destruct (forall_not_or_exists (next G (covered T)) R)
      as [RNEXT|NRNEXT].
    { desf.
      assert (exists w', W w' /\ ~ issued T w' /\ E w') as XW.
      { destruct (WIS e RNEXT0 RNEXT) as [w'].
        { eapply NCOV; eauto. }
        exists w'; splits; desf.
        apply wf_rfE in H0; auto.
        apply seq_eqv_l in H0; desf. }
      assert (WMIN := WMIN XW).
      clear XW.
      desf.
      assert (~ covered T w) as WNCOV.
      { intro H. apply WMIN0. 
          by apply (w_covered_issued TCCOH); split. }
      destruct (exists_next (covered T) w WMIN2 WNCOV) as [n NSB]; desf.
      destruct NSB as [HSB|HSB]; desf.
      { exfalso; eapply NWNEXT; eauto. }
      exists (mkTC (covered T) (issued T ∪₁ (eq w))).
      exists w; right; unnw; splits; simpls.

      set (nRorF := RorF).
      specialize (nRorF n NSB0).
      split; [split; [split|]|]; auto.
      intros x [y H]; desc; subst.
      apply seq_eqv_r in H. desc; subst.
      apply NNPP; intro COVX.
      
      assert (sb x y) as SBXY.
      { by apply bob_in_sb, fwbob_in_bob. }
      assert (sb^? n x) as NX.
      { destruct (eq_dec_actid n x) as [EQNX|NEQNX]; [by left|right].
        edestruct (sb_semi_total_r ) as [LL|RR]; eauto.
        { intros H'. apply COVX.
          apply TCCOH; vauto.
          apply (@wf_sbE G) in SBXY.
          unfolder in SBXY; basic_solver. }
        exfalso; apply COVX.
        eapply NSB0; basic_solver 12. }

      assert (fwbob⁺ n y) as BOB.
      { destruct NX as [NX|NX]; subst; [by apply t_step|].
        apply sb_fwbob_in_fwbob.
        eexists; eauto. }
      clear x H COVX NX SBXY.
      desf.
      { assert (NY := NSB0).
        apply NCOV in NSB0.
        unfold coverable in NSB0.
        apply not_and_or in NSB0; desf.
        { exfalso; apply NSB0. apply NY. }
        apply not_or_and in NSB0; desf.
        apply not_or_and in NSB0; desf.
        apply NSB2; unnw; split; auto.
        clear NSB0 NSB1 NSB2.
        red. intros x' [y' H'].
        apply seq_eqv_r in H'; desf.
        apply rfi_union_rfe in H'; destruct H' as [RFI|RFE].
        { destruct RFI as [RF SBXY].
          apply (w_covered_issued TCCOH); split.
          2: by eapply NY; eexists; apply seq_eqv_r; eauto.
          apply (wf_rfD WF) in RF.
          apply seq_eqv_l in RF; desf. }
        eapply WMIN1.
        eexists. apply seq_eqv_r. split; eauto.
        apply seq_eqv_l; split.
        { apply wf_rfeD in RFE; auto;
            apply seq_eqv_l in RFE; desf. }
        eapply ct_ct. exists y'.
        split.
        { apply t_step. left. by apply rfe_in_ar. }
        hahn_rewrite fwbob_in_bob in BOB.
        hahn_rewrite bob_in_ar in BOB.
        eapply clos_trans_mori.
        2: by apply BOB.
        basic_solver. }
      assert (exists f, (F∩₁Sc) f /\ ~ covered T f /\ E f) as FF.
      { exists n; splits; auto; apply NSB0. }
      specialize (FMIN FF); clear FF; desf.
      destruct (exists_next (covered T) f FMIN2 FMIN0) as [m MSB]; desf.
      destruct MSB as [MSB|MSB].
      { desf.
        specialize (NCOV f MSB0).
        apply NCOV. split.
        { apply MSB0. }
        right; split; auto.
        { type_solver. }
        intros x [z X]. apply seq_eqv_r in X; desf.
        eapply FMIN1.
        apply seq_eqv_l; split.
        { cdes IMMCON. apply (wf_scD Wf_sc) in X. apply seq_eqv_l in X; desf. }
        apply seq_eqv_r; split; auto.
        apply t_step. red. left. by apply sc_in_ar. }
      assert (R m) as RM.
      { specialize (RorF m MSB0).
        desf; auto.
        exfalso.
        destruct MSB0 as [MSB1 MSB2].
        apply MSB2.
        eapply FMIN1.
        hahn_rewrite seq_eqv_r.
        hahn_rewrite seq_eqv_l.
        splits; eauto.
        apply t_step. left. apply bob_in_ar.
        apply sb_to_f_in_bob.
        apply seq_eqv_r. split; auto.
        mode_solver. }
      destruct (WIS m RM MSB0) as [w' [WW [WRF WI]]].
      { by apply NCOV. }
      apply WI.
      eapply WMIN1.
      eexists. apply seq_eqv_r. splits; eauto.
      hahn_rewrite seq_eqv_l; splits; auto.

      assert ((ar G sc)⁺ w' f) as wfWF'.
      { apply rfi_union_rfe in WRF; destruct WRF as [[RFI SB]|RFE].
        { assert (sb w' f) as SB'.
          { eapply sb_trans; eauto. }
          apply t_step.
          apply (bob_in_ar sc).
          apply sb_to_f_in_bob.
          apply seq_eqv_r. split; auto.
          mode_solver. }
        eapply t_trans; apply t_step.
        { apply rfe_in_ar; eauto. }
        apply bob_in_ar.
        apply sb_to_f_in_bob.
        apply seq_eqv_r. split; auto.
        mode_solver. }
      assert ((ar G sc ∪ rf ⨾ ppo ∩ same_loc)⁺ w' f) as wfWF.
      { eapply clos_trans_mori.
        2: by apply wfWF'.
        basic_solver. }
      eapply t_trans; [apply wfWF|].
      apply rt_ct; exists n.
      split.
      2: eapply clos_trans_mori; [|by apply BOB].
      2: rewrite fwbob_in_bob; rewrite bob_in_ar; basic_solver.
      destruct (classic (f = n)) as [|FNEQ]; subst.
      { apply rt_refl. }
      apply rt_step. left. apply sc_in_ar.
      cdes IMMCON.
      edestruct wf_sc_total as [J|J]; eauto.
      { split; [split|].
        2,3: by apply FMIN.
        apply (dom_r (wf_sbE G)) in MSB.
        apply seq_eqv_r in MSB. desf. }
      { split; [split|].
        2,3: by apply nRorF.
        apply (dom_l (wf_sbE G)) in HSB.
        apply seq_eqv_l in HSB. desf. }
      exfalso.
      apply NSB0.
      eapply FMIN1.
      apply seq_eqv_l; split; auto.
      apply seq_eqv_r; split; eauto.
      apply t_step. left. by apply sc_in_ar. }

  assert (forall e, next G (covered T) e -> (F∩₁Sc) e) as FSC.
    { intros e H.
      specialize (NWNEXT e H); specialize (NCOV e H);
        specialize (NRNEXT e H).
      destruct (lab_rwf lab e) as [ | [| FF]]; vauto; split; auto.
      destruct (classic (Sc e)) as [SC|NSC]; auto.
      exfalso. apply NCOV; split.
      { apply H. }
      right; split; auto.
      unfold dom_cond. red.
      ins. destruct H0 as [y H0].
      apply seq_eqv_r in H0; desf.
      eapply wf_scD in H0.
      2: by apply IMMCON.
      apply seq_eqv_l in H0. destruct H0 as [_ H0].
      apply seq_eqv_r in H0.
      mode_solver. }
    assert (exists f', (F∩₁Sc) f' /\ ~ covered T f' /\ E f') as XF.
    { exists e'; splits; try by apply N_FIN.
        by apply FSC. }
    exfalso.
    destruct (FMIN XF) as [esc X]; desf.
    destruct (exists_next (covered T) esc X2 X0); desf.
    destruct H; desf.
    { eapply NCOV; eauto.
      split; [apply H0|].
      right; split; [by apply X|].
      intros x [y H]. eapply X1.
      apply seq_eqv_r in H; desf.
      apply seq_eqv_l; split.
      { eapply wf_scD in H.
        2: by apply IMMCON.
        apply seq_eqv_l in H; desf. }
      apply seq_eqv_r; split; auto.
      apply t_step. left. by apply sc_in_ar. }
    specialize (FSC _ H0).
    apply (NCOV _ H0). destruct TCCOH; desf. apply CC.
    rewrite seq_eqv_r, seq_eqv_l in X1.
    eapply X1.
    splits; eauto.
    apply t_step. left. apply bob_in_ar.
    apply sb_to_f_in_bob.
    apply seq_eqv_r. split; auto.
    mode_solver.
  Qed.

End Traversal.
