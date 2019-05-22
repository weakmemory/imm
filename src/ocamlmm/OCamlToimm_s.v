(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section OCamlMM_TO_IMM_S.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'Einit'" := (E ∩₁ is_init).
Notation "'Eninit'" := (E \₁ is_init).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).

Notation "'detour'" := G.(detour).

Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(imm_s_hb.hb). (* ? clashes with OCaml's hb *)

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ar).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'ORlx'" := (fun a => is_true (is_only_rlx lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Notation "'ohb'" := G.(OCaml.hb).

Hypothesis LSM : forall l,
    << LM : Loc_ l \₁ is_init ⊆₁ ORlx >> \/
    << LM : Loc_ l \₁ is_init ⊆₁ Sc >>.

Hypothesis WSCFACQRMW : W∩₁Sc ≡₁ codom_rel (<|F∩₁ Acq|> ;; immediate sb ;; rmw).
Hypothesis RMWSC  : rmw ≡ ⦗Sc⦘ ⨾ rmw ⨾ ⦗Sc⦘.

Hypothesis WRLXF : W∩₁ORlx ⊆₁ codom_rel (<|F∩₁Acqrel|> ;; immediate sb).
Hypothesis RSCF  : R∩₁Sc  ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

Lemma sc_rf_sw (WF: Wf G):
    ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ sw. 
Proof.
  arewrite (Sc ⊆₁ Rel) at 1 by mode_solver.
  arewrite (Sc ⊆₁ Acq)      by mode_solver.
  unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
  rewrite !seqA.
  hahn_frame.
  rewrite (dom_l WF.(wf_rfD)) at 1.
  basic_solver 40.
Qed. 

Lemma sc_rf_pscb (WF: Wf G):
    ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ psc_base G. 
Proof.
  arewrite (rf ⊆ rf ∩ same_loc).
  { apply inclusion_inter_r; try basic_solver.
    apply WF.(wf_rfl). }
  rewrite <- seq_eqvK, !seqA.  
  arewrite (⦗Sc⦘ ⨾ rf ∩ same_loc ⨾ ⦗Sc⦘ ⊆ hb ∩ same_loc).
  { apply inclusion_inter_r.
    { rewrite inclusion_inter_l1. rewrite (sc_rf_sw WF). apply sw_in_hb. }
    basic_solver. }
  unfold psc_base. hahn_frame.
  arewrite (hb ∩ same_loc ⊆ scb G).
  basic_solver 10. 
Qed.

Lemma co_sc_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  <|Sc|> ;; co ;; <|Sc|> ⊆ hb.
Proof.
  rewrite fsupp_imm_t with (r:=⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘).
  4: { generalize WF.(co_trans). basic_solver. }
  3: { generalize WF.(co_irr). basic_solver. }
  2: { arewrite (⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘ ⊆ co) by basic_solver.
       rewrite WF.(wf_coE). unfold acts_set.
       red. ins. eexists. basic_solver. }
  
  assert (transitive hb) as THB by apply hb_trans.
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IPC. }
  assert (W ∩₁ Sc ⊆₁ codom_rel rmw) as WSCRMW. 
  { rewrite WSCFACQRMW. basic_solver. }
           
  apply inclusion_t_ind; auto.
  arewrite (immediate (⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘) ⊆ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⨾ sb).
  2: { arewrite (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ sw).
       2: { rewrite sw_in_hb, sb_in_hb.
            apply rewrite_trans; auto. }
       apply sc_rf_sw; auto. }
  rewrite (dom_r WF.(wf_coD)).
  rewrite !seqA.
  rewrite <- id_inter.
  rewrite WSCFACQRMW.
  intros w1 w2 [co_rmw_w1_w2 imm_w1_w2].
  apply seq_eqv_l in co_rmw_w1_w2.
  destruct co_rmw_w1_w2 as [SCW1 co_rmw_w1_w2].
  apply seq_eqv_r in co_rmw_w1_w2.
  destruct co_rmw_w1_w2 as [co_rmw_w1_w2 tmp].
  (* [f2 [r2 [FF2 rw_r2_w2]]] *)
  (* why "rewrite <- seqA in tmp." doesn't work here ? *)
  destruct tmp as [f2 tmp].
  rewrite <- seqA2 in tmp.
  destruct tmp as [r2 [SB_f2_r2 rw_r2_w2]]. 
  apply seq_eqv_l. split; auto.
  assert (Sc r2) as SCR2.
  { apply RMWSC in rw_r2_w2. generalize rw_r2_w2. basic_solver. }

  assert (E r2) as ER2.
  { apply (dom_l WF.(wf_rmwE)) in rw_r2_w2.
    generalize rw_r2_w2. basic_solver. }
  assert (R r2) as EW.
  { apply (dom_l WF.(wf_rmwD)) in rw_r2_w2.
    generalize rw_r2_w2. type_solver. }

  exists r2. split.
  2: { apply seq_eqv_l. split; auto.
       apply rmw_in_sb; auto. }
  assert (exists w', rf w' r2) as [w' RF].
  { apply IPC. split; auto. }
  destruct (classic (w1 = w')) as [|NEQ]; desf.

  assert (E w') as EW'. 
  { apply WF.(wf_rfE) in RF. generalize RF. basic_solver. }
  assert (W w') as WW'. 
  { apply WF.(wf_rfD) in RF. generalize RF. basic_solver. }
  
  set (GG := WW').
  apply is_w_loc in GG. desf.
  
  assert (loc r2 = Some l) as LOCR2.
  { rewrite <- GG. symmetry.
    apply wf_rfl; auto. }

  assert (same_loc_w1_w': same_loc w1 w').
  { red. rewrite GG. rewrite <- LOCR2.
    apply WF.(wf_col) in co_rmw_w1_w2. red in co_rmw_w1_w2.
    apply WF.(wf_rmwl) in rw_r2_w2. red in rw_r2_w2.
    symmetry in rw_r2_w2.
    apply (same_loc_trans co_rmw_w1_w2 rw_r2_w2). }
  
  assert (E w1) as EW1.
  { apply (dom_l WF.(wf_coE)) in co_rmw_w1_w2.
    generalize co_rmw_w1_w2. basic_solver. }
  assert (W w1) as WW1.
  { apply (dom_l WF.(wf_coD)) in co_rmw_w1_w2.
    generalize co_rmw_w1_w2. basic_solver. }
  
  destruct (classic (is_init w')) as [INIT|NINIT].
  { (* show a cycle: r2 -hb- w2 *)
    assert (co w' w1) as CO.
    { apply co_from_init; auto.
      unfolder. splits; eauto; desf. }
    exfalso.
    eapply atomicity_alt; eauto.
    { apply IPC. }
    split; eauto.
    do 2 (eexists; split; eauto). }

  assert (Sc w') as SCW'.
  { specialize (LSM l).
    destruct LSM as [CC|CC].
    2: { apply CC. split; auto. }
    exfalso.
    assert (~ is_init r2) as NINITR2.
    { eapply read_or_fence_is_not_init; eauto. }
    assert ((Loc_ l \₁ is_init) r2) as DD by (by split).
    apply CC in DD. clear -SCR2 DD. mode_solver. }

  assert (codom_rel rmw w') as RMWW'.
  { apply WSCRMW. by split. }

  eapply wf_co_total in NEQ; eauto.
  2,3: split; [split|]; auto.
  
  cdes IPC. cdes IC.
  exfalso.
  destruct NEQ as [NEQ|NEQ].
  2: { eapply atomicity_alt; eauto.
       split; eauto.
       do 2 (eexists; split; eauto). }
  apply imm_w1_w2 with (c:=w').
  { apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto.
    apply WSCFACQRMW. by split. }
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  2: { eexists. rewrite <- seqA2. eexists. split; eauto. }
  apply rf_rmw_in_co; auto.
  eexists. eauto.
Qed. 

Lemma ohb_in_hb (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ohb ⊆ hb.
Proof.
  unfold OCaml.hb.
  rewrite !seq_union_l, !seq_union_r.
  rewrite co_sc_in_hb; eauto.
  arewrite (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ sw).
  2: { rewrite sb_in_hb, sw_in_hb, !unionK.
       unfold imm_s_hb.hb. by rewrite ct_of_ct. }
  arewrite (⦗Sc⦘ ⊆ ⦗Rel⦘) at 1 by mode_solver.
  arewrite (⦗Sc⦘ ⊆ ⦗Acq⦘) by mode_solver.
  unfold imm_s_hb.sw. hahn_frame.
  rewrite (dom_l WF.(wf_rfD)) at 1.
  arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⊆ release).
  2: basic_solver 10.
  unfold imm_s_hb.release, imm_s_hb.rs.
  basic_solver 40.
Qed.
  
Lemma imm_to_ocaml_coherent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  irreflexive (ohb ;; (co ∪ fr)).
Proof.
  rewrite ohb_in_hb; eauto. 
  arewrite (co ∪ fr ⊆ eco^?).
  { rewrite co_in_eco, fr_in_eco. basic_solver. }
  apply IPC.
Qed.


Lemma sc_co_fr_ct_in_co_fr (WF: Wf G) :
  ⦗Sc⦘ ⨾ (co ∪ fr)⁺ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘.
Proof.
  hahn_frame.
  rewrite path_ut_first.
  unionL.
  { unionR left. apply ct_of_trans. apply WF. }
  arewrite (co＊ ⨾ fr ⊆ fr).
  { rewrite seq_rtE_l. unionL; [done|].
    sin_rewrite co_fr; auto. basic_solver. }
  rewrite seq_rtE_r.
  unionL; [basic_solver|].
  rewrite seqA.
  rewrite <- ct_begin. 
  rewrite path_ut_first.
  rewrite !seq_union_r.
  assert (fr ⨾ co⁺ ⊆ fr) as AA.
  { rewrite ct_of_trans; [|by apply WF].
      by rewrite WF.(fr_co). }
  arewrite (fr ⨾ co＊ ⊆ fr).
  { rewrite rtE, seq_union_r, seq_id_r. rewrite AA. by unionL. }
  arewrite (fr ⨾ fr ⊆ ∅₂) by apply WF.(fr_fr).
  rewrite AA. basic_solver.
Qed.


Lemma sc_scb_pscb: (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘ ⊆ psc_base G).
Proof. 
  unfold psc_base. basic_solver 10. 
Qed.

Lemma sl_mode (WF: Wf G) r (SL: r ⊆ same_loc):
  ⦗Eninit \₁ F⦘ ⨾ r ⨾ ⦗Eninit \₁ F⦘ ⊆ ⦗Sc⦘ ⨾ r ⨾ ⦗Sc⦘ ∪ ⦗ORlx⦘ ⨾ r ⨾ ⦗ORlx⦘.
Proof.
  red. intros x y H. 
Admitted.

Lemma wr_mode: Eninit ∩₁ (W ∪₁ R) ⊆₁ Sc ∪₁ ORlx.
Proof.
Admitted.


Lemma SC_RF (WF: Wf G): ⦗Sc⦘ ⨾ rf ⊆ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘.
Proof.
  arewrite (rf ≡ <|W|>;;rf;;<|R|>) at 1 by apply WF.(wf_rfD).
  arewrite (rf ≡ <|E|>;;rf;;<|E|>) at 1 by apply WF.(wf_rfE).
  arewrite (⦗Sc⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗Eninit \₁ F⦘ ⨾ ⦗Sc⦘).
  { rewrite <- !id_inter. apply eqv_rel_mori. red. intros x H.
    destruct H. split; auto. red. split; [| mode_solver ]. 
    red. split.
    { destruct H0. auto. }
    tertium_non_datur (is_init x); auto.
    exfalso. apply (init_pln WF) in H1. mode_solver. }
  rewrite <- id_inter. arewrite (E ∩₁ R ⊆₁ Eninit \₁ F).
  { red. intros x H. red. split.
    { destruct H. split; auto.
      apply (read_or_fence_is_not_init WF). auto. }
    mode_solver. }
  seq_rewrite seq_eqvC. 
  rewrite !seqA. sin_rewrite (sl_mode WF); [| apply WF.(wf_rfl) ]. 
  case_union _ _. unionL; [basic_solver| ].
  mode_solver. 
Qed.

Lemma SB_RF_SYNC (WF: Wf G): 
  ⦗Eninit \₁ (W ∪₁ R)⦘ ⨾ sb ⨾ rf ⊆ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rf ∪ rmw ⨾ rf.
Proof.
  arewrite (sb ⨾ rf ⊆ sb ⨾ ⦗Eninit ∩₁ (W ∪₁ R)⦘ ⨾ rf).
  { rewrite no_sb_to_init at 1.
    arewrite (rf ≡ ⦗E⦘ ⨾ rf) at 1 by eapply dom_l; apply WF.(wf_rfE). seq_rewrite seq_eqvC.
    arewrite (rf ≡ ⦗W⦘ ⨾ rf) at 1 by eapply dom_l; apply WF.(wf_rfD).
    arewrite (W ⊆₁ W ∪₁ R) at 1. basic_solver. }
  sin_rewrite wr_mode.
  rewrite (id_union Sc ORlx). repeat case_union _ _. unionL.
  2: { arewrite (rf ≡ ⦗W⦘ ⨾ rf) at 1 by eapply dom_l; apply WF.(wf_rfD).
       seq_rewrite <- id_inter. rewrite set_interC. sin_rewrite WRLXF.
       intros e r H. rewrite <- seqA2 in H. red in H.
       destruct H as [w [[e' [[EQee' [NIe WRe]] SBew]] H]].
       rewrite <- EQee' in SBew. clear EQee'.
       destruct H as [w' [[EQww' [f [f' [[EQff' FARf] SBIfw]]]] RFwr]].
       rewrite <- EQff' in SBIfw. clear EQff'.
       rewrite <- EQww' in RFwr. clear EQww'.
       pose same_thread.
       assert (sb e f) as SBef. 
       { admit. }
       left. 
       rewrite <- !seqA2. unfold seq at 1. exists w. split; auto.
       exists f. split.
       2: { generalize SBIfw. basic_solver. }
       exists f. split; auto. generalize FARf. basic_solver. }
  
  
Admitted. 




Lemma F_HB (WF: Wf G): ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rf ⨾ (rmw ⨾ rf)^* ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⊆ hb. 
Proof. 
  rewrite (dom_l WF.(wf_rfD)) at 1. rewrite !seqA.
  seq_rewrite <- rt_seq_swap. rewrite !seqA. 
  rewrite <- sw_in_hb. unfold imm_s_hb.sw.
  arewrite (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊ ⊆ release).
  2: { rewrite id_inter. sin_rewrite (r_step (sb ⨾ ⦗F⦘)). 
       arewrite (Acqrel ⊆₁ Acq) by mode_solver. }
  unfold imm_s_hb.release, imm_s_hb.rs.
  arewrite (⦗W⦘ ⨾ (rf ⨾ rmw)＊ ⊆ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊).
  { basic_solver 10. }
  arewrite (⦗F ∩₁ Acqrel⦘ ⨾ sb ⊆ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?); [|done].
  mode_solver 10.
Qed.

Lemma WIP_sc_sb_rf_ending_sb_ct_pscb (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  (⦗Sc ∩₁ (W ∪₁ R)⦘ ⨾ (sb ⨾ rf)＊ ⨾ sb ⨾ ⦗(W ∪₁ R) ∩₁ Sc⦘ ⊆ (psc_base G)^+).
Proof.
  rewrite <- sc_scb_pscb. (* cannot arewrite *)
  
  rewrite seq_rtE_l, seq_union_r. unionL.
  { arewrite (sb ⊆ scb G).
    rewrite <- ct_step. 
    basic_solver. }
  pose ct_end as CE. symmetry in CE. seq_rewrite CE.
  rewrite !id_inter, !seqA.
  
  arewrite (⦗W ∪₁ R⦘ ⨾ (sb ⨾ rf)⁺ ⊆ ⦗W ∪₁ R⦘ ⨾ (⦗W ∪₁ R⦘ ⨾ sb ⨾ rf)⁺).
  { rewrite ct_rotl at 1.
    assert (rf ≡ rf ⨾ ⦗R⦘) as RF_R. 
    { eapply dom_r. rewrite WF.(wf_rfD) at 1. auto. }
    rewrite RF_R at 1. (* how to (a)rewrite at two places ?*)
    arewrite (R ⊆₁ W ∪₁ R) at 2.
    rewrite <- seq_eqvK at 1. rewrite seqA at 1.
    rewrite <- (seqA _ sb _). 
    rewrite <- ct_rotl. basic_solver 10. }
  
  sin_rewrite SB_RF_SYNC. 
    
  assert (sb ⨾ rf ⨾ ⦗Sc⦘ ⊆ sb ⨾ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘) as SB_RF_SC by admit. 
  assert (rmw ⨾ rf ⊆ ⦗Sc⦘ ⨾ hb ∩ same_loc ⨾ ⦗Sc⦘) as RMW_RF_HBL.
  { rewrite RMWSC, !seqA, (SC_RF WF IPC). hahn_frame.
    apply inclusion_inter_r.
    2: { rewrite (wf_rmwl WF), (wf_rfl WF), inclusion_seq_eqv_l. 
         rewrite rewrite_trans by apply same_loc_trans. basic_solver. }     
    rewrite (rmw_in_sb WF), (SC_RF WF IPC), (sc_rf_sw WF).
    unfold imm_s_hb.hb. rewrite ct_begin, <- inclusion_t_rt, ct_begin.
    basic_solver 10. }
    
  rewrite <- seq_eqvK with (dom:=F ∩₁ Acqrel).
  rewrite ct_unionE. rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite RMW_RF_HBL. 
    arewrite (hb ∩ same_loc ⊆ scb G).
    arewrite ((⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)^+ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)^+ ⨾ ⦗Sc⦘).
    { rewrite ct_end. rewrite <- seq_eqvK at 4. basic_solver. }
    arewrite (⦗Sc⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)).
    { arewrite (⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘). unfold scb. basic_solver 10. }
    rewrite ct_unit. basic_solver. }
  rewrite !seqA. 
  arewrite (⦗W ∪₁ R⦘ ⨾ (rmw ⨾ rf)＊ ⊆ ⦗W ∪₁ R⦘ ⨾ (rmw ⨾ rf)＊ ⨾ ⦗W ∪₁ R⦘).
  { rewrite seq_rtE_r. unionL.
    { basic_solver. }
    rewrite seqA, <- ct_begin, ct_end. 
    arewrite (rf ≡ rf ⨾ ⦗R⦘) at 2 by eapply dom_r; rewrite WF.(wf_rfD) at 1; auto.
    arewrite (⦗R⦘ ⊆ ⦗W ∪₁ R⦘). hahn_frame.
    seq_rewrite <- ct_end. basic_solver. }

  rewrite RMW_RF_HBL at 1. 
  arewrite (hb ∩ same_loc ⊆ scb G).
  arewrite (⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)＊ ⊆ ⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)＊ ⨾ ⦗Sc⦘).
  { rewrite seq_rtE_r, seq_union_r.
    unionL. 
    { basic_solver 10. }
    rewrite seqA. seq_rewrite <- ct_begin. rewrite ct_end.
    rewrite <- seq_eqvK at 5. hahn_frame.
    rewrite <- ct_end. basic_solver. }
  
  assert ((sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ⊆ scb G) as SCB_NL.
  { unfold scb. basic_solver 20. }
  assert (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘) as RF_SCB.
  { rewrite <- seq_eqvK at 1. rewrite <- seq_eqvK at 3. 
    rewrite !seqA.  hahn_frame.
    unfold scb. arewrite (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ hb ∩ same_loc).
    { apply inclusion_inter_r.
      { rewrite <- sw_in_hb. apply (sc_rf_sw WF). }
      rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r. apply WF.(wf_rfl). }
    basic_solver 10. }
  
  assert (⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rf ⨾ (rmw ⨾ rf)＊)⁺
               ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)⁺).
  { rewrite <- seqA with (r1:=sb). 
    rewrite ct_rotl.
    rewrite !seqA. rewrite (F_HB WF). 
    rewrite (rtE (rmw ⨾ rf)). repeat case_union _ _.
    assert (⦗Sc⦘ ⨾ (sb \ same_loc) ⨾ hb＊ ⨾ (sb \ same_loc) ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘) as SBNL_HB_SCB. 
    { hahn_frame. unfold scb. rewrite rtE. repeat case_union _ _.
      unionL.
      { seq_rewrite seq_id_r. do 2 arewrite (sb \ same_loc ⊆ sb).
        rewrite rewrite_trans; [| apply sb_trans]. basic_solver 10. }
      rewrite ct_of_trans; [| apply hb_trans]. basic_solver 20. }
    assert (⦗W ∪₁ R⦘ ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⊆ sb \ same_loc) as WR_FB_NL by admit. 
    assert (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⊆ sb \ same_loc) as FB_WR_NL by admit. 
    
    unionL.
    2: { rewrite RMW_RF_HBL.
         arewrite ((⦗Sc⦘ ⨾ hb ∩ same_loc ⨾ ⦗Sc⦘)⁺ ⊆ ⦗Sc⦘ ⨾ (⦗Sc⦘ ⨾ hb ∩ same_loc ⨾ ⦗Sc⦘)⁺ ⨾ ⦗Sc⦘).
         { rewrite ct_end at 1. rewrite <- seq_eqvK at 4. hahn_frame_r. 
           seq_rewrite <- ct_end.
           rewrite ct_begin at 1. rewrite <- seq_eqvK at 1. hahn_frame_l.
           rewrite ct_begin. basic_solver 10. }
         sin_rewrite SB_RF_SC. rewrite !seqA.
         rewrite (dom_l WF.(wf_rfD)) at 1.
         arewrite (⦗Sc⦘ ⨾ (⦗W⦘ ⨾ rf) ≡ ⦗W⦘ ⨾ ⦗Sc⦘ ⨾ rf) by basic_solver.
         sin_rewrite WR_FB_NL.
         arewrite (⦗W⦘ ⊆ ⦗W ∪₁ R⦘) at 1 by basic_solver. sin_rewrite FB_WR_NL. 
         sin_rewrite SBNL_HB_SCB. 
         rewrite <- seq_eqvK at 2.
         rewrite (ct_begin (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)). rewrite !seqA.
         hahn_frame. sin_rewrite RF_SCB.
         arewrite (hb ∩ same_loc ⊆ scb G). arewrite (sb ⊆ scb G). arewrite (⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘).
         do 2 rewrite <- seqA. rewrite seqA with (r2:=scb G).
         rewrite ct_unit. rewrite inclusion_t_rt.
         rewrite <- ct_begin. basic_solver. }
    sin_rewrite seq_id_l.
    assert (rf ⨾ sb ≡ rf ⨾ ⦗ORlx⦘ ⨾ sb ∪ rf ⨾ ⦗Sc⦘ ⨾ sb) as SB_BEG by admit.
    seq_rewrite SB_BEG. repeat case_union _ _. unionL. 
    2: { rewrite !seqA. sin_rewrite SB_RF_SC.
         rewrite (dom_l WF.(wf_rfD)) at 1. rewrite !seqA. 
         seq_rewrite (seq_eqvC Sc W). rewrite !seqA. 
         rewrite <- seq_eqvK at 2. rewrite <- seq_eqvK at 4. rewrite !seqA.
         sin_rewrite WR_FB_NL.
         arewrite (⦗W⦘ ⊆ ⦗W ∪₁ R⦘) at 1 by basic_solver. sin_rewrite FB_WR_NL. 
         sin_rewrite SBNL_HB_SCB. sin_rewrite RF_SCB. 
         arewrite (sb ⊆ scb G). arewrite (⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘).
         do 2 rewrite ct_begin, <- inclusion_t_rt. rewrite ct_begin.
         rewrite !seqA. hahn_frame. }
    rewrite !seqA. 
    arewrite (⦗ORlx⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘) by admit. (* because the only way it could not is when sb starts with Rsc (dom(rmw) for corresponding write), but then it should be Sc, not ORlx *)
    rewrite <- (seq_eqvK (F ∩₁ Acqrel)) at 3. rewrite !seqA. 
    arewrite (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⊆ hb).
    { arewrite (rf ⊆ rf ⨾ (rmw ⨾ rf)＊ ) by basic_solver 10. 
      apply (F_HB WF). }
    seq_rewrite <- ct_end. rewrite ct_of_trans; [| by apply hb_trans]. 
    sin_rewrite WR_FB_NL. sin_rewrite FB_WR_NL.
    arewrite (hb ⊆ hb＊). sin_rewrite SBNL_HB_SCB.
    rewrite ct_begin. hahn_frame. }

  sin_rewrite H. rewrite rt_ct. 
  basic_solver. 
Admitted.


Lemma WIP_sc_sb_rf_ct_pscb (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  (⦗Sc ∩₁ (W ∪₁ R)⦘ ⨾ (sb ⨾ rf)⁺ ⨾ ⦗Sc⦘ ⊆ (psc_base G)⁺).
Proof.
  rewrite ct_end, !seqA.
  arewrite (sb ⨾ rf ⨾ ⦗Sc⦘ ≡ sb ⨾ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘) by admit.
  arewrite (rf ≡ ⦗W⦘ ⨾ rf) at 2.
  { eapply dom_l. apply WF.(wf_rfD). } 
  rewrite <- seq_eqvK with (dom:=Sc) at 1. rewrite !seqA.
  seq_rewrite (seq_eqvC Sc W). rewrite !seqA. 
  sin_rewrite (sc_rf_pscb); auto.
  rewrite ct_end. hahn_frame.
  arewrite (⦗Sc⦘ ⨾ ⦗W⦘ ⊆ ⦗(W ∪₁ R) ∩₁ Sc⦘) by mode_solver.  
  rewrite (WIP_sc_sb_rf_ending_sb_ct_pscb WF IPC). basic_solver. 
Admitted. 

Lemma WIP_po_rfe_co_fr (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  acyclic (sb ∪ rfe ∪ ⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘).
Proof.
  arewrite (rfe ⊆ rf). arewrite (coe ⊆ co). arewrite (fre G ⊆ fr). 
  assert (⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘ ⊆ psc_base G) as CO_FR_PSCB.
  { unfold psc_base. hahn_frame.
    arewrite (co ∪ fr ⊆ scb G).
    basic_solver 10. }
  
  apply acyclic_union1.
  { admit. }
  { rewrite CO_FR_PSCB. cdes IPC.
    arewrite (psc_base G ⊆ psc_f G ∪ psc_base G). auto. }
  rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
  rewrite <- seq_eqvK.
  rewrite <- !seqA, acyclic_rotl, !seqA.
  
  sin_rewrite sc_co_fr_ct_in_co_fr; auto.
  arewrite (⦗Sc⦘ ⨾ (co ∪ fr) ≡ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗W ∪₁ R⦘) by admit.
  rewrite seq_eqvC. rewrite <- !seqA, acyclic_rotl, !seqA.
  sin_rewrite CO_FR_PSCB.
  
  assert (⦗(W ∪₁ R)⦘ ⨾ ⦗Sc⦘ ⨾ (sb ∪ rf)⁺ ⨾ ⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⊆ (psc_base G)＊) as SC_SB_RF_PSCB.
  { 
    rewrite ct_unionE.
    assert (rf⁺ ≡ rf) as RF1. 
    { rewrite ct_begin. rewrite rtE. rewrite seq_union_r. rewrite ct_begin.
      seq_rewrite (rf_rf WF). basic_solver. }
    seq_rewrite RF1. 
    arewrite (rf＊ ≡ rf^?).
    { rewrite rtE. rewrite RF1. basic_solver. }
    rewrite <- !seqA. rewrite seqA with (r3:=⦗Sc⦘).
    rewrite seqA with (r1:=⦗(W ∪₁ R)⦘).
    case_union _ _.
    rewrite seq_union_r. rewrite seq_union_r, seq_union_l. 
    unionL.
    { rewrite (sc_rf_pscb WF). basic_solver. }
    rewrite cr_seq. case_union _ _. rewrite seq_union_r.
    arewrite ((sb ⨾ rf^?)⁺ ⊆ (sb ⨾ rf)^* ⨾ sb^?).
    { rewrite crE, seq_union_r, seq_id_r.
      rewrite unionC.
      rewrite path_absorb_rt.
      3: by apply sb_trans.
      2: left; generalize (@sb_trans G); basic_solver.
      rewrite crE, seq_union_r, seq_id_r.
      apply union_mori; eauto with hahn. }
    rewrite seq_union_l. 
    assert (⦗Sc ∩₁ (W ∪₁ R)⦘ ⨾ (sb ⨾ rf)＊ ⨾ sb^? ⨾ ⦗(W ∪₁ R) ∩₁ Sc⦘ ⊆ (psc_base G)＊) as SB_RF'.
    { rewrite cr_seq, !seq_union_r. unionL.
      { generalize (WIP_sc_sb_rf_ct_pscb WF IPC). basic_solver 10. }
      rewrite seq_rtE_l, seq_union_r. unionL.
      { arewrite (sb ⊆ scb G). arewrite (⦗Sc ∩₁ (W ∪₁ R)⦘ ⊆ ⦗Sc⦘) by mode_solver. 
        arewrite (⦗(W ∪₁ R) ∩₁ Sc⦘ ⊆ ⦗Sc⦘) by mode_solver. 
        sin_rewrite sc_scb_pscb. basic_solver. }
      pose proof ct_end. symmetry in H. seq_rewrite H.
      rewrite inclusion_t_rt. 
      rewrite (WIP_sc_sb_rf_ending_sb_ct_pscb WF IPC). basic_solver 10. }
    rewrite seq_union_r. 
    unionL.
    1, 2: rewrite !seqA, <- seqA, <- !id_inter.
    1, 2: rewrite set_interC with (s:=Sc), set_interC with (s':=Sc) at 1.
    { apply SB_RF'. }
    arewrite (⦗Sc ∩₁ (W ∪₁ R)⦘ ⊆ ⦗Sc⦘) by mode_solver.
    arewrite (rf ≡ rf ⨾ ⦗R⦘) at 1 by eapply dom_r; apply WF.(wf_rfD).
    arewrite (⦗R⦘ ⊆ ⦗W ∪₁R⦘) by mode_solver. 
    sin_rewrite (SC_RF WF IPC). 
    rewrite <- seq_eqvK at 2. rewrite !seqA.
    sin_rewrite (sc_rf_pscb WF).
    seq_rewrite <- id_inter. 
    sin_rewrite SB_RF'.
    rewrite <- ct_begin. basic_solver. }
  
  sin_rewrite SC_SB_RF_PSCB. 
  rewrite <- ct_end.
  cdes IPC. arewrite ((psc_base G)⁺ ⊆ (psc_base G ∪ psc_f G)⁺).
  red. red in Cpsc.
  rewrite ct_of_ct. rewrite unionC. auto.  
Admitted.
    
Lemma imm_to_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  assert (irreflexive (ohb ;; (co ∪ fr))) as HH.
  { eapply imm_to_ocaml_coherent; eauto. }
  red. splits; auto.
  1,2: eapply irreflexive_mori; eauto.
  1,2: red; basic_solver 10.
  
  apply acyclic_union1.
  { admit. }
  { (* arewrite (⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘ ⊆ (coe ∪ fre G)) by basic_solver. *)
    (* cdes IC. red in Cint.  *) admit. 
  }
  arewrite (coe ⊆ co).
  arewrite ((fre G) ⊆ fr). 
  (* arewrite ((⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘)⁺ ⊆ ⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘). *)

  rewrite sc_co_fr_ct_in_co_fr; auto.
Admitted.

End OCamlMM_TO_IMM_S.


