(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
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
Notation "'hb'" := G.(imm_s_hb.hb).

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
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Notation "'ohb'" := G.(OCaml.hb).

Hypothesis LSM : forall l,
    ⟪ LM : Loc_ l \₁ is_init ⊆₁ ORlx ⟫ \/
    ⟪ LM : Loc_ l \₁ is_init ⊆₁ Sc ⟫.

Hypothesis WSCFACQRMW : W∩₁Sc ≡₁ codom_rel (⦗F∩₁ Acq⦘ ⨾ immediate sb ⨾ rmw).
Hypothesis RMWSC  : rmw ≡ ⦗Sc⦘ ⨾ rmw ⨾ ⦗Sc⦘.

Hypothesis WRLXF : W∩₁ORlx ⊆₁ codom_rel (⦗F∩₁Acqrel⦘ ⨾ immediate sb).
Hypothesis RSCF  : R∩₁Sc  ⊆₁ codom_rel (⦗F∩₁Acq⦘ ⨾ immediate sb).

Lemma sc_rf_in_sw (WF: Wf G):
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

Lemma sc_rf_in_pscb (WF: Wf G):
    ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ psc_base G. 
Proof.
  arewrite (rf ⊆ rf ∩ same_loc).
  { apply inclusion_inter_r; try basic_solver.
    apply WF.(wf_rfl). }
  rewrite <- seq_eqvK, !seqA.  
  arewrite (⦗Sc⦘ ⨾ rf ∩ same_loc ⨾ ⦗Sc⦘ ⊆ hb ∩ same_loc).
  { apply inclusion_inter_r.
    { rewrite inclusion_inter_l1. rewrite (sc_rf_in_sw WF). apply sw_in_hb. }
    basic_solver. }
  unfold psc_base. hahn_frame.
  arewrite (hb ∩ same_loc ⊆ scb G).
  basic_solver 10. 
Qed.

Lemma co_sc_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘ ⊆ hb.
Proof.
  rewrite fsupp_imm_t with (r:=⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘).
  4: { generalize WF.(co_trans). basic_solver. }
  3: { generalize WF.(co_irr). basic_solver. }
  2: { arewrite (⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘ ⊆ co) by basic_solver.
       rewrite WF.(wf_coE). unfold acts_set.
       red. ins. eexists. basic_solver. }
  
  assert (sc_per_loc G) as SPL.
  { apply coherence_sc_per_loc. apply IPC. }
  assert (W ∩₁ Sc ⊆₁ codom_rel rmw) as WSCRMW. 
  { rewrite WSCFACQRMW. basic_solver. }
           
  apply inclusion_t_ind, hb_trans; auto.
  arewrite (immediate (⦗Sc⦘ ⨾ co ⨾ ⦗Sc⦘) ⊆ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⨾ sb).
  2: { sin_rewrite (sc_rf_in_sw WF).
       rewrite sw_in_hb, sb_in_hb.
       apply rewrite_trans, hb_trans. }
  rewrite (dom_r WF.(wf_coD)).
  rewrite !seqA.
  rewrite <- id_inter.
  rewrite WSCFACQRMW.
  intros w1 w2 [co_rmw_w1_w2 imm_w1_w2].
  apply seq_eqv_l in co_rmw_w1_w2.
  destruct co_rmw_w1_w2 as [SCW1 co_rmw_w1_w2].
  apply seq_eqv_r in co_rmw_w1_w2.
  destruct co_rmw_w1_w2 as [co_rmw_w1_w2 tmp].
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
  { assert (co w' w1) as CO.
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
  sin_rewrite (sc_rf_in_sw WF).
  rewrite sb_in_hb, sw_in_hb, !unionK.
  unfold imm_s_hb.hb. by rewrite ct_of_ct.
Qed.
  
Lemma imm_to_ocaml_coherent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  irreflexive (ohb ⨾ (co ∪ fr)).
Proof.
  rewrite ohb_in_hb; eauto. 
  arewrite (co ∪ fr ⊆ eco^?).
  { rewrite co_in_eco, fr_in_eco. basic_solver. }
  apply IPC.
Qed.

Lemma trans_co_fr (WF: Wf G) :
  transitive (co ∪ fr).
Proof.
  apply transitiveI.
  rewrite seq_union_r. do 2 rewrite seq_union_l.
  rewrite co_co, fr_co, fr_fr, co_fr; auto. 
  basic_solver. 
Qed.

Lemma sc_scb_pscb: (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘ ⊆ psc_base G).
Proof. 
  unfold psc_base. basic_solver 10. 
Qed.

Lemma wr_mode: Eninit ∩₁ (W ∪₁ R) ⊆₁ Sc ∪₁ ORlx.
Proof.
  unfolder. ins. desc.
  assert (exists l, Loc_ l x) as [l LX].
  { unfold Events.loc. unfold is_f, is_r, is_w in *.
    destruct (lab x) eqn:AA; simpls; desf.
    all: eauto. }
  destruct (LSM l) as [LL|LL]; [right|left].
  all: eapply LL; split; auto.
Qed.

Lemma sl_mode (WF: Wf G) r (SL: r ⊆ same_loc):
  ⦗Eninit \₁ F⦘ ⨾ r ⨾ ⦗Eninit \₁ F⦘ ⊆ ⦗Sc⦘ ⨾ r ⨾ ⦗Sc⦘ ∪ ⦗ORlx⦘ ⨾ r ⨾ ⦗ORlx⦘.
Proof.
  red. intros x y HH. 
  apply seq_eqv_lr in HH.
  destruct HH as [[[EX NIX] NFX] [HH [[EY NIY] NFY]]].
  assert (exists l, Loc_ l x) as [l LX].
  { unfold Events.loc. unfold is_f in *.
    destruct (lab x) eqn:AA; simpls.
    all: eauto. }
  assert (Loc_ l y) as LY.
  { rewrite <- LX. symmetry. by apply SL. }
  destruct (LSM l) as [LL|LL]; [right|left].
  all: apply seq_eqv_lr; splits; auto.
  all: eapply LL; split; auto.
Qed.

Lemma sc_ninit (WF: Wf G): Sc ⊆₁ set_compl is_init.
Proof. rewrite WF.(init_pln). mode_solver. Qed.
  
Lemma sc_rf_l (WF: Wf G): ⦗Sc⦘ ⨾ rf ⊆ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘.
Proof.
  rewrite WF.(wf_rfD) at 1.
  rewrite WF.(wf_rfE) at 1.
  rewrite !seqA.
  arewrite (⦗Sc⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗Eninit \₁ F⦘ ⨾ ⦗Sc⦘).
  { arewrite (Sc ⊆₁ Sc ∩₁ set_compl is_init).
    { generalize WF.(sc_ninit). basic_solver. }
    type_solver. }
  rewrite <- id_inter.
  arewrite (E ∩₁ R ⊆₁ Eninit \₁ F).
  { rewrite init_w; eauto. type_solver. }
  seq_rewrite seq_eqvC. 
  rewrite !seqA. sin_rewrite (sl_mode WF); [| by apply WF.(wf_rfl) ]. 
  mode_solver.
Qed.

Lemma sc_rf_r (WF: Wf G): ⦗set_compl is_init⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘.
Proof.
  rewrite WF.(wf_rfD) at 1.
  rewrite WF.(wf_rfE) at 1.
  rewrite !seqA.
  arewrite (⦗set_compl is_init⦘ ⨾ ⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗Eninit \₁ F⦘) by type_solver.
  arewrite (⦗E⦘ ⨾ ⦗R⦘ ⊆ ⦗Eninit \₁ F⦘).
  { rewrite init_w; eauto. type_solver. }
  sin_rewrite (sl_mode WF); [| apply WF.(wf_rfl) ].
  mode_solver.
Qed.

Lemma dom_crt: forall (A : Type) (dom : A -> Prop) r,
    ⦗dom⦘ ⨾ (r ⨾ ⦗dom⦘)＊ ⊆ ⦗dom⦘ ⨾ (r ⨾ ⦗dom⦘)＊ ⨾ ⦗dom⦘.
Proof.
  intros A dom r. rewrite rtE at 1. rewrite seq_union_r.
  unionL; [basic_solver| ].
  hahn_frame. rewrite ct_end at 1. rewrite <- seq_eqvK at 2. hahn_frame_r.
  rewrite <- ct_end. basic_solver.
Qed.

Lemma sb_w_sync (WF: Wf G): 
    ⦗E \₁ F⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ sb ⨾ (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗ORlx⦘ ∪ ⦗F ∩₁ Acq⦘ ⨾ sb ⨾ ⦗Sc⦘) ⨾ ⦗W⦘ ∪ rmw ⨾ ⦗W⦘.
Proof.
  rewrite (dom_r G.(wf_sbE)) at 1.
  rewrite inclusion_union_minus with (r:=sb) (r':=rmw) at 1.
  rewrite !seq_union_l, !seq_union_r.
  apply union_mori; [|basic_solver].
  rewrite no_sb_to_init at 1.
  rewrite seq_eqv_minus_lr.
  rewrite !seqA.
  arewrite (⦗set_compl is_init⦘ ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⊆ ⦗W ∩₁ Sc ∪₁ W ∩₁ ORlx⦘).
  { unfolder. ins. desf. splits; auto.
    destruct wr_mode with (x:=y); auto.
    basic_solver. }
  rewrite id_union. rewrite !seq_union_r.
  unionL.
  
  2: { unionR left. rewrite <- (seq_eqvK (W ∩₁ ORlx)). rewrite WRLXF at 1. 
       unfolder. intros e w H'. destruct H' as [H'' [H' [[f' [f U]] T']]].
       desf.
       assert (~is_init f) as NINITf.
       { generalize (@read_or_fence_is_not_init G WF f). type_solver. }
       exists f. splits; auto. 
       assert (e <> f) as NEQfe. 
       { red. type_solver. }       
       pose (sb_semi_total_r WF NINITf NEQfe H' U0 ) as SB.
       destruct SB; auto.
       exfalso. specialize (U1 e). auto. }
  unionR right. 
  rewrite <- (seq_eqvK (W ∩₁ Sc)) at 1. rewrite WSCFACQRMW at 1. 
  unfolder. intros e w [H' [w' [[f' [f U]] V]]].
  destruct U as [N [r' Z]]. 
  desf.
  exists f.
  assert (immediate sb r' w) as [SBr'w IMMr'w]. 
  { apply WF.(wf_rmwi) in Z0. auto. }
  splits; auto. 
  2: { apply (rmw_in_sb WF) in Z0. apply (sb_trans Z Z0). }
  assert (e <> f) as NEQfe. 
  { red. type_solver. }
  assert (sb e r') as SBer'.  
  { assert (e <> r') as NEQer'. 
    { red. type_solver. }
    assert (~is_init r') as NINITr'.
    { apply (WF.(wf_rmwD)), seq_eqv_l in Z0. desf. 
      generalize (@read_or_fence_is_not_init G WF r'). type_solver 10. }
    pose (sb_semi_total_r WF NINITr' NEQer' w') as SB. destruct SB; auto.    
    exfalso. specialize (IMMr'w e). auto. }
  assert (~is_init f) as NINITf.
  { generalize (@read_or_fence_is_not_init G WF f). type_solver. }
  pose (sb_semi_total_r WF NINITf NEQfe SBer' Z) as SB. destruct SB; auto.
  exfalso. specialize (Z1 e). auto.
Qed.

Lemma sb_r_sc_sync (WF: Wf G):
  ⦗E \₁ F⦘ ⨾  sb ⨾ ⦗R⦘ ⨾ ⦗Sc⦘ ⊆ sb ⨾ ⦗F ∩₁ Acq⦘ ⨾ sb ⨾ ⦗R⦘ ⨾ ⦗Sc⦘.
Proof.
  rewrite <- id_inter. rewrite <- (seq_eqvK (R ∩₁ Sc)). rewrite RSCF at 1.
  unfolder. intros e r [A [C [[f' [f U]] V]]]. desf.
  exists f. splits; auto.
  assert (e <> f) as NEQfe. 
  { red. type_solver. }
  assert (~is_init f) as NINITf.
  { generalize (@read_or_fence_is_not_init G WF f). type_solver. }  
  pose (sb_semi_total_r WF NINITf NEQfe C U0) as SB.
  destruct SB; auto.
  exfalso. specialize (U1 e). auto. 
Qed. 
  
Lemma sb_rf_sc_sc (WF : Wf G) : (* TODO *)
  sb ⨾ rf ⨾ ⦗Sc⦘ ⊆ sb ⨾ ⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘.
Proof.
  rewrite no_sb_to_init at 1. rewrite !seqA.
    by sin_rewrite sc_rf_r.
Qed.

Lemma rmw_rf_hbl (WF: Wf G):
  rmw ⨾ rf ⊆ ⦗Sc⦘ ⨾ hb ∩ same_loc ⨾ ⦗Sc⦘.
Proof.
  rewrite RMWSC, !seqA, (sc_rf_l WF). hahn_frame.
  apply inclusion_inter_r.
  2: { rewrite (wf_rmwl WF), (wf_rfl WF), inclusion_seq_eqv_l. 
       rewrite rewrite_trans by apply same_loc_trans. basic_solver. }     
  rewrite (rmw_in_sb WF), (sc_rf_l WF), (sc_rf_in_sw WF).
  unfold imm_s_hb.hb. rewrite ct_begin, <- inclusion_t_rt, ct_begin.
  basic_solver 10.
Qed.


Lemma f_hb (WF: Wf G):
  ((⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗ORlx⦘ ⨾ rf ∪ sb ⨾ ⦗Sc⦘ ⨾ rf)
     ⨾ (rmw ⨾ rf)＊ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘) ⊆ hb. 
Proof. 
  rewrite (dom_l WF.(wf_rfD)) at 1.
  rewrite seq_union_l, !seqA. 
  seq_rewrite <- rt_seq_swap. rewrite !seqA. 
  assert (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊ ⊆ release) as REL. 
  { unfold imm_s_hb.release, imm_s_hb.rs.
    arewrite (⦗W⦘ ⨾ (rf ⨾ rmw)＊ ⊆ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊).
    { basic_solver 10. }
    arewrite (⦗F ∩₁ Acqrel⦘ ⨾ sb ⊆ ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?); [|done].
    mode_solver 10. }
  rewrite inclusion_seq_eqv_l with (dom:=ORlx). 
  sin_rewrite REL. 
  unionL.
  { rewrite <- sw_in_hb. unfold imm_s_hb.sw.
    hahn_frame. rewrite id_inter. sin_rewrite (r_step (sb ⨾ ⦗F⦘)). 
    basic_solver 10. }
  arewrite (⦗Sc⦘ ⨾ (rf ⨾ rmw)＊ ⊆ ⦗Sc⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗Sc⦘).
  { rewrite RMWSC. do 2 rewrite <- seqA. sin_rewrite dom_crt. basic_solver. }
  sin_rewrite (sc_rf_l WF). 
  arewrite (sb ⊆ hb).
  sin_rewrite (sc_rf_in_sw WF). sin_rewrite sw_in_hb.
  arewrite (⦗Sc⦘ ⨾ (rf ⨾ rmw)＊ ⊆ hb＊).
  { rewrite rtE, seq_union_r. unionL; [basic_solver| ].
    rewrite ct_rotl.
    rewrite (rmw_rf_hbl WF).
    sin_rewrite (sc_rf_l WF).
    sin_rewrite WF.(rmw_in_sb). sin_rewrite sb_in_hb. 
    sin_rewrite (sc_rf_in_sw WF). sin_rewrite sw_in_hb.
    rewrite inclusion_seq_eqv_l,  inclusion_seq_eqv_r.
    arewrite (hb ∩ same_loc ⊆ hb).
    seq_rewrite <- ct_begin. rewrite ct_unit. basic_solver. }
  rewrite inclusion_seq_eqv_r.
  seq_rewrite <- ct_begin. do 2 sin_rewrite ct_unit.
  apply ct_of_trans, hb_trans.
Qed.


Lemma rf_scb (WF: Wf G): (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘).
Proof.
  rewrite <- seq_eqvK at 1. rewrite <- seq_eqvK at 3. 
  rewrite !seqA.  hahn_frame.
  unfold scb. arewrite (⦗Sc⦘ ⨾ rf ⨾ ⦗Sc⦘ ⊆ hb ∩ same_loc).
  { apply inclusion_inter_r.
    { rewrite <- sw_in_hb. apply (sc_rf_in_sw WF). }
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r. apply WF.(wf_rfl). }
  basic_solver 10.
Qed.

Lemma sbnl_hb_scb: ((sb \ same_loc) ⨾ hb＊ ⨾ (sb \ same_loc) ⊆ scb G). 
Proof.
  unfold scb. rewrite rtE. repeat case_union _ _.
  unionL.
  { seq_rewrite seq_id_r. do 2 arewrite (sb \ same_loc ⊆ sb).
    rewrite rewrite_trans; [| apply sb_trans]. basic_solver 10. }
  rewrite ct_of_trans; [| apply hb_trans]. basic_solver 20.
Qed. 

Lemma wr_fb_nl: (⦗W ∪₁ R⦘ ⨾ sb ⨾ ⦗F⦘ ⊆ sb \ same_loc). 
Proof. 
  unfold Events.same_loc, Events.loc, is_w, is_f, is_r.
  unfolder. ins. desf.
Qed. 
Lemma fb_wr_nl: (⦗F⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⊆ sb \ same_loc).
  unfold Events.same_loc, Events.loc, is_w, is_f, is_r.
  unfolder. ins. desf.
Qed. 

Lemma scb_chain (WF: Wf G):
  (⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (sb ⨾ ⦗F ∩₁ Acq⦘ ⨾ (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗ORlx⦘ ⨾ rf ∪ sb ⨾ ⦗Sc⦘ ⨾ rf) ⨾ (rmw ⨾ rf)＊)⁺ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘) ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)⁺.
Proof.
  rewrite <- seqA with (r1:=sb). 
  rewrite ct_rotl.
  rewrite !seqA.
  
  rewrite <- !seqA with (r3:=(⦗F ∩₁ Acq⦘)). sin_rewrite dom_crt. 
  rewrite !seqA. sin_rewrite (f_hb WF).
  assert (⦗W ∪₁ R⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⨾ hb＊ ⨾ ⦗F ∩₁ Acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ scb G) as SCB'.
  { rewrite rtE. repeat case_union _ _. unionL.
    { repeat rewrite inclusion_seq_eqv_l.
      hahn_frame. rewrite inclusion_seq_eqv_r, rewrite_trans; [| apply sb_trans].
      unfold scb. basic_solver 10. }
    arewrite (F ∩₁ Acq ⊆₁ F) by basic_solver. 
    sin_rewrite wr_fb_nl. 
    arewrite (W ⊆₁ W ∪₁ R).  sin_rewrite fb_wr_nl.
    hahn_frame. 
    rewrite ct_of_trans; [| apply hb_trans].
    arewrite (hb ⊆ hb＊). apply sbnl_hb_scb. }
  
  repeat case_union _ _. unionL.    
  2: { rewrite (dom_l WF.(wf_rfD)) at 1. seq_rewrite (seq_eqvC Sc W).
       rewrite !seqA. 
       sin_rewrite (sc_rf_l WF).
       rewrite <- seqA with (r2:=⦗W⦘). sin_rewrite SCB'.
       rewrite <- seq_eqvK at 2.
       rewrite !seqA. rewrite <- ct_ct. 
       rewrite ct_begin at 1.  hahn_frame. 
       sin_rewrite (rf_scb WF). rewrite <- seq_eqvK at 2. rewrite !seqA.
       rewrite rt_ct, ct_begin. hahn_frame. 
       rewrite (rmw_rf_hbl WF). arewrite (hb ∩ same_loc ⊆ scb G).
       rewrite <- !seqA with (r3:=(⦗Sc⦘)). sin_rewrite dom_crt.
       rewrite !seqA. rewrite (inclusion_seq_eqv_l).
       rewrite <- rt_rt at 2. hahn_frame_l.
       rewrite inclusion_seq_eqv_l with (dom:=(W ∪₁ R)). 
       arewrite (sb ⊆ scb G). rewrite <- inclusion_t_rt.
       rewrite ct_begin. hahn_frame. }
  
  rewrite !seqA.
  arewrite (sb ⨾ ⦗ORlx⦘ ⨾ rf ⊆ sb ⨾ ⦗ORlx⦘ ⨾ rf ⨾ ⦗ORlx⦘).
  { rewrite (WF.(wf_rfE)), (WF.(wf_rfD)) at 1.
    rewrite no_sb_to_init, (no_rf_to_init WF) at 1. hahn_frame_l.    
    arewrite (⦗fun x : actid => ~ is_init x⦘ ⨾ ⦗ORlx⦘ ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⊆ ⦗ORlx⦘ ⨾ ⦗E \₁ (fun a : actid => is_init a) \₁ F⦘) by mode_solver.
    arewrite (⦗fun x : actid => ~ is_init x⦘ ⨾ ⦗R⦘ ⨾ ⦗E⦘ ⊆ ⦗E \₁ (fun a : actid => is_init a) \₁ F⦘) by mode_solver.
    rewrite (sl_mode WF (WF.(wf_rfl))).
    rewrite seq_union_r. unionL; [mode_solver| ].
    basic_solver. }
  arewrite (⦗ORlx⦘ ⨾ (rmw ⨾ rf)＊ ⊆ ⦗ORlx⦘).
  { rewrite rtE, seq_union_r. unionL; [basic_solver| ].
    rewrite ct_begin, RMWSC, !seqA. mode_solver.  }
  arewrite (rf ⨾ ⦗ORlx⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘).
  { rewrite (dom_r (WF.(wf_rfD))), (dom_r (WF.(wf_rfE))) at 1. 
    rewrite !seqA. 
    arewrite (⦗E⦘ ⨾ ⦗R⦘ ⊆ ⦗E \₁ F⦘) by type_solver.
    hahn_frame_l. seq_rewrite (@seq_eqvC _ _ ORlx). rewrite seqA. 
    rewrite id_union at 1. case_union _ _.  do 3 rewrite seq_union_r at 1. unionL.
    { hahn_frame_r. rewrite (sb_w_sync WF), seq_union_r. unionL. 
      2: { rewrite RMWSC, seqA. mode_solver. }
      rewrite inclusion_seq_eqv_l. 
      arewrite (W ⊆₁ W ∪₁ R) at 1. hahn_frame.
      mode_solver. }
    rewrite (sb_r_sc_sync WF). arewrite (R ⊆₁ W ∪₁ R) at 1.
    hahn_frame. basic_solver. }
    
  pose (f_hb WF). rewrite seq_union_l,  <- inclusion_union_r1 in i. 
  rewrite rtE, <- inclusion_union_r1, seq_id_l, !seqA in i.
  rewrite <- seq_eqvK with (dom:=(F ∩₁ Acq)) at 3. rewrite seqA. 
  sin_rewrite i.
  sin_rewrite (@inclusion_seq_eqv_l actid hb (F ∩₁ Acq)).
  seq_rewrite <- ct_end. rewrite ct_of_trans by apply hb_trans.
  arewrite (F ∩₁ Acq ⊆₁ F) by mode_solver.
  sin_rewrite wr_fb_nl. sin_rewrite fb_wr_nl.
  pose sbnl_hb_scb. rewrite rtE, <- inclusion_union_r2, ct_of_trans in i0; [| apply hb_trans].
  sin_rewrite i0. rewrite ct_begin. hahn_frame. 
Qed. 

Lemma rmw_rf_ct_sb_scb (WF: Wf G):
  (rmw ⨾ rf)⁺ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)⁺.
Proof.
  rewrite (rmw_rf_hbl WF). 
  arewrite (hb ∩ same_loc ⊆ scb G).
  arewrite ((⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)⁺ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)⁺ ⨾ ⦗Sc⦘).
  { rewrite ct_end. rewrite <- seq_eqvK at 4. basic_solver. }
  arewrite (⦗Sc⦘ ⨾ sb ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ (⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)).
  { arewrite (⦗W ∪₁ R⦘ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘). unfold scb. basic_solver 10. }
  rewrite ct_unit. basic_solver.
Qed.

Lemma sc_sb_rf_ct_sb_pscb (WF: Wf G):
  (⦗Sc ∩₁ (W ∪₁ R)⦘ ⨾ (sb ⨾ rf)＊ ⨾ sb ⨾ ⦗(W ∪₁ R) ∩₁ Sc⦘ ⊆ (psc_base G)⁺).
Proof.
  rewrite <- sc_scb_pscb.
  
  rewrite rtE. do 2 case_union _ _. unionL. 
  { arewrite (sb ⊆ scb G).
    rewrite <- ct_step. 
    basic_solver. }
  rewrite !id_inter, !seqA.
  
  arewrite (⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (sb ⨾ rf)⁺ ⊆ ⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ (⦗E \₁ F⦘ ⨾ sb ⨾ rf)⁺).
  { rewrite ct_rotl at 1.
    arewrite (rf ≡ rf ⨾ ⦗R⦘) at 1 by eapply (dom_r WF.(wf_rfD)).
    arewrite (rf ⨾ ⦗R⦘ ⊆ rf ⨾ ⦗E \₁ F⦘).
    { rewrite (dom_r WF.(wf_rfE)) at 1. rewrite seqA.
      hahn_frame. type_solver. }
    arewrite (⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ sb ⊆ ⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⨾ ⦗E \₁ F⦘ ⨾ sb).
    { rewrite <- (seq_eqvK (W ∪₁ R)) at 1.
      rewrite <- (seq_eqvK (Sc)) at 1.
      rewrite !seqA. seq_rewrite (seq_eqvC (Sc) (W ∪₁ R)). 
      arewrite (sb ≡ ⦗E⦘ ⨾ sb) by eapply (dom_l (wf_sbE G)). 
      arewrite (⦗W ∪₁ R⦘ ⨾ ⦗E⦘ ⊆ ⦗E \₁ F⦘) by mode_solver.
      hahn_frame. basic_solver. }
    rewrite <- seq_eqvK at 1. rewrite seqA at 1.
    rewrite <- (seqA _ sb _). 
    rewrite <- ct_rotl.
    seq_rewrite seq_eqvK. basic_solver 10. }
  
  rewrite (dom_l WF.(wf_rfD)) at 1. sin_rewrite (sb_w_sync WF).
  
  rewrite <- seq_eqvK with (dom:=F ∩₁ Acqrel).
  case_union _ _. seq_rewrite ct_unionE.
  case_union ((rmw ⨾ ⦗W⦘) ⨾ rf)⁺ _. do 2 rewrite seq_union_r. unionL.
  { rewrite inclusion_seq_eqv_r. sin_rewrite (rmw_rf_ct_sb_scb WF). basic_solver. } 
  
  rewrite !seqA. 
  arewrite (⦗W ∪₁ R⦘ ⨾ (rmw ⨾ ⦗W⦘ ⨾ rf)＊ ⊆ ⦗W ∪₁ R⦘ ⨾ (rmw ⨾ rf)＊ ⨾ ⦗W ∪₁ R⦘).
  { rewrite inclusion_seq_eqv_l with (dom:=W).
    rewrite (dom_r WF.(wf_rfD)) at 1. arewrite (R ⊆₁ W ∪₁ R) at 2.
    rewrite <- seqA. rewrite dom_crt.
    rewrite !seqA. hahn_frame. rewrite inclusion_seq_eqv_r. basic_solver. }
  
  rewrite (rmw_rf_hbl WF) at 1.
  arewrite (hb ∩ same_loc ⊆ scb G).
  seq_rewrite (@seq_eqvC _ Sc _). rewrite seqA.
  rewrite <- seqA with (r3:=⦗Sc⦘). sin_rewrite dom_crt. rewrite !seqA.
  rewrite <- rt_ct with (r:=(⦗Sc⦘ ⨾ scb G ⨾ ⦗Sc⦘)).
  do 2 rewrite inclusion_seq_eqv_l at 1. hahn_frame_l. 

  pose (scb_chain WF). rewrite <- !seqA with (r3:=rf) in i. rewrite <- seq_union_l in i.
  arewrite (Acqrel ⊆₁ Acq) at 1 by mode_solver. rewrite <- seq_union_r.
  do 2 sin_rewrite (@inclusion_seq_eqv_r actid _ W). 
  rewrite !seqA. rewrite !seqA in i. auto. 
Qed.


Lemma sc_sb_rf_ct_pscb (WF: Wf G):
  (⦗Sc ∩₁ (W ∪₁ R)⦘ ⨾ (sb ⨾ rf)⁺ ⨾ ⦗Sc⦘ ⊆ (psc_base G)⁺).
Proof.
  rewrite ct_end, !seqA.
  sin_rewrite sb_rf_sc_sc; auto.
  rewrite (dom_l WF.(wf_rfD)) at 2.
  rewrite <- seq_eqvK with (dom:=Sc) at 1. rewrite !seqA.
  seq_rewrite (seq_eqvC Sc W). rewrite !seqA. 
  sin_rewrite (sc_rf_in_pscb); auto.
  rewrite ct_end. hahn_frame.
  arewrite (⦗Sc⦘ ⨾ ⦗W⦘ ⊆ ⦗(W ∪₁ R) ∩₁ Sc⦘) by mode_solver.  
  rewrite (sc_sb_rf_ct_sb_pscb WF). basic_solver. 
Qed.

Lemma acyclic_sb_rf (WF: Wf G) sc (IPC: imm_psc_consistent G sc):
  acyclic (sb ∪ rf).
Proof. 
  cdes IPC. cdes IC.
  rewrite rfi_union_rfe, <- unionA. arewrite (rfi ⊆ sb). rewrite unionK. 
  apply acyclic_union. 
  { rewrite sb_in_hb. cdes Cint.
    red. rewrite ct_of_trans; [| apply hb_trans].
    arewrite (hb ⊆ hb ⨾ eco^?); [basic_solver|auto]. }
  rewrite acyclic_rotl, rtE, seq_union_l, seq_id_l.
  rewrite ct_of_trans by apply sb_trans.
  red in Cext. cdes Cext. 
  apply acyclic_union.
  { apply acyclic_disj. rewrite WF.(wf_rfeD). mode_solver. }
  rewrite seqA, <- ct_begin.
  arewrite (rfe⁺ ≡ rfe).
  { rewrite ct_begin, rtE, seq_union_r.
    rewrite ct_begin. rewrite WF.(wf_rfeD) at 2. rewrite WF.(wf_rfeD) at 3. 
    type_solver. }
  rewrite WF.(wf_rfeD), (dom_r WF.(wf_rfeE)), seqA. 
  arewrite (⦗E⦘ ⨾ ⦗R⦘ ⊆ ⦗E \₁ F⦘) by type_solver.
  arewrite (rfe ⊆ ar sc). 
  do 2 rewrite <- seqA. rewrite acyclic_rotl, !seqA.
  sin_rewrite (sb_w_sync WF). 
  seq_rewrite seq_union_r.
  arewrite (F ∩₁ Acqrel ⊆₁ F ∩₁ Acq/Rel) by mode_solver.
  arewrite (F ∩₁ Acq ⊆₁ F ∩₁ Acq/Rel) by mode_solver.
  rewrite <- seq_eqvK with (dom:=(F ∩₁ Acq/Rel)), !seqA. 
  repeat arewrite (sb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⊆ imm_bob.bob G).
  repeat arewrite (⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ imm_bob.bob G).
  rewrite RMWSC, WF.(wf_rmwD).
  arewrite ((fun a : actid => R_ex lab a) ⊆₁ R) by type_solver.
  arewrite (⦗Sc⦘ ⨾ ⦗R⦘ ⊆ ⦗R ∩₁ Acq⦘) by mode_solver. 
  rewrite WF.(rmw_in_sb). arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ imm_bob.bob G).
  arewrite (imm_bob.bob G ⊆ ar sc).
  repeat rewrite inclusion_seq_eqv_r. do 2 rewrite seq_union_l.
  rewrite !seqA, unionK.
  arewrite (ar sc ⨾ ar sc ⨾ ar sc ⊆ (ar sc)^+).
  { do 2 rewrite <- ct_ct at 1. basic_solver 10. }
  arewrite (ar sc ⨾ ar sc ⊆ (ar sc)^+).
  { rewrite <- ct_ct at 1. basic_solver 10. }
  rewrite unionK. red in Cext. red.
  rewrite ct_of_ct. auto.
Qed. 
  
Lemma imm_to_ocaml_causal (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  acyclic (sb ∪ rfe ∪ ⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘).
Proof.
  arewrite (rfe ⊆ rf). arewrite (coe ⊆ co). arewrite (fre G ⊆ fr). 
  assert (⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘ ⊆ psc_base G) as CO_FR_PSCB.
  { unfold psc_base. hahn_frame.
    arewrite (co ∪ fr ⊆ scb G).
    basic_solver 10. }
  
  apply acyclic_union1.
  { apply (@acyclic_sb_rf WF _ IPC). }
  { rewrite CO_FR_PSCB. cdes IPC.
    arewrite (psc_base G ⊆ psc_f G ∪ psc_base G). auto. }
  
  rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
  rewrite <- seq_eqvK.
  rewrite <- !seqA, acyclic_rotl, !seqA.

  seq_rewrite (@ct_of_trans _ (co ∪ fr)); [| apply (trans_co_fr WF)].
  arewrite (co ∪ fr ⊆ ⦗W ∪₁ R⦘ ⨾ (co ∪ fr) ⨾ ⦗W ∪₁ R⦘).
  { rewrite WF.(wf_coD), WF.(wf_frD). basic_solver. }
  seq_rewrite (@seq_eqvC _ _ (W ∪₁ R)). rewrite seqA. rewrite seq_eqvC. 
  rewrite <- !seqA, acyclic_rotl, !seqA.
  sin_rewrite CO_FR_PSCB.
  
  arewrite (⦗(W ∪₁ R)⦘ ⨾ ⦗Sc⦘ ⨾ (sb ∪ rf)⁺ ⨾ ⦗Sc⦘ ⨾ ⦗W ∪₁ R⦘ ⊆ (psc_base G)＊).
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
    { rewrite (sc_rf_in_pscb WF). basic_solver. }
    rewrite cr_seq. case_union _ _. rewrite seq_union_r.
    arewrite ((sb ⨾ rf^?)⁺ ⊆ (sb ⨾ rf)＊ ⨾ sb^?).
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
      { generalize (sc_sb_rf_ct_pscb WF). basic_solver 10. }
      rewrite (sc_sb_rf_ct_sb_pscb WF). basic_solver 10. }
    rewrite seq_union_r. 
    unionL.
    1, 2: rewrite !seqA, <- seqA, <- !id_inter.
    1, 2: rewrite set_interC with (s:=Sc), set_interC with (s':=Sc) at 1.
    { apply SB_RF'. }
    arewrite (⦗Sc ∩₁ (W ∪₁ R)⦘ ⊆ ⦗Sc⦘) by mode_solver.
    arewrite (rf ≡ rf ⨾ ⦗R⦘) at 1 by eapply dom_r; apply WF.(wf_rfD).
    arewrite (⦗R⦘ ⊆ ⦗W ∪₁R⦘) by mode_solver. 
    sin_rewrite (sc_rf_l WF). 
    rewrite <- seq_eqvK at 2. rewrite !seqA.
    sin_rewrite (sc_rf_in_pscb WF).
    seq_rewrite <- id_inter. 
    sin_rewrite SB_RF'.
    rewrite <- ct_begin. basic_solver. }
  
  rewrite <- ct_end.
  cdes IPC. arewrite ((psc_base G)⁺ ⊆ (psc_base G ∪ psc_f G)⁺).
  red. red in Cpsc.
  rewrite ct_of_ct. rewrite unionC. auto.  
Qed.
    
Lemma imm_to_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  assert (irreflexive (ohb ⨾ (co ∪ fr))) as HH.
  { eapply imm_to_ocaml_coherent; eauto. }
  red. splits; auto.
  1,2: eapply irreflexive_mori; eauto.
  1,2: red; basic_solver 10.

  apply (imm_to_ocaml_causal WF IPC). 
Qed. 
  
End OCamlMM_TO_IMM_S.
