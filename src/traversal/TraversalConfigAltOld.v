From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import AuxDef.
Require Import TraversalConfig TraversalConfigAlt.
Require Import imm_s_rfppo.

Set Implicit Arguments.

Section TCCOH_ALT_OLD.

 Variable G : execution.
 Variable sc : relation actid.
 Variable T : trav_config.

  Notation "'I'" := (issued T).
  Notation "'C'" := (covered T).

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
  Notation "'ar'" := (ar G sc).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).
  Notation "'release'" := (release G).
  Notation "'sw'" := (sw G).
  Notation "'hb'" := (hb G).

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
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
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

Variable WF : Wf G.
Variable IMMCON : imm_consistent G sc.

Record tc_coherent_alt_old :=
  { otc_init : Init ∩₁ E ⊆₁ C ;
    otc_C_in_E : C ⊆₁ E ;
    otc_sb_C : dom_rel ( sb ⨾ ⦗C⦘) ⊆₁ C ;
    otc_W_C_in_I : C ∩₁ W ⊆₁ I ;
    otc_rf_C : dom_rel ( rf ⨾ ⦗C⦘) ⊆₁ I ;
    otc_sc_C : dom_rel ( sc ⨾ ⦗C⦘) ⊆₁ C ;
    otc_I_in_E : I ⊆₁ E ;
    otc_I_in_W : I ⊆₁ W ;
    otc_fwbob_I : dom_rel ( fwbob ⨾ ⦗I⦘) ⊆₁ C ;
    otc_dr_pb_I : dom_rel ( (detour ∪ rfe ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ⨾ (ppo ∪ bob) ⨾ ⦗I⦘) ⊆₁ I ;
    otc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I ;
    otc_rfi_ppo_loc_I  : dom_rel (rfi ⨾ ppo ∩ same_loc ⨾ ⦗I⦘) ⊆₁ I;
  }.

Section Props.

Hypothesis tc_old : tc_coherent_alt_old.

Lemma otc_rfirmw_I : dom_rel (rfi ⨾ rmw ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite (rmw_in_ppo_loc WF).
  apply tc_old.
Qed.

Lemma otc_rf_ppo_loc_I :
  dom_rel (rf ⨾ ppo ∩ same_loc ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite rfi_union_rfe. rewrite !seq_union_l, dom_union.
  unionL.
  { apply tc_old. }
  arewrite (ppo ∩ same_loc ⊆ ppo).
  etransitivity.
  2: by apply otc_dr_pb_I. 
  basic_solver 10.
Qed.

Lemma otc_rfrmw_I :
  dom_rel (rf ⨾ rmw ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite rfi_union_rfe. rewrite !seq_union_l, dom_union.
  unionL.
  { apply otc_rfirmw_I. }
  rewrite (rmw_in_ppo WF).
  etransitivity.
  2: by apply otc_dr_pb_I. 
  basic_solver 10.
Qed.

Lemma otc_tc_fwbob_I : dom_rel (fwbob⁺ ⨾ ⦗I⦘) ⊆₁ C.
Proof using tc_old.
  rewrite ct_end, !seqA.
  rewrite (dom_rel_helper (otc_fwbob_I tc_old)).
  rewrite fwbob_in_sb.
  generalize (@sb_trans G); ins; relsf.
  generalize (otc_sb_C tc_old).
  basic_solver 12.
Qed.

Lemma otc_W_bob_I : dom_rel (⦗W⦘ ⨾ bob⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using tc_old.
  rewrite tc_bob; relsf; splits; [| type_solver].
  rewrite (dom_rel_helper otc_tc_fwbob_I).
  generalize (otc_W_C_in_I tc_old).
  basic_solver 12.
Qed.

Lemma otc_I_ar_I_implied_helper_0 :
  dom_rel (⦗W⦘ ⨾  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite (bob_ppo_W_sb WF).
  rewrite crE.
  rewrite wf_ppoD at 1 2.
  relsf; splits; try type_solver.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  { generalize (otc_I_in_W tc_old). basic_solver. }
  sin_rewrite bob_sb; relsf; splits.
  { rewrite !seqA.
    arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ sb^?).
    { generalize (otc_W_ex_sb_I tc_old). basic_solver 12. }
    generalize otc_W_bob_I. basic_solver 12. }
  generalize otc_W_ex_sb_I.
  basic_solver 12.
Qed.

Lemma bob_W_ex_sb_W_ex_rfi_ct_alt :
  (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⨾ ⦗W⦘ ⊆
  (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⨾ (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ bob)^?.
Proof using.
  rewrite unionC.
  rewrite path_union1.
  rewrite !seq_union_l. unionL.
  { rewrite rtE. basic_solver 10. }
  hahn_frame_l.
  arewrite (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪
            ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆
            ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊).
  { rewrite rtE. basic_solver 20. }
  arewrite (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ sb).
  { rewrite bob_in_sb. basic_solver. }
  rewrite rt_of_trans; [|by apply sb_trans].
  rewrite ct_begin.
  arewrite (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^? ⊆ sb) at 2.
  { unfold Execution.rfi. generalize (@sb_trans G). basic_solver. }
  rewrite rt_of_trans; [|by apply sb_trans].
  arewrite (sb^? ⨾ sb^? ⊆ sb^?).
  { generalize (@sb_trans G). basic_solver. }
  rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l.
  unionL.
  { type_solver. }
  arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ⨾ ⦗R ∩₁ Acq⦘) at 1.
  { basic_solver. }
  arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
  basic_solver 10.
Qed.

Lemma dom_W_ex_rfi_Acq_bob_I_in_I :
  dom_rel (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ bob ⨾ ⦗I⦘) ⊆₁ I.
Proof using tc_old.
  etransitivity.
  2: by apply otc_dr_pb_I; auto.
  basic_solver 20.
Qed.
            
Lemma dom_W_ex_rfi_Acq_bob_cr_I_in_I :
  dom_rel ((⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ bob)^? ⨾ ⦗I⦘) ⊆₁ I.
Proof using tc_old.
  rewrite crE. rewrite seq_union_l, dom_union. unionL.
  { basic_solver. }
  rewrite !seqA. by apply dom_W_ex_rfi_Acq_bob_I_in_I.
Qed.

Lemma otc_I_ar_I_implied_helper_1 :
  dom_rel (⦗W⦘ ⨾ (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite (bob_ppo_W_ex_rfi_W_sb WF).
  rewrite crE.
  rewrite wf_ppoD at 1 2.
  relsf; splits; try type_solver.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
  { generalize (otc_I_in_W tc_old); basic_solver. }
  sin_rewrite bob_W_ex_sb_W_ex_rfi_ct_alt. rewrite !seqA.
  rewrite (dom_rel_helper dom_W_ex_rfi_Acq_bob_cr_I_in_I).
  rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
  rewrite rtE. relsf. split; [basic_solver|].
  rewrite <- dom_eqv1.
  arewrite (bob ⊆ bob ∪ ppo). by apply otc_I_ar_I_implied_helper_0.
Qed.

Lemma otc_dr_ppo_I : dom_rel ((rfe ∪ detour) ⨾ ppo ⨾ ⦗I⦘) ⊆₁ I.
Proof using tc_old.
  etransitivity.
  2: by apply (otc_dr_pb_I tc_old). 
  basic_solver 10.
Qed.

Lemma otc_dr_bob_I : dom_rel ((rfe ∪ detour) ⨾ bob ⨾ ⦗I⦘) ⊆₁ I.
Proof using tc_old.
  etransitivity.
  2: by apply otc_dr_pb_I; auto.
  basic_solver 20.
Qed.

Lemma otc_dr_bob_ct_I : dom_rel ((rfe ∪ detour) ⨾ bob⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  remember (rfe ∪ detour) as rd.
  rewrite tc_bob. rewrite !seq_union_l, !seq_union_r, !dom_union. unionL.
  2: { arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
       subst rd. by apply otc_dr_bob_I. }
  rewrite (dom_rel_helper otc_tc_fwbob_I).
  subst rd; relsf. split.
  { generalize (otc_rf_C tc_old); unfold Execution.rfe. basic_solver 21. }
  rewrite (dom_l (wf_detourD WF)).
  rewrite detour_in_sb.
  generalize (otc_sb_C tc_old) (otc_W_C_in_I tc_old); basic_solver 21.
Qed.

Lemma otc_I_ar_I_implied_helper_2 :
   dom_rel (⦗W⦘ ⨾ ar⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF IMMCON tc_old.
  assert (wf_sc G sc) as WFS by apply IMMCON.
  assert (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ sb) as AA.
  { rewrite (ppo_in_sb WF), bob_in_sb.
    arewrite (rfi ⊆ sb). basic_solver 10. }
  assert (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ sb) as BB.
  { rewrite bob_in_sb. arewrite (rfi ⊆ sb). basic_solver 10. }

  unfold imm_s.ar, ar_int.
  arewrite (sc ∪ rfe ∪
               (bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ⊆ 
            (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ∪
            (sc ∪ rfe ∪ detour)).
  { basic_solver 12. }
  remember (sc ∪ rfe ∪ detour) as srd.
  remember (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) as bps.
  rewrite unionC.
  rewrite path_union1.
  arewrite (srd ∪ srd ⨾ bps⁺ ⊆ srd ⨾ bps＊).
  { rewrite rtE. basic_solver 12. }
  relsf; splits.
  { generalize otc_I_ar_I_implied_helper_1.
    rewrite <- Heqbps. basic_solver 21. }
  rewrite !seqA, <- dom_eqv1.
  arewrite (⦗W⦘ ⨾ bps＊ ⨾ (srd ⨾ bps＊)⁺ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (fun _ _ => True)); cycle 1.
  { generalize (otc_W_C_in_I tc_old). basic_solver. }
  rewrite inclusion_t_rt.
  arewrite (I ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
  apply rt_ind_right with (P:= fun r =>  ⦗W⦘ ⨾ bps＊ ⨾ r ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘).
  { auto with hahn. }
  { rels. rewrite rtE; relsf. subst. unionL.
    { type_solver. }
    rewrite id_union; relsf; unionL.
    { rewrite (dom_rel_helper otc_I_ar_I_implied_helper_1). subst.
      basic_solver 12. }
    rewrite AA. rewrite ct_of_trans; [|by apply sb_trans].
    arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘) by basic_solver.
    rewrite (dom_rel_helper (otc_sb_C tc_old)).
    generalize (otc_W_C_in_I tc_old); basic_solver. }
  intros k H; rewrite !seqA.
  rewrite rtE at 2; relsf; unionL; subst srd.
  { rewrite (wf_scD WFS).
    rewrite (otc_I_in_W tc_old) at 1.
    rewrite (dom_r (wf_rfeD WF)).
    rewrite (dom_r (wf_detourD WF)).
    rewrite id_union; relsf; unionL; try type_solver.
    rewrite !seqA.
    arewrite (⦗F ∩₁ Sc⦘ ⨾ sc ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⨾ (fun _ _ : actid => True)).
    { generalize (otc_sc_C tc_old); basic_solver 21. }
    sin_rewrite H; basic_solver. }
  rewrite !unionA.
  remember (rfe ∪ detour) as rd.
  relsf; unionL.
  { cut (sc ⨾ bps⁺ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗C ∩₁ F ∩₁ Sc⦘ ⨾ (fun _ _ : actid => True)).
    { intro A. sin_rewrite A. arewrite (C ∩₁ F ∩₁ Sc ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
      sin_rewrite H. basic_solver. }
    subst bps.
    rewrite AA. rewrite ct_of_trans; [|by apply sb_trans].
    rewrite (wf_scD WFS), !seqA.
    rewrite id_union; relsf; unionL.
    { arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⊆ fwbob).
      { unfold imm_bob.fwbob. mode_solver. }
      generalize (otc_sc_C tc_old) (otc_fwbob_I tc_old).
      basic_solver 21. }
    generalize (otc_sc_C tc_old) (otc_sb_C tc_old).
    basic_solver 21. }
  cut (rd ⨾ bps⁺ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I⦘ ⨾ (fun _ _ : actid => True)).
  { intro A. sin_rewrite A. arewrite (I ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
    sin_rewrite H. basic_solver. }
  subst bps.
  rewrite (bob_ppo_W_ex_rfi_W_sb WF); relsf; unionL.
  { rewrite id_union; relsf; unionL.
    { generalize (otc_dr_pb_I tc_old). subst rd. basic_solver 12. }
    rewrite wf_ppoD. type_solver. }
  rewrite id_union; relsf; unionL.
  { arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (otc_I_in_W tc_old). basic_solver. }
    sin_rewrite bob_W_ex_sb_W_ex_rfi_ct_alt. rewrite !seqA.
    rewrite (dom_rel_helper (dom_W_ex_rfi_Acq_bob_cr_I_in_I)).
    arewrite (rd ⨾ ppo^? ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⨾ ⦗I⦘ ⊆
              ⦗I⦘ ⨾ rd ⨾ ppo^? ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊ ⨾ ⦗I⦘).
    2: basic_solver.
    apply dom_rel_helper.
    rewrite rtE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    { rewrite crE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
      unionL; subst rd.
      2: by apply otc_dr_ppo_I.
      rewrite (otc_I_in_W tc_old) at 1.
      rewrite (dom_r (wf_rfeD WF)), (dom_r (wf_detourD WF)).
      mode_solver. }
    rewrite crE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
    unionL.
    2: { rewrite (dom_r (wf_ppoD G)), !seqA.
         arewrite (bob ⊆ bob ∪ ppo).
         rewrite (dom_rel_helper otc_I_ar_I_implied_helper_0).
         subst rd.
         arewrite ((rfe ∪ detour) ⨾ ppo ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (rfe ∪ detour) ⨾ ppo ⨾ ⦗I⦘).
         { apply dom_rel_helper. apply otc_dr_ppo_I. }
         basic_solver. }
    arewrite (⦗I⦘ ⊆ ⦗W⦘ ⨾ ⦗I⦘).
    { generalize (otc_I_in_W tc_old). basic_solver. }
    sin_rewrite bob_sb. rewrite !seq_union_l, !seq_union_r, dom_union. unionL.
    2: { subst rd. rewrite (W_ex_acq_in_W WF).
         rewrite (dom_r (wf_rfeD WF)), (dom_r (wf_detourD WF)).
         mode_solver. }
    rewrite !seqA.
    arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆
              ⦗I⦘ ⨾ (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘).
    { apply dom_rel_helper. 
      rewrite crE. rewrite !seq_union_l, seq_id_l, dom_union. unionL.
      { basic_solver. }
      etransitivity.
      2: by apply (otc_W_ex_sb_I tc_old).
      basic_solver 10. }
    rewrite <- !seqA. do 3 rewrite dom_seq. rewrite seqA.
    subst rd. by apply otc_dr_bob_ct_I. }
  rewrite BB. rewrite ct_of_trans; [|by apply sb_trans].
  arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘).
  { basic_solver. }
  rewrite (ppo_in_sb WF).
  arewrite (sb^? ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). basic_solver. }
  rewrite (dom_rel_helper (otc_sb_C tc_old)).
  subst rd; relsf; unionL.
  { generalize (otc_rf_C tc_old); unfold Execution.rfe. basic_solver 21. }
  rewrite (dom_l (wf_detourD WF)).
  rewrite detour_in_sb.
  generalize (otc_sb_C tc_old) (otc_W_C_in_I tc_old); basic_solver 21.
Qed.

Lemma otc_rf_ppo_loc_ct_I :
  dom_rel ((rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  intros x [y HH]. destruct_seq_r HH as IY.
  induction HH as [x y AA|x y z AA BB].
  2: by intuition.
  apply otc_rf_ppo_loc_I; auto. eexists. apply seqA.
  apply seq_eqv_r. split; eauto.
Qed.

Lemma otc_rfrmw_ct_I :
  dom_rel ((rf ⨾ rmw)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF tc_old.
  rewrite (rmw_in_ppo_loc WF). apply otc_rf_ppo_loc_ct_I.
Qed.

Lemma otc_I_ar_rf_ppo_loc_I_implied_helper_2 :
   dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF IMMCON tc_old.
  assert (wf_sc G sc) as WFS by apply IMMCON.
  rewrite ct_step with (r:=ar) at 1.
  rewrite unionC.
  rewrite path_absorb1.
  2: { apply ar_ct_rf_ppo_loc_in_ar_ct; auto. }
  rewrite !seq_union_l, !seq_union_r, !dom_union.
  unionL.
  { arewrite_id ⦗W⦘. rewrite seq_id_l. by apply otc_rf_ppo_loc_ct_I. }
  { rewrite ct_of_ct. apply otc_I_ar_I_implied_helper_2; auto. }
  rewrite ct_of_ct; rewrite seqA.
  arewrite ((rf ⨾ ppo ∩ same_loc)⁺ ⊆ (rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘).
  { rewrite (dom_r (wf_ppoD G)) at 1.
    rewrite seq_eqv_inter_lr.
    rewrite <- !seqA. by rewrite inclusion_ct_seq_eqv_r. }
  rewrite (dom_rel_helper otc_I_ar_I_implied_helper_2).
  arewrite_id ⦗W⦘. rewrite !seq_id_l.
  rewrite <- !seqA.
  rewrite (dom_rel_helper otc_rf_ppo_loc_ct_I).
  basic_solver.
Qed.

Lemma otc_I_ar_rfrmw_I_implied_helper_2 :
   dom_rel (⦗W⦘ ⨾ (ar ∪ rf ⨾ rmw)⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof using WF IMMCON tc_old.
  rewrite (rmw_in_ppo_loc WF). apply otc_I_ar_rf_ppo_loc_I_implied_helper_2.
Qed.

End Props.
End TCCOH_ALT_OLD.
