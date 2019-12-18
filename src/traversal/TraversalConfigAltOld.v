From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s.

Require Import TraversalConfig TraversalConfigAlt.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TCCOH_ALT_OLD.

 Variable G : execution.
 Variable sc : relation actid.
 Variable T : trav_config.

  Notation "'I'" := (issued T).
  Notation "'C'" := (covered T).

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rf'" := G.(rf).
  Notation "'co'" := G.(co).
  Notation "'coe'" := G.(coe).
  Notation "'fr'" := G.(fr).

  Notation "'eco'" := G.(eco).

  Notation "'bob'" := G.(bob).
  Notation "'fwbob'" := G.(fwbob).
  Notation "'ppo'" := G.(ppo).
  Notation "'ar'" := (ar G sc).
  Notation "'fre'" := G.(fre).
  Notation "'rfi'" := G.(rfi).
  Notation "'rfe'" := G.(rfe).
  Notation "'deps'" := G.(deps).
  Notation "'detour'" := G.(detour).
  Notation "'release'" := G.(release).
  Notation "'sw'" := G.(sw).
  Notation "'hb'" := G.(hb).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
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

Implicit Type WF : Wf G.
Implicit Type WF_SC : wf_sc G sc.

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
    otc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I
  }.

Lemma otc_tc_fwbob_I (tc_old : tc_coherent_alt_old) :
  dom_rel (fwbob⁺ ⨾ ⦗I⦘) ⊆₁ C.
Proof.
rewrite ct_end, !seqA.
rewrite (dom_rel_helper (otc_fwbob_I tc_old)).
rewrite fwbob_in_sb.
generalize (@sb_trans G); ins; relsf.
generalize (otc_sb_C tc_old).
basic_solver 12.
Qed.

Lemma otc_W_bob_I (tc_old : tc_coherent_alt_old) :
  dom_rel (⦗W⦘ ⨾ bob⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
rewrite tc_bob; relsf; splits; [| type_solver].
rewrite (dom_rel_helper (otc_tc_fwbob_I tc_old)).
generalize (otc_W_C_in_I tc_old).
basic_solver 12.
Qed.

Lemma otc_I_ar_I_implied_helper_0 WF (tc_old : tc_coherent_alt_old) :
  dom_rel (⦗W⦘ ⨾ (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
  rewrite (bob_ppo_W_sb WF).
  rewrite crE.
  rewrite wf_ppoD at 1 2.
  relsf; splits; try type_solver.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ;; ⦗I⦘).
  { generalize (otc_I_in_W tc_old); basic_solver. }
  sin_rewrite bob_sb; relsf; splits.
  { rewrite !seqA.
    arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ sb^?).
    { generalize (otc_W_ex_sb_I tc_old). basic_solver 12. }
    generalize (otc_W_bob_I tc_old). basic_solver 12. }
  generalize (otc_W_ex_sb_I tc_old).
  basic_solver 12.
Qed.

Lemma otc_I_ar_I_implied_helper_1 WF (tc_old : tc_coherent_alt_old) :
  dom_rel (⦗W⦘ ⨾ (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)^+ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
  rewrite (bob_ppo_W_ex_rfi_W_sb WF).
  rewrite crE.
  rewrite wf_ppoD at 1 2.
  relsf; splits; try type_solver.
  arewrite (⦗I⦘ ⊆ ⦗W⦘ ;; ⦗I⦘).
  { generalize (otc_I_in_W tc_old); basic_solver. }
  arewrite ((bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ;; <|W|> ⊆
            (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^* ;; (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ;; bob)^?).
  { rewrite unionC.
    rewrite path_union1.
    rewrite !seq_union_l. unionL.
    { rewrite rtE. basic_solver 10. }
    hahn_frame_l.
    arewrite (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪
              ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆
              ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*).
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
    arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ;; ⦗R ∩₁ Acq⦘) at 1.
    { basic_solver. }
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
    basic_solver 10. }

  arewrite ((⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ bob)^? ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ bob)^? ⨾ ⦗I⦘).
  { apply dom_rel_helper.
    rewrite crE. rewrite seq_union_l, dom_union. unionL.
    { basic_solver. }
    rewrite !seqA.
    etransitivity.
    2: by apply otc_dr_pb_I; auto.
    basic_solver 10. }

  rewrite <- !seqA. do 2 rewrite dom_seq. rewrite !seqA.
  rewrite rtE. relsf. split; [basic_solver|].
  rewrite <- dom_eqv1.
  arewrite (bob ⊆ bob ∪ ppo). by apply otc_I_ar_I_implied_helper_0.
Qed.

Lemma otc_I_ar_I_implied_helper_2  WF WF_SC (tc_old : tc_coherent_alt_old) :
   dom_rel (<|W|> ;; ar⁺ ;; <|I|>) ⊆₁ I.
Proof.
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
  arewrite (srd ∪ srd ⨾ bps⁺ ⊆ srd ⨾ bps^*).
  { rewrite rtE. basic_solver 12. }
  relsf; splits.
  { generalize (otc_I_ar_I_implied_helper_1 WF tc_old).
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
    { rewrite (dom_rel_helper (otc_I_ar_I_implied_helper_1 WF tc_old)). subst.
      basic_solver 12. }
    rewrite (ppo_in_sb WF), bob_in_sb.
    arewrite_id ⦗W_ex_acq⦘.
    arewrite_id ⦗W⦘ at 2.
    generalize (@sb_trans G); ins; relsf.
    arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘).
    { basic_solver. }
    admit. }
    (* rewrite (dom_rel_helper (otc_sb_C tc_old)). *)
    (* generalize (otc_W_C_in_I tc_old); basic_solver. } *)
  intros k H; rewrite !seqA.
  rewrite rtE at 2; relsf; unionL; subst srd.
  { rewrite (wf_scD WF_SC).
    rewrite (otc_I_in_W tc_old) at 1.
    rewrite (dom_r (wf_rfeD WF)).
    rewrite (dom_r (wf_detourD WF)).
    rewrite id_union; relsf; unionL; try type_solver.

    rewrite !seqA.
    arewrite (⦗F ∩₁ Sc⦘ ⨾ sc ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⨾ (fun _ _ : actid => True)).
    generalize (otc_sc_C tc_old); basic_solver 21.
    sin_rewrite H; basic_solver. }
  rewrite !unionA.
  remember (rfe ∪ detour) as rd.
  relsf; unionL.
  { cut (sc ⨾ bps^+ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗C ∩₁ F ∩₁ Sc⦘ ;; (fun _ _ : actid => True)).
    { intro A. sin_rewrite A. arewrite (C ∩₁ F ∩₁ Sc ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
      sin_rewrite H. basic_solver. }
    subst bps.
    rewrite (ppo_in_sb WF), bob_in_sb.
    arewrite_id ⦗W_ex_acq⦘.
    arewrite_id ⦗W⦘.
    generalize (@sb_trans G); ins; relsf.
    rewrite (wf_scD WF_SC), !seqA.
    rewrite id_union; relsf; unionL.
    { admit. }
    (* { arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⊆  fwbob). *)
    (*   { unfold imm_bob.fwbob. mode_solver. } *)
    (*   generalize (otc_sc_C tc_old) (otc_fwbob_I tc_old). *)
    (*   basic_solver 21. } *)
    generalize (otc_sc_C tc_old) (otc_sb_C tc_old).
    admit. }
    (* basic_solver 21. *)
  cut (rd ⨾ bps^+ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I⦘ ;; (fun _ _ : actid => True)).
  { intro A. sin_rewrite A. arewrite (I ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
    sin_rewrite H. basic_solver. }
  subst bps.
  rewrite (bob_ppo_W_sb WF); relsf; unionL.
  rewrite id_union; relsf; unionL.
  { generalize (otc_dr_pb_I tc_old); subst rd. basic_solver 12.
                       by rewrite wf_ppoD; type_solver.
                       rewrite id_union; relsf; unionL.
                 ++ arewrite (⦗I⦘ ⊆ ⦗W⦘ ;; ⦗I⦘).
                      by generalize (otc_I_in_W tc_old); basic_solver.
                      sin_rewrite bob_sb; relsf; unionL.
                    ** rewrite !seqA.
                       arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (fun _ _ : actid => True)).
                         by generalize (otc_W_ex_sb_I tc_old); basic_solver 21.
                         rewrite crE; relsf; unionL.
                       --- rewrite tc_bob; relsf; unionL.
                           2: by generalize (otc_dr_pb_I tc_old); subst rd; unfold imm_bob.bob; basic_solver 21.
                           seq_rewrite (dom_rel_helper (otc_tc_fwbob_I  tc_old)).
                           subst rd; relsf; unionL.
                           generalize (otc_rf_C tc_old); unfold Execution.rfe; basic_solver 21.
                           rewrite (dom_l (wf_detourD WF)).
                           rewrite detour_in_sb.
                           generalize (otc_sb_C tc_old) (otc_W_C_in_I tc_old); basic_solver 21.
                       --- rewrite wf_ppoD, !seqA.
                           seq_rewrite (dom_rel_helper (otc_W_bob_I tc_old)).
                           generalize (otc_dr_pb_I tc_old).
                           subst rd.
                           basic_solver 21.
                    ** 
                      rewrite crE; relsf; unionL; subst rd.
                      ---  
                        rewrite (dom_r (wf_rfeD WF)).
                        rewrite (dom_r (wf_detourD WF)).
                        rewrite (W_ex_in_W WF).
                        type_solver.
                      ---
                        generalize (otc_dr_pb_I tc_old) (otc_W_ex_sb_I tc_old).
                        basic_solver 21.
                 ++ rewrite (ppo_in_sb WF), bob_in_sb.
                    arewrite_id ⦗W_ex_acq⦘.
                    arewrite_id ⦗W⦘.
                    generalize (@sb_trans G); ins; relsf.
                    arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘).
                    basic_solver.
                    rewrite (dom_rel_helper (otc_sb_C tc_old)).
                    subst rd; relsf; unionL.
                    generalize (otc_rf_C tc_old); unfold Execution.rfe; basic_solver 21.
                    rewrite (dom_l (wf_detourD WF)).
                    rewrite detour_in_sb.
                    generalize (otc_sb_C tc_old) (otc_W_C_in_I tc_old); basic_solver 21.

Qed.

End TCCOH_ALT_OLD.
