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
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Notation "'ohb'" := G.(OCaml.hb).

Hypothesis LSM : forall l,
    << LM : Loc_ l \₁ is_init  ⊆₁ Rlx \₁ Sc >> \/
    << LM : Loc_ l \₁ is_init ⊆₁ Sc >>.

Hypothesis WSCFACQRMW : W∩₁Sc ≡₁ codom_rel (<|F∩₁ Acq|> ;; immediate sb ;; rmw).
Hypothesis RMWSC  : rmw ≡ ⦗Sc⦘ ⨾ rmw ⨾ ⦗Sc⦘.

Hypothesis WRLXF : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acqrel|> ;; immediate sb).
Hypothesis RSCF  : R∩₁Sc  ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

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
       arewrite (Sc ⊆₁ Rel) at 1 by mode_solver.
       arewrite (Sc ⊆₁ Acq)      by mode_solver.
       unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
       rewrite !seqA.
       hahn_frame.
       rewrite (dom_l WF.(wf_rfD)) at 1.
       basic_solver 40. }
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
    apply CC in DD. by destruct DD.  }

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
       unfold imm_s_hb.hb. basic_solver. }
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

Lemma sb_rfe_sc_in_hb (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  <|Sc|> ;; (sb ∪ rfe)⁺ ;; <|Sc|> ⊆ hb.
Proof.
Admitted.

(* Lemma sc_co_fr_ct_in_co_fr (WF: Wf G) : *)
(*   (⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘)⁺ ⊆ ⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘. *)
Lemma sc_co_fr_ct_in_co_fr (WF: Wf G) :
  ⦗Sc⦘ ⨾ (co ∪ fr)⁺ ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘.
Proof.
  (* rewrite inclusion_ct_seq_eqv_l. rewrite inclusion_ct_seq_eqv_r. *)
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

Lemma WIP_po_rfe_co_fr (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  (* (⦗Sc⦘ ⨾ (sb ∪ rfe) ⨾ ⦗Sc⦘ ∪ ⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘)⁺ ⊆ (psc_base G)⁺. *)
  acyclic (sb ∪ rfe ∪ ⦗Sc⦘ ⨾ (coe ∪ fre G) ⨾ ⦗Sc⦘).
Proof.

  assert (⦗Sc⦘ ⨾ (co ∪ fr) ⨾ ⦗Sc⦘ ⊆ psc_base G) as COE_FRE_PSCB.
  { unfold psc_base. hahn_frame.
    arewrite (co ∪ fr ⊆ scb G).
    basic_solver 10. }
  
  apply acyclic_union1.
  { admit. }
  { arewrite (coe ∪ fre G ⊆ co ∪ fr).
    rewrite COE_FRE_PSCB. cdes IPC.
    arewrite (psc_base G ⊆ psc_f G ∪ psc_base G). auto. }
  rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
  rewrite <- seq_eqvK.
  rewrite <- !seqA. rewrite acyclic_rotl. rewrite !seqA.
  
  arewrite (coe ∪ fre G ⊆ co ∪ fr).
  sin_rewrite sc_co_fr_ct_in_co_fr; auto. 
  sin_rewrite COE_FRE_PSCB. 

  assert (⦗F ∩₁ Acqrel⦘⨾ sb ⨾ rfe ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ hb) as F_HB.
  { rewrite <- sw_in_hb. unfold imm_s_hb.sw.
    do 2 rewrite id_inter.
    arewrite (Acqrel ⊆₁ Rel) by mode_solver.  
    unfold imm_s_hb.release.
    rewrite <- !seqA, seq_eqvC, !seqA.
    arewrite (sb ⨾ ⦗F⦘ ⊆ (sb ⨾ ⦗F⦘)^?). arewrite ( (⦗F⦘ ⨾ sb) ⊆ (⦗F⦘ ⨾ sb)^?). 
    arewrite (rfe ⊆ rf).
    arewrite (rf ≡ ⦗W⦘⨾ rf) at 1.
    { rewrite WF.(wf_rfD). basic_solver. }    
    arewrite (⦗W⦘ ⊆ imm_s_hb.rs G).
    { unfold imm_s_hb.rs. basic_solver 100. }
    hahn_frame. basic_solver. }  
    
  assert (⦗Sc⦘ ⨾ (sb ⨾ rfe)⁺ ⨾ ⦗Sc⦘ ⊆ (psc_base G)⁺) as CT_SB_RFE_PSCB.
  { arewrite (sb ⨾ rfe ≡ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rfe).
    { arewrite (sb ⨾ rfe ≡ sb ⨾ ⦗W⦘ ⨾ rfe).
      { rewrite WF.(wf_rfeD). basic_solver 100. }
      admit. }
    rewrite <- seq_eqvK with (dom:=F ∩₁ Acq/Rel).
    rewrite seqA. rewrite <- seqA with (r2:=⦗F ∩₁ Acq/Rel⦘).
    rewrite ct_rotl.
    admit. }

  assert (⦗Sc⦘ ⨾ (sb ∪ rfe)⁺ ⨾ ⦗Sc⦘ ⊆ (psc_base G)⁺) as SC_SB_RFE_PSCB.
  { rewrite ct_unionE.
    arewrite (rfe⁺ ≡ rfe).
    { admit. }
    arewrite (rfe＊ ≡ rfe^?).
    { admit. }
    case_union _ _.
    rewrite seq_union_r.
    unionL.
    { arewrite (⦗Sc⦘ ⨾ rfe ⨾ ⦗Sc⦘ ⊆ ⦗Sc⦘ ⨾ hb ∩ same_loc ⨾ ⦗Sc⦘).
      { admit. }
      rewrite <- ct_step. unfold psc_base.
      hahn_frame.
      arewrite (hb ∩ same_loc ⊆ scb G).
      basic_solver 50. }
    arewrite ((sb ⨾ rfe^?) ≡ (sb ∪ sb ⨾ rfe)) by basic_solver 100. 
    (* rewrite unionC. *)
    (* rewrite ct_begin. *)
    (* rewrite path_ut. *)
    (* arewrite (rfe⁺ ≡ rfe) by admit. *)
    (* arewrite (rfe＊ ≡ rfe^?) by admit. *)
    (* case_union _ _. *)
    (* 2: { apply sb_trans. } *)
    admit. }
  rewrite <- seqA with (r2:=⦗Sc⦘) (r3:=psc_base G). rewrite <- seqA.   
  rewrite SC_SB_RFE_PSCB.
  rewrite ct_unit.
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
