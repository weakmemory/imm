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
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Init'" := (fun a => is_true (is_init a)).

Notation "'hbo'" := G.(OCaml.hb).

Hypothesis LSM : forall l,
    << LM : Loc_ l \₁ Init  ⊆₁ Rlx \₁ Sc >> \/
    << LM : Loc_ l \₁ Init  ⊆₁ Sc >>.

Hypothesis WSCRMW : W∩₁Sc ≡₁ codom_rel rmw.
Hypothesis RMWSC  : rmw ≡ ⦗Sc⦘ ⨾ rmw ⨾ ⦗Sc⦘.

Hypothesis WRLXF : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acq/Rel|> ;; immediate sb).
Hypothesis RSCF : R∩₁Sc ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

Lemma init_begins_co (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  forall l, (E ∩₁ Loc_ l ∩₁ W ∩₁ Init) × ((E ∩₁ Loc_ l ∩₁ W) \₁ Init) ⊆ co.
Proof.
  intros l. intros w0 w [w0_props w_props].
  (* how to write these properly? *)
  destruct w_props as [[[]]].   
  destruct w0_props as [[[]]].   
  destruct (classic (w0 = w)) as [WEQ|WNEQ].
  { exfalso. rewrite WEQ in H6. auto. }
  eapply wf_co_total in WNEQ; eauto. 
  3: { split; [split|];  auto. }
  2: { split; [split|]; auto. rewrite <- H0 in H4. auto. }
  destruct WNEQ as [co_w0_w | co_w_w0]; auto.
  assert (sb_w0_w: sb w0 w).
  { destruct w0.
    { destruct w.
      { exfalso. auto. }
      unfold ext_sb; auto. unfold Execution.sb. basic_solver.
    }
    destruct w; exfalso; auto.     
  }
  exfalso.
  cdes IPC. cdes IC. red in Cint. red in Cint. 
  apply Cint with (x:=w0). red. exists w. split.    
  assert (hb_w0_w: (sb ∪ sw)  w0 w). 
  { basic_solver. } (* ? how to employ obvious r <<= r+ instead of this hack? *)
  { red. basic_solver. }
  red. right. red. red. left. red. right. basic_solver. 
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
  rewrite WSCRMW.
  intros w1 w2 [co_rmw_w1_w2 imm_w1_w2].
  apply seq_eqv_l in co_rmw_w1_w2. destruct co_rmw_w1_w2 as [SCW1 co_rmw_w1_w2].
  apply seq_eqv_r in co_rmw_w1_w2. destruct co_rmw_w1_w2 as [co_rmw_w1_w2 RMWW2].
  destruct RMWW2 as [r2 rw_r2_w2].  
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
    apply (same_loc_trans co_rmw_w1_w2 rw_r2_w2).
  }
  
  destruct (classic (Init w')) as [INIT|NINIT].
  { (* show a cycle: r2 -hb- w2 *)
    assert (co_w'_w1: co w' w1).
    { specialize (init_begins_co WF IPC).
      intros H. apply H with (l:=l). split.
      { do 3 (split; auto). }
      split; auto.
      { split.
        2: { apply WF.(wf_coD) in co_rmw_w1_w2.
             generalize co_rmw_w1_w2. basic_solver. }
        split.
        { apply WF.(wf_coE) in co_rmw_w1_w2.
          generalize co_rmw_w1_w2. basic_solver. }
        red in same_loc_w1_w'. rewrite same_loc_w1_w'.  auto. }
      destruct (classic (is_init w1)).
      2: {auto. }
      exfalso.
      assert (same_inits: w1 = w').
      { apply (init_same_loc WF); auto.  }
      auto.
    }
    exfalso.
    assert (atom: rmw ∩ (fr ⨾ co) ⊆ ∅₂). (* ? is there a way to not duplicate? *)
    { apply atomicity_alt; auto.
      all: cdes IPC; cdes IC; auto. 
      apply coherence_sc_per_loc in Cint. auto.
    }
    red in atom. apply (atom r2 w2). split; auto. 
    red. exists w1. split.
    - red. basic_solver.
    - auto.
  }

  assert (Sc w') as SCW'.
  { specialize (LSM l).
    destruct LSM as [CC|CC].
    2: { apply CC. split; auto. }
    exfalso.
    assert (~ is_init r2) as NINITR2.
    { eapply read_or_fence_is_not_init; eauto. }
    assert ((Loc_ l \₁ Init) r2) as DD.
    { split; auto. }
    apply CC in DD.
    destruct DD. auto. (* ? desf *)  }   

  assert (codom_rel rmw w') as RMWW'.
  { apply WSCRMW. split; auto. }

  assert (E w1) as EW1.
  { apply (dom_l WF.(wf_coE)) in co_rmw_w1_w2.
    generalize co_rmw_w1_w2. basic_solver. }
  assert (W w1) as WW1.
  { apply (dom_l WF.(wf_coD)) in co_rmw_w1_w2.
    generalize co_rmw_w1_w2. basic_solver. }

  eapply wf_co_total in NEQ; eauto.
  3: { split; [split|]; auto. }
  2: { split; [split|]; auto. }
  
  cdes IPC. cdes IC.
  assert (sc_per_loc G) as SCPL by (by apply coherence_sc_per_loc).
  
  exfalso.
  destruct NEQ as [NEQ|NEQ].
  2: { eapply atomicity_alt; eauto.
       split; eauto.
       do 2 (eexists; split; eauto). }
  apply imm_w1_w2 with (c:=w').
  { apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto. }
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  2: { eexists; eauto. }
  apply rf_rmw_in_co; auto.
  eexists. eauto.
Qed. 
  
Lemma s_imm_consistentimplies_ocaml_coherent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_coherent G.
Proof.
   cdes IPC. cdes IC. red in Cint. 
   red. unfold OCaml.hb.
   assert (dismiss_hbinit:
             ocaml_coherent G <->
             irreflexive ((sb ∪ (on_sc G (coe ∪ rf))) ;; (co ∪ fr))).
   {admit. }
   apply dismiss_hbinit.
   assert (seq_dist_union_l: forall r1 r2 r3 : relation actid,
              (r1 ∪ r2) ;; r3 ≡ r1;;r3 ∪ r2;;r3).
   {admit. }
   assert (seq_dist_union_r: forall r1 r2 r3 : relation actid,
              r1 ;; (r2 ∪ r3) ≡ r1;;r2 ∪ r1;;r3).
   {admit. }
   rewrite seq_dist_union_l. 
   red. intros x H.
   red in Cint. apply Cint with (x:=x). unfold Execution_eco.eco.
   destruct H.
   { destruct H as [y [sb_x_y eco'_y_x]].
     apply sb_in_hb in sb_x_y. 
     exists y. split; auto. red. right.
     apply unionA.              (* ? why rewrite fails here ? *)
     red. right. apply seq_dist_union_l. (* and here *)
     basic_solver.
   }
   unfold on_sc in H. apply seqA in H.
   apply seq_eqv_l in H.
   destruct H as [SCx [y [hb'_x_y eco_y_x]]].
   apply seq_eqv_r in hb'_x_y. destruct hb'_x_y as [hb'_x_y SCy]. 
   assert (hb_x_y: hb x y). 
   { red in hb'_x_y. destruct hb'_x_y as [coe_x_y | rf_x_y].
     { apply inclusion_minus_rel in coe_x_y.
       apply ((co_sc_in_hb WF IPC) x y). 
       basic_solver.
     }
     red. unfold imm_s_hb.sw. apply ct_step. red. right.
     exists x. split.
     { red. unfold imm_s_hb.rs.
       assert (REL_x: Rel x).
       { unfold is_rel. unfold is_sc in SCx. basic_solver 100.  }
       assert (W_x: W x).
       { apply WF.(wf_rfD) in rf_x_y.
         generalize rf_x_y. basic_solver.
       }
       assert (clos_refl_trans_opt: forall r r' : relation actid, r ⊆ r ⨾ clos_refl_trans r').
       { intros r r'. basic_solver 50. }
       (* ? how to simplify it ? *)
       apply seq_eqv_l; split; auto. 
       exists x. split; auto.
       apply seq_eqv_l; split; auto. 
       exists x. split; auto.
       apply clos_refl_trans_opt. 
       basic_solver. 
     }
     apply seqA. apply seq_eqv_r; split; auto. 
     exists y. split; auto.
     unfold is_acq. unfold is_sc in SCy. basic_solver 100. 
   }
   exists y. split; auto.
   red. right. apply unionA. red. right.
   apply seq_dist_union_l.
   basic_solver. 
Admitted.


Lemma s_imm_consistentimplies_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  red. splits; auto.
  (* 3: {apply (s_imm_consistentimplies_ocaml_causal WF IPC). }  *)
  
  (* rewrite co_in_eco. *)
  (* 2: rewrite fr_in_eco. *)
  (* 1,2: by arewrite (eco ⊆ eco^?); apply Cint. *)

Admitted.

End OCamlMM_TO_IMM_S.
