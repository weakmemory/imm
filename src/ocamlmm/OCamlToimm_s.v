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
Notation "'hb'" := G.(hb).

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

Hypothesis LSM : forall l,
    << LM : Loc_ l \₁ Init  ⊆₁ Rlx \₁ Sc >> \/
    << LM : Loc_ l \₁ Init  ⊆₁ Sc >>.

Hypothesis WSCRMW : W∩₁Sc ≡₁ codom_rel rmw.
Hypothesis RMWSC  : rmw ≡ ⦗Sc⦘ ⨾ rmw ⨾ ⦗Sc⦘.

Hypothesis WRLXF : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acq/Rel|> ;; immediate sb).
Hypothesis RSCF : R∩₁Sc ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

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
  intros x y [HH AA].
  apply seq_eqv_l in HH. destruct HH as [SCX HH].
  apply seq_eqv_r in HH. destruct HH as [HH RMWY].
  destruct RMWY as [z ZY].
  apply seq_eqv_l. split; auto.
  assert (Sc z) as SCZ.
  { apply RMWSC in ZY. generalize ZY. basic_solver. }

  assert (E z) as EZ.
  { apply (dom_l WF.(wf_rmwE)) in ZY.
    generalize ZY. basic_solver. }
  assert (R z) as EW.
  { apply (dom_l WF.(wf_rmwD)) in ZY.
    generalize ZY. type_solver. }

  exists z. split.
  2: { apply seq_eqv_l. split; auto.
       apply rmw_in_sb; auto. }
  assert (exists v, rf v z) as [v RF].
  { apply IPC. split; auto. }
  destruct (classic (x = v)) as [|NEQ]; desf.

  assert (E v) as EV. 
  { apply WF.(wf_rfE) in RF. generalize RF. basic_solver. }
  assert (W v) as WV. 
  { apply WF.(wf_rfD) in RF. generalize RF. basic_solver. }
  
  set (GG := WV).
  apply is_w_loc in GG. desf.
  
  assert (loc z = Some l) as LOCZ.
  { rewrite <- GG. symmetry.
    apply wf_rfl; auto. }
  
  destruct (classic (Init v)) as [INIT|NINIT].
  { admit. }
  assert (Sc v) as SCV.
  { specialize (LSM l).
    destruct LSM as [CC|CC].
    2: { apply CC. split; auto. }
    exfalso.
    assert (~ is_init z) as NINITZ.
    { eapply read_or_fence_is_not_init; eauto. }
    assert ((Loc_ l \₁ Init) z) as DD.
    { split; auto. }
   apply CC in DD.
   destruct DD. desf. }

  assert (codom_rel rmw v) as RMWV.
  { apply WSCRMW. split; auto. }

  assert (E x) as EX.
  { apply (dom_l WF.(wf_coE)) in HH.
    generalize HH. basic_solver. }
  assert (W x) as WX.
  { apply (dom_l WF.(wf_coD)) in HH.
    generalize HH. basic_solver. }

  eapply wf_co_total in NEQ; eauto.
  3: { split; [split|]; auto. }
  2: { split; [split|]; auto.
       rewrite GG, <- LOCZ.
       arewrite (loc z = loc y) by (by apply WF.(wf_rmwl)).
       apply WF.(wf_col); auto. }

  cdes IPC. cdes IC.
  assert (sc_per_loc G) as SCPL by (by apply coherence_sc_per_loc).
  
  exfalso.
  destruct NEQ as [NEQ|NEQ].
  2: { eapply atomicity_alt; eauto.
       split; eauto.
       do 2 (eexists; split; eauto). }
  apply AA with (c:=v).
  { apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto. }
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  2: { eexists; eauto. }
  apply rf_rmw_in_co; auto.
  eexists. eauto.
Admitted.

Lemma s_imm_consistentimplies_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  red. splits; auto.

  rewrite co_in_eco.
  2: rewrite fr_in_eco. 
  1,2: by arewrite (eco ⊆ eco^?); apply Cint.

Admitted.

End OCamlMM_TO_IMM_S.
