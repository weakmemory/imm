(******************************************************************************)
(** * Definition of s_IMM PPO  *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.

Set Implicit Arguments.

Section IMM_S_PPO.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'fwbob'" := (fwbob G).
Notation "'bob'" := (bob G).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition ppo := ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪
                       rmw ∪ rmw_dep ;; sb^? ∪ ⦗R_ex⦘ ⨾ sb)⁺ ⨾ ⦗W⦘.

Definition ar_int := bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ 
                     ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

Lemma ppo_in_sb WF: ppo ⊆ sb.
Proof using.
unfold ppo.
arewrite_id ⦗R_ex⦘.
rewrite (addr_in_sb WF), (data_in_sb WF), (ctrl_in_sb WF).
rewrite (rmw_dep_in_sb WF).
arewrite (rfi ⊆ sb).
rewrite (rmw_in_sb WF) at 1.
rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
assert (sb⁺ ⊆ sb) as AA.
{ generalize (@sb_trans G). ins. relsf. }
etransitivity.
2: by apply AA.
apply clos_trans_mori.
generalize (@sb_trans G); ins; relsf.
Qed.

Lemma rmw_in_ppo WF : rmw ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_rmwD WF) at 1.
rewrite <- ct_step.
basic_solver 10.
Qed.

Lemma rmw_in_ppo_loc WF : rmw ⊆ ppo ∩ same_loc.
Proof using.
  apply inclusion_inter_r.
  { by apply rmw_in_ppo. }
  apply (wf_rmwl WF).
Qed.

(* Lemma rmw_sb_W_in_ppo WF : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ppo. *)
(* Proof using. *)
(* unfold ppo; rewrite (wf_rmwD WF). *)
(* rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1. *)
(* rewrite (rmw_in_sb WF) at 1. *)
(* rewrite <- ct_step. *)
(* generalize (@sb_trans G). *)
(* basic_solver 12. *)
(* Qed. *)

Lemma data_in_ppo WF : data ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_dataD WF) at 1.
hahn_frame; econs; basic_solver 12.
Qed.

Lemma R_ex_sb_W_in_ppo : ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  arewrite (⦗R_ex⦘ ⊆ ⦗R⦘ ;; ⦗R_ex⦘).
  { generalize (@R_ex_in_R _ lab). basic_solver. }
  unfold ppo. hahn_frame.
  rewrite <- ct_step. eauto with hahn.
Qed.

(* Lemma rmw_sb_cr_W_in_ppo WF : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo. *)
(* Proof using. *)
(*   rewrite crE. rewrite seq_union_l, seq_union_r, seq_id_l. *)
(*   rewrite (rmw_sb_W_in_ppo WF). *)
(*   rewrite (rmw_in_ppo WF). eauto with hahn hahn_full. *)
(* Qed. *)

Lemma wf_ppoE WF : ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold ppo.
rewrite !seqA, seq_eqvC.
hahn_frame.
seq_rewrite seq_eqvC.
rewrite !seqA.
hahn_frame.
rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
apply inclusion_t_t.
unfold Execution.rfi.
rewrite (wf_rfE WF), (wf_dataE WF), (wf_rmw_depE WF) at 1.
rewrite (wf_addrE WF), (wf_ctrlE WF), (wf_rmwE WF) at 1.
rewrite wf_sbE at 1 2 3 4.
basic_solver 21.
Qed.

Lemma wf_ar_intE WF : ar_int ≡ ⦗E⦘ ⨾ ar_int ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold ar_int.
rewrite (wf_bobE WF), (wf_ppoE WF) at 1.
rewrite (wf_detourE WF), (@wf_sbE G), (wf_rfiE WF).
basic_solver 42.
Qed.

Lemma wf_ppoD: ppo ≡ ⦗R⦘ ⨾ ppo ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold ppo; basic_solver.
Qed.

Lemma fwbob_ppo WF: fwbob ⨾ ppo ⊆ fwbob.
Proof using.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite fwbob_r_sb.
basic_solver.
Qed.

Lemma bob_ppo WF: bob ⨾ ppo ⊆ bob.
Proof using.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite bob_r_sb.
basic_solver.
Qed.

Lemma ar_int_in_sb WF: ar_int ⊆ sb.
Proof using.
unfold ar_int.
rewrite bob_in_sb.
rewrite (ppo_in_sb WF).
arewrite (detour ⊆ sb).
arewrite (rfi ⊆ sb).
basic_solver 21.
Qed.

Lemma ppo_rfi_ppo : ppo ⨾ rfi ⨾ ppo ⊆ ppo.
Proof using.
unfold ppo.
rewrite !seqA.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R⦘ at 2.
arewrite (rfi ⊆ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ∪ rmw_dep ⨾ sb^?∪ ⦗R_ex⦘ ⨾ sb)＊) at 2.
{ rewrite rtE. rewrite <- ct_step. basic_solver 10. }
rewrite inclusion_t_rt at 1.
relsf.
Qed.

Lemma deps_rfi_in_ppo : ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  unfold ppo, Execution.deps.
  hahn_frame.
  apply inclusion_t_t; basic_solver 21.
Qed.

(* TODO: move to a more appropriate place. *)
Lemma rmw_sb_loc_in_rmw_coi WF (SPL : sc_per_loc G) :
  rmw ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ⊆ rmw ;; coi^?.
Proof using.
  rewrite !crE, !seq_union_r, !seq_id_r.
  apply union_mori; [done|].
  rewrite (dom_r (wf_rmwD WF)) at 1. rewrite !seqA.
    by rewrite (w_sb_loc_w_in_coi WF).
Qed.

(* Lemma ppo_alt WF  *)
(*   (RMW_DEPS : rmw ⊆ deps) *)
(*   (DEPS_RMW_FAIL : rmw_dep ⨾ sb ⊆ ctrl) :  *)
(*   ppo ≡ ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘. *)
(* Proof using. *)
(*   unfold ppo. *)
(* Admitted. *)

(* generalize (@sb_trans G); ins. *)
(* unfold ppo. *)
(* split. *)
(* 2: by hahn_frame; apply inclusion_t_t; basic_solver 12. *)
(* rewrite RMW_DEPS; unfold Execution.deps. *)
(* rewrite path_ut_first; relsf; unionL. *)
(* by hahn_frame; apply inclusion_t_t; basic_solver 12. *)
(* arewrite ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ (data ∪ addr ∪ ctrl) ∪ rmw_dep ⨾ sb^?) ⊆ sb). *)
(* { rewrite (data_in_sb WF), (addr_in_sb WF), (ctrl_in_sb WF). *)
(*   arewrite (rfi ⊆ sb). *)
(*   rewrite (rmw_dep_in_sb WF). *)
(*   relsf. } *)
(* relsf. *)
(* rewrite (dom_r (wf_rmw_depD WF)), !seqA. *)
(* rewrite (crE sb) at 2; relsf; unionL. *)
(* by rewrite R_ex_in_R; type_solver. *)
(* hahn_frame. *)
(* sin_rewrite RMW_CTRL_FAIL. *)
(* rewrite DEPS_RMW_FAIL. *)
(* rewrite ct_end. *)
(* apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42. *)
(* Qed. *)

Lemma bob_in_ar_int : bob ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma ppo_in_ar_int : ppo ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma detour_in_ar_int : detour ⊆ ar_int.
Proof using. unfold ar_int. basic_solver. Qed.

Lemma w_ex_acq_sb_w_in_ar_int : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma bob_ppo_W_sb WF :
  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆ ppo ∪ ppo ^? ;; (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+.
Proof using.
  arewrite (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆
                (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) ∪ ppo).
  basic_solver 12.
  apply ct_ind_left with (P:= fun r =>  r).
  { auto with hahn. }
  { arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
    arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺) at 2.
    basic_solver 12. }
  intros k H. rewrite H; clear k H; rewrite crE; relsf; unionL.
  { rewrite (bob_ppo WF). 
    arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
    basic_solver. }
  { rewrite (wf_ppoD) at 1. type_solver. }
  { rewrite (wf_ppoD) at 1 2. type_solver. }
  arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*); relsf.
  { sin_rewrite (bob_ppo WF). 
    arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*); relsf. }
  { arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*) at 1; relsf. }
  { rewrite (wf_ppoD) at 1. type_solver. }
  { basic_solver 12. }
  rewrite (wf_ppoD) at 1 2. type_solver.
Qed.

Lemma bob_ppo_W_ex_rfi_W_sb WF :
  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ⊆
  ppo ∪ ppo ^? ;; (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)^+.
Proof using.
  assert (⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb ⊆
                 ppo ∪ ((bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺ ∪
                 ppo ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)⁺)) as AA.
  { arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R ∩₁ Acq⦘ ;; ⦗R ∩₁ Acq⦘) at 1 by basic_solver.
    arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
    unionR right -> left.
    rewrite <- ct_ct. rewrite <- !ct_step.
    basic_solver 10. }

  arewrite (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆
                (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘) ∪ ppo).
  { basic_solver 12. }
  apply ct_ind_left with (P:= fun r =>  r).
  { auto with hahn. }
  { rewrite <- ct_step. basic_solver 10. }
  intros k H. rewrite H; clear k H; rewrite crE; relsf; unionL.
  { rewrite (bob_ppo WF). 
    unionR right -> left. rewrite <- ct_step. basic_solver. }
  { rewrite (wf_ppoD) at 1. type_solver. }
  { rewrite (ppo_in_sb WF) at 1.
    rewrite !seqA. apply AA. }
  { rewrite (wf_ppoD) at 1 2. type_solver. }
  2: sin_rewrite (bob_ppo WF). 
  1-3,5: unionR right -> left; rewrite <- ct_ct at 2;
    rewrite <- ct_step at 2; basic_solver 10.
  { rewrite (wf_ppoD) at 1. type_solver. }
  { arewrite (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆ sb) at 1.
    { rewrite bob_in_sb. arewrite (rfi ⊆ sb). basic_solver. }
    rewrite (ppo_in_sb WF) at 1.
    generalize (@sb_trans G); ins; relsf. }
  { basic_solver 10. }
  rewrite (wf_ppoD) at 1 2; type_solver.
Qed.

Lemma ppo_helper WF :
  ppo ⊆ ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ∪ rmw_dep ⨾ sb^?)＊ ⨾  
             (⦗R_ex⦘ ⨾ sb)^? ⨾ ⦗W⦘.
Proof using.
  unfold ppo.
  rewrite path_ut_first.
  rewrite !seq_union_l, !seq_union_r; unionL.
  { basic_solver 21. }
  hahn_frame_l.
  hahn_frame_l.
  hahn_frame_r.
  rewrite (data_in_sb WF).
  rewrite (ctrl_in_sb WF).
  rewrite (addr_in_sb WF).
  rewrite (rmw_dep_in_sb WF).
  rewrite (rmw_in_sb WF).
  arewrite (rfi ⊆ sb).
  arewrite_id ⦗R_ex⦘ at 2.
  generalize (@sb_trans G); ins; relsf.
Qed.

Lemma rf_rmw_sb_loc_in_rf_ppo_loc WF (RMWREX : dom_rel rmw ⊆₁ R_ex) :
  rf ;; rmw ;; sb ∩ same_loc ;; <|W|> ⊆ rf ;; ppo ∩ same_loc.
Proof using.
  arewrite (rmw ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ (rmw ⨾ sb ⨾ ⦗W⦘) ∩ same_loc).
  { arewrite (rmw ⊆ rmw ∩ same_loc).
    { apply inclusion_inter_r; [done|]. apply (wf_rmwl WF). }
    generalize (@same_loc_trans _ lab). basic_solver. }
  rewrite (dom_rel_helper RMWREX). rewrite !seqA.
  rewrite (rmw_in_sb WF).
  arewrite (sb ⨾ sb ⊆ sb).
  { generalize (@sb_trans G). basic_solver. }
    by rewrite R_ex_sb_W_in_ppo.
Qed.

Lemma rmw_in_ar_int WF : rmw ⊆ ar_int.
Proof using.
  unfold ar_int.
  rewrite (rmw_in_ppo WF). eauto with hahn.
Qed.

Lemma rfe_rmw_in_rfe_ar_int_ct WF : rfe ⨾ rmw ⊆ (rfe ∪ ar_int)⁺.
Proof using.
  rewrite rmw_in_ar_int; auto.
  arewrite (ar_int ⊆ rfe ∪ ar_int) at 1.
  arewrite (rfe ⊆ rfe ∪ ar_int) at 1.
  do 2 (rewrite ct_begin; rewrite rtE).
  rewrite <- ct_step. basic_solver 10.
Qed.

Lemma ar_int_rfe_rfrmw_in_ar_int_rfe_ct WF : (rfe ∪ ar_int) ;; rf ;; rmw ⊆ (rfe ∪ ar_int)⁺.
Proof using.
  remember (rfe ∪ ar_int) as ax.
  assert (sb ;; sb ⊆ sb) as AA.
  { apply transitiveI. apply sb_trans. }
  
  assert (rfi ;; rmw ⊆ sb) as BB.
  { arewrite (rfi ⊆ sb). by rewrite rmw_in_sb. }

  rewrite rfi_union_rfe.
  rewrite seq_union_l, seq_union_r.
  unionL.
  2: { rewrite rfe_rmw_in_rfe_ar_int_ct; auto.
       arewrite (ax ⊆ ax^?) at 1. subst ax. relsf. }
  subst ax.
  rewrite !seq_union_l.
  unionL.
  { rewrite (dom_l (wf_rfiD WF)).
    rewrite (dom_r (wf_rfeD WF)).
    type_solver. }
  unfold ar_int at 1.
  rewrite !seq_union_l.
  unionL.
  5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
  3: { rewrite (wf_detourD WF).
       rewrite (wf_rfiD WF). type_solver. }
  { unfold imm_bob.bob at 1.
    rewrite !seq_union_l, !seqA.
    unionL.
    2: { rewrite BB, AA.
         arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
         rewrite bob_in_ar_int. rewrite <- ct_step. eauto with hahn. }
    rewrite fwbob_rfi_rmw_in_fwbob; auto.
    rewrite fwbob_in_bob. rewrite bob_in_ar_int. eauto with hahn. }
  { rewrite (rmw_in_ppo WF), ppo_rfi_ppo. rewrite <- ct_step.
    rewrite ppo_in_ar_int. eauto with hahn. }
  arewrite_id ⦗W⦘. rewrite seq_id_l.
  rewrite (dom_r (wf_rmwD WF)).
  sin_rewrite BB. sin_rewrite AA.
  rewrite <- ct_step.
  rewrite w_ex_acq_sb_w_in_ar_int. eauto with hahn.
Qed.

Lemma ar_int_rfe_rfrmw_rt_in_ar_int_rfe_ct WF :
  (rfe ∪ ar_int) ;; (rf ;; rmw)^* ⊆ (rfe ∪ ar_int)⁺.
Proof using.
  apply rt_ind_left with (P:=fun r => (rfe ∪ ar_int) ⨾ r).
  { eauto with hahn. }
  { by rewrite seq_id_r, <- ct_step. }
  ins. sin_rewrite ar_int_rfe_rfrmw_in_ar_int_rfe_ct; auto.
  rewrite ct_end at 1. rewrite !seqA. rewrite H.
  relsf.
Qed.

Lemma ar_int_rfe_ct_rfrmw_rt_in_ar_int_rfe_ct WF :
  (rfe ∪ ar_int)⁺ ;; (rf ;; rmw)^* ⊆ (rfe ∪ ar_int)⁺.
Proof using.
  rewrite ct_end at 1. rewrite !seqA. rewrite ar_int_rfe_rfrmw_rt_in_ar_int_rfe_ct; auto.
  relsf.
Qed.

End IMM_S_PPO.
