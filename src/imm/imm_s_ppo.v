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
Remove Hints plus_n_O.

Section IMM_S_PPO.

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

Notation "'lab'" := G.(lab).
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
                              rmw ;; ((sb ∩ same_loc) ⨾ ⦗W⦘)^? ∪ rmw_dep ;; sb^?)⁺ ⨾ ⦗W⦘.

Definition ar_int := bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ 
                     ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

Lemma ppo_in_sb WF: ppo ⊆ sb.
Proof using.
unfold ppo.
rewrite (addr_in_sb WF), (data_in_sb WF), (ctrl_in_sb WF).
rewrite (rmw_dep_in_sb WF).
arewrite (rfi ⊆ sb).
rewrite WF.(rmw_in_sb).
rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
assert (sb⁺ ⊆ sb) as AA.
{ generalize (@sb_trans G). ins. relsf. }
etransitivity.
2: by apply AA.
apply clos_trans_mori.
generalize (@sb_trans G); ins; relsf.
generalize (@sb_trans G). basic_solver 10.
Qed.

Lemma rmw_in_ppo WF : rmw ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_rmwD WF) at 1.
rewrite R_ex_in_R at 1.
rewrite <- ct_step.
basic_solver 10.
Qed.

(* Lemma rmw_sb_W_in_ppo WF : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ppo. *)
(* Proof. *)
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

(* Lemma R_ex_sb_in_ppo WF : ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo. *)
(* Proof using. *)
(*   arewrite (⦗R_ex⦘ ⊆ ⦗R⦘ ;; ⦗R_ex⦘) by type_solver. *)
(*   unfold ppo. hahn_frame. rewrite <- ct_step. eauto with hahn. *)
(* Qed. *)

(* Lemma rmw_sb_cr_W_in_ppo WF : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo. *)
(* Proof using. *)
(*   rewrite crE. rewrite seq_union_l, seq_union_r, seq_id_l. *)
(*   rewrite WF.(rmw_sb_W_in_ppo). *)
(*   rewrite WF.(rmw_in_ppo). eauto with hahn hahn_full. *)
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
arewrite_id ⦗W⦘ at 2.
arewrite_id ⦗R⦘ at 2.
arewrite (rfi ⊆ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^? ∪ rmw_dep ⨾ sb^?)＊) at 2.
rewrite inclusion_t_rt at 1.
relsf.
Qed.

Lemma deps_rfi_in_ppo : ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  unfold ppo, Execution.deps.
  hahn_frame.
  apply inclusion_t_t; basic_solver 21.
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
by auto with hahn.
- arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
  arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺) at 2.
  basic_solver 12.
- intros k H. rewrite H; clear k H; rewrite crE; relsf; unionL.
+ rewrite (bob_ppo WF). 
  arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
  basic_solver.
+ rewrite (wf_ppoD) at 1. type_solver.
+ rewrite (wf_ppoD) at 1 2. type_solver.
+ arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*); relsf.
+ sin_rewrite (bob_ppo WF). 
  arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*); relsf.
+ arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^*) at 1; relsf.
+ rewrite (wf_ppoD) at 1. type_solver.
+ basic_solver 12.
+ rewrite (wf_ppoD) at 1 2. type_solver.
Qed.

End IMM_S_PPO.
