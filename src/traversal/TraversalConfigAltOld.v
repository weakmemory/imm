From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
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
  { tc_init : Init ∩₁ E ⊆₁ C ;
    tc_C_in_E : C ⊆₁ E ;
    tc_sb_C : dom_rel ( sb ⨾ ⦗C⦘) ⊆₁ C ;
    tc_W_C_in_I : C ∩₁ W ⊆₁ I ;
    tc_rf_C : dom_rel ( rf ⨾ ⦗C⦘) ⊆₁ I ;
    tc_sc_C : dom_rel ( sc ⨾ ⦗C⦘) ⊆₁ C ;
    tc_I_in_E : I ⊆₁ E ;
    tc_I_in_W : I ⊆₁ W ;
    tc_fwbob_I : dom_rel ( fwbob ⨾ ⦗I⦘) ⊆₁ C ;
    tc_dr_pb_I : dom_rel ( (detour ∪ rfe) ⨾ (ppo ∪ bob) ⨾ ⦗I⦘) ⊆₁ I ;
    tc_W_ex_sb_I : dom_rel (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗I⦘) ⊆₁ I
  }.

(* move to imm_common.v *)
Lemma bob_ppo_W_sb WF :
  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆ ppo ∪ ppo ^? ;; (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+.
Proof.
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

(* move to imm_common.v *)
Lemma bob_sb :
  (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+ ⨾ ⦗W⦘ ⊆ 
  bob^+ ⨾ (⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘.
Proof.
apply ct_ind_left with (P:= fun r =>  r ⨾ ⦗W⦘).
by auto with hahn.
by arewrite (bob ⊆ bob⁺); basic_solver 12.
intros k H.
rewrite !seqA; rewrite H; clear k H.
relsf; unionL.
- arewrite(bob ⊆ bob^*) at 1; relsf.
- sin_rewrite bob_in_sb.
generalize (@sb_trans G); ins; relsf.
basic_solver 12.
- arewrite (bob ⊆ bob⁺); basic_solver 12.
- generalize (@sb_trans G); basic_solver 12.
Qed.

(* move to imm_common.v *)
Lemma tc_bob :
  bob^+ ⊆ fwbob^+ ∪ ⦗R ∩₁ Acq⦘ ⨾ sb.
Proof.
unfold imm_common.bob.
apply ct_ind_left with (P:= fun r =>  r).
by auto with hahn.
by arewrite (fwbob ⊆ fwbob⁺); basic_solver 12.
intros k H.
rewrite H; clear k H.
relsf; unionL.
- by arewrite (fwbob ⊆ fwbob^*); relsf; basic_solver 12.
- sin_rewrite (fwbob_in_sb).
  generalize (@sb_trans G); ins; relsf; basic_solver 12.
- arewrite (⦗R ∩₁ Acq⦘ ⊆ ⦗R⦘). basic_solver.
  sin_rewrite fwbob_r_sb.
  by arewrite (fwbob ⊆ fwbob^+); basic_solver 21.
- generalize (@sb_trans G); basic_solver 12.
Qed.

Lemma tc_tc_fwbob_I (tc_old : tc_coherent_alt_old) :
  dom_rel (fwbob⁺ ⨾ ⦗I⦘) ⊆₁ C.
Proof.
rewrite ct_end, !seqA.
rewrite (dom_rel_helper (tc_fwbob_I tc_old)).
rewrite fwbob_in_sb.
generalize (@sb_trans G); ins; relsf.
generalize (tc_sb_C tc_old).
basic_solver 12.
Qed.

Lemma tc_W_bob_I (tc_old : tc_coherent_alt_old) :
  dom_rel (⦗W⦘ ⨾ bob⁺ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
rewrite tc_bob; relsf; splits; [| type_solver].
rewrite (dom_rel_helper (tc_tc_fwbob_I tc_old)).
generalize (tc_W_C_in_I tc_old).
basic_solver 12.
Qed.

Lemma tc_I_ar_I_implied_helper_1 WF (tc_old : tc_coherent_alt_old) :
  dom_rel (⦗W⦘ ⨾  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^+ ⨾ ⦗I⦘) ⊆₁ I.
Proof.
rewrite (bob_ppo_W_sb WF).
rewrite crE.
rewrite wf_ppoD at 1 2.
relsf; splits; try type_solver.
arewrite (⦗I⦘ ⊆ ⦗W⦘ ;; ⦗I⦘).
by generalize (tc_I_in_W tc_old); basic_solver.
sin_rewrite bob_sb; relsf; splits.
+ rewrite !seqA.
  arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ sb^?).
  by generalize (tc_W_ex_sb_I tc_old); basic_solver 12.
  generalize (tc_W_bob_I tc_old); basic_solver 12.
+ generalize (tc_W_ex_sb_I tc_old).
  basic_solver 12.
Qed.

Lemma tc_I_ar_I_implied_helper_2  WF WF_SC (tc_old : tc_coherent_alt_old) :
   dom_rel (<|W|> ;; ar⁺ ;; <|I|>) ⊆₁ I.
Proof.
  unfold imm_s.ar, ar_int.
  arewrite (sc ∪ rfe ∪ (bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) ⊆ 
    (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) ∪ (sc ∪ rfe ∪ detour)).
  by basic_solver 12.
  remember (sc ∪ rfe ∪ detour) as srd.
  remember (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) as bps.
  rewrite unionC.
  rewrite path_union1.
  arewrite (srd ∪ srd ⨾ bps⁺ ⊆ srd ⨾ bps^*).
  by rewrite rtE; basic_solver 12.
  relsf; splits.
- generalize (tc_I_ar_I_implied_helper_1 WF tc_old).
  rewrite <- Heqbps; basic_solver 21.
- rewrite !seqA, <- dom_eqv1.
  arewrite (⦗W⦘ ⨾ bps＊ ⨾ (srd ⨾ bps＊)⁺ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (fun _ _ => True)); cycle 1.
  by generalize (tc_W_C_in_I tc_old); basic_solver.
  rewrite inclusion_t_rt.
  arewrite (I ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1.
  apply rt_ind_right with (P:= fun r =>  ⦗W⦘ ⨾ bps＊ ⨾ r ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘).
by auto with hahn.
+ rels.
rewrite rtE; relsf.
subst.
unionL.
type_solver.
rewrite id_union; relsf; unionL.
* rewrite (dom_rel_helper (tc_I_ar_I_implied_helper_1 WF tc_old)); subst.
basic_solver 12.
*
rewrite (ppo_in_sb WF), bob_in_sb.
arewrite_id ⦗W_ex_acq⦘.
arewrite_id ⦗W⦘ at 2.
generalize (@sb_trans G); ins; relsf.
arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘).
basic_solver.
rewrite (dom_rel_helper (tc_sb_C tc_old)).
generalize (tc_W_C_in_I tc_old); basic_solver.
+ intros k H; rewrite !seqA.
rewrite rtE at 2; relsf; unionL; subst srd.

*
rewrite (wf_scD WF_SC).
rewrite (tc_I_in_W tc_old) at 1.
rewrite (dom_r (wf_rfeD WF)).
rewrite (dom_r (wf_detourD WF)).
rewrite id_union; relsf; unionL; try type_solver.

rewrite !seqA.
arewrite (⦗F ∩₁ Sc⦘ ⨾ sc ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⨾ (fun _ _ : actid => True)).
generalize (tc_sc_C tc_old); basic_solver 21.
sin_rewrite H; basic_solver.


* 
rewrite !unionA.

remember (rfe ∪ detour) as rd.
relsf; unionL.
-- cut (sc ⨾ bps^+ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗C ∩₁ F ∩₁ Sc⦘ ;; (fun _ _ : actid => True)).
by intro A; sin_rewrite A; arewrite (C ∩₁ F ∩₁ Sc ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1; sin_rewrite H; basic_solver.
subst bps.
rewrite (ppo_in_sb WF), bob_in_sb.
arewrite_id ⦗W_ex_acq⦘.
arewrite_id ⦗W⦘.
generalize (@sb_trans G); ins; relsf.
rewrite (wf_scD WF_SC), !seqA.
rewrite id_union; relsf; unionL.
++ 
arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⊆  fwbob).
by unfold imm_common.fwbob; mode_solver.
generalize (tc_sc_C tc_old) (tc_fwbob_I tc_old).
basic_solver 21.
++ 
generalize (tc_sc_C tc_old) (tc_sb_C tc_old).
basic_solver 21.

-- cut (rd ⨾ bps^+ ⨾ ⦗I ∪₁ C ∩₁ F ∩₁ Sc⦘ ⊆ ⦗I⦘ ;; (fun _ _ : actid => True)).
by intro A; sin_rewrite A; arewrite (I ⊆₁ I ∪₁ C ∩₁ F ∩₁ Sc) at 1; sin_rewrite H; basic_solver.
subst bps.
rewrite (bob_ppo_W_sb WF); relsf; unionL.
rewrite id_union; relsf; unionL.
by generalize (tc_dr_pb_I tc_old); subst rd; basic_solver 12.
by rewrite wf_ppoD; type_solver.
rewrite id_union; relsf; unionL.
++ arewrite (⦗I⦘ ⊆ ⦗W⦘ ;; ⦗I⦘).
by generalize (tc_I_in_W tc_old); basic_solver.
sin_rewrite bob_sb; relsf; unionL.
** rewrite !seqA.
arewrite ((⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)^? ⨾ ⦗W⦘ ⨾ ⦗I⦘ ⊆ ⦗I⦘ ⨾ (fun _ _ : actid => True)).
by generalize (tc_W_ex_sb_I tc_old); basic_solver 21.
rewrite crE; relsf; unionL.
--- rewrite tc_bob; relsf; unionL.
2: by generalize (tc_dr_pb_I tc_old); subst rd; unfold imm_common.bob; basic_solver 21.
seq_rewrite (dom_rel_helper (tc_tc_fwbob_I  tc_old)).
subst rd; relsf; unionL.
generalize (tc_rf_C tc_old); unfold Execution.rfe; basic_solver 21.
rewrite (dom_l (wf_detourD WF)).
rewrite detour_in_sb.
generalize (tc_sb_C tc_old) (tc_W_C_in_I tc_old); basic_solver 21.
--- rewrite wf_ppoD, !seqA.
seq_rewrite (dom_rel_helper (tc_W_bob_I tc_old)).
generalize (tc_dr_pb_I tc_old).
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
generalize (tc_dr_pb_I tc_old) (tc_W_ex_sb_I tc_old).
basic_solver 21.
++ rewrite (ppo_in_sb WF), bob_in_sb.
arewrite_id ⦗W_ex_acq⦘.
arewrite_id ⦗W⦘.
generalize (@sb_trans G); ins; relsf.
arewrite (⦗C ∩₁ F ∩₁ Sc⦘ ⊆  ⦗C⦘).
basic_solver.
rewrite (dom_rel_helper (tc_sb_C tc_old)).
subst rd; relsf; unionL.
generalize (tc_rf_C tc_old); unfold Execution.rfe; basic_solver 21.
rewrite (dom_l (wf_detourD WF)).
rewrite detour_in_sb.
generalize (tc_sb_C tc_old) (tc_W_C_in_I tc_old); basic_solver 21.

Qed.

End TCCOH_ALT_OLD.
