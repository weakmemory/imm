(******************************************************************************)
(** * Compilation correctness from the IMM memory model to the TSO model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events Execution Execution_eco.
Require Import TSO.
Require Import imm_common imm_hb imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section immToTSO.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'coi'" := G.(coi).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).


(* imm *)
Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).
Notation "'rs'" := G.(rs).
Notation "'hb'" := G.(hb).
Notation "'ppo'" := G.(ppo).
Notation "'psc'" := G.(psc).
Notation "'bob'" := G.(bob).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* tso *)
Notation "'ppot'" := G.(TSO.ppo).
Notation "'fence'" := G.(fence).
Notation "'implied_fence'" := G.(implied_fence).
Notation "'hbt'" := G.(TSO.hb).
Notation "'MFENCE'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

Hypothesis CON: TSOConsistent G.

Lemma WF : Wf G.
Proof. apply CON. Qed.

(******************************************************************************)
(** * coherence   *)
(******************************************************************************)

Lemma release_in : release ⊆ sb^? ;; <|W|> ;; (ppot ∪ rfe)^*.
Proof.
unfold imm_hb.release, imm_hb.rs.
arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⊆ sb^?) by basic_solver.
arewrite (⦗W⦘ ⊆ ⦗W⦘ ;; ⦗W⦘) at 1. 
by basic_solver.
hahn_frame; relsf; unionL.
rewrite rt_begin; rewrite TSO.ppo_alt; basic_solver 12.
rewrite (dom_r (wf_rmwD WF)).
rewrite <- !seqA.
rewrite <- rt_seq_swap.
arewrite_id ⦗W⦘ at 2; rels.
rewrite <- (rt_of_rt (ppot ∪ rfe)).
apply inclusion_rt_rt.
rewrite rfi_union_rfe; relsf; unionL.
- arewrite (rfi ⊆ sb).
  rewrite (dom_r (wf_rmwD WF)).
  rewrite (rmw_in_sb WF).
  generalize (@sb_trans G).
  rewrite rt_begin; rewrite TSO.ppo_alt; basic_solver 21.
- rewrite (wf_rfeD WF).
  rewrite (dom_r (wf_rmwD WF)).
  rewrite rt_begin.
  rewrite rt_begin.
  rewrite rt_begin.
  rewrite (rmw_in_sb WF).
  rewrite TSO.ppo_alt; basic_solver 42.
Qed.

Lemma sw_in : sw ⊆ sb ∪ sb^? ;; <|W|> ;; (ppot ∪ rfe)^+ ;; <|R|> ;; sb^?.
Proof.
generalize (@sb_trans G); ins.
unfold imm_hb.sw.
rewrite (dom_r (wf_releaseD WF)).
rewrite release_in.
arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ sb^?) by basic_solver.
relsf; unionL.
- rewrite rtE; relsf; unionL.
by arewrite (rfi ⊆ sb); basic_solver 12.
rewrite path_ut_last at 1; relsf; unionL.
rewrite TSO.ppo_in_sb at 1.
arewrite (rfi ⊆ sb); relsf; basic_solver 21.
rewrite TSO.ppo_in_sb at 2.
rewrite (dom_r (wf_rfiD WF)); rewrite (dom_r (wf_rfeD WF)) at 2; rewrite !seqA.
arewrite (rfi ⊆ sb).
arewrite_id ⦗W⦘ at 2.
relsf.
arewrite (⦗R⦘ ⊆ ⦗R⦘ ;; ⦗R⦘) at 2.
basic_solver.
arewrite (⦗R⦘ ⨾ sb ⨾ ⦗R⦘ ⊆ ppot).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot ⊆ (ppot ∪ rfe)^*) at 2.
arewrite (rfe ⊆ (ppot ∪ rfe)^+) at 2.
relsf.
- rewrite (wf_rfeD WF) at 2; rewrite !seqA.
arewrite (⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot ⊆ (ppot ∪ rfe)^*) at 2.
arewrite (rfe ⊆ (ppot ∪ rfe)^+) at 3.
relsf.
Qed.

Lemma hb_in : hb ⊆ sb ∪ sb^? ;; <|W|> ;; (ppot ∪ rfe)^+ ;; <|R|> ;; sb^?.
Proof.
generalize (@sb_trans G); ins.
unfold imm_hb.hb.
rewrite sw_in, <- !unionA; rels.
apply inclusion_t_ind_right.
basic_solver.

relsf; rewrite !seqA; relsf; unionL.
1,2,3: basic_solver 21.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot).
case_refl _; [type_solver| rewrite TSO.ppo_alt; basic_solver 21].
arewrite (ppot ⊆ (ppot ∪ rfe)^*) at 2.
arewrite ((ppot ∪ rfe)^+ ⊆ (ppot ∪ rfe)^*) at 1.
relsf.
Qed.

Lemma Coherence : coherence G.
Proof.
generalize (@sb_trans G); ins.
generalize (eco_trans WF); ins.
cdes CON; unfold TSO.hb in *.
apply coherence_alt.
rewrite hb_in; relsf; unionL.
- apply sb_irr.
- rotate 2; relsf.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)^*) at 1.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); apply SC_PER_LOC.
- rewrite (wf_rfeD WF) at 2; rewrite !seqA; rotate 1.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)^*).
arewrite (rfe ⊆ (ppot ∪ rfe)^*) at 4.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); rewrite (co_in_eco); relsf.
- arewrite (co ⨾ rfe^? ⊆ co ⨾ rfe^? ⨾ ⦗RW⦘).
rewrite (dom_r (wf_rfeD WF)).
rewrite (dom_r (wf_coD WF)).
basic_solver 12.
rewrite (dom_l (wf_coD WF)).
rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
rotate 1.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)^*).
arewrite (rfe ⊆ (ppot ∪ rfe)^*) at 4.
rotate 1; relsf.
arewrite (ppot ∪ rfe ⊆ (ppot ∪ rfe ∪ co)).
arewrite (co ⊆ (ppot ∪ rfe ∪ co)^*) at 2.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
- arewrite (rfe ⊆ rf); rewrite (rf_in_eco); rewrite (fr_in_eco); relsf.
- arewrite (fr ⨾ rfe^? ⊆ fr ⨾ rfe^? ⨾ ⦗RW⦘).
rewrite (dom_r (wf_rfeD WF)).
rewrite (dom_r (wf_frD WF)).
basic_solver 12.
rewrite (dom_l (wf_frD WF)).
rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗R⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
rotate 1.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ (ppot ∪ rfe)^*).
arewrite (rfe ⊆ (ppot ∪ rfe)^*) at 4.
rotate 1; relsf.
arewrite (ppot ∪ rfe ⊆ (ppot ∪ rfe ∪ fr)).
arewrite (fr ⊆ (ppot ∪ rfe ∪ fr)^*) at 2.
relsf; eapply acyclic_mon; [edone|basic_solver 12].
Qed.

(******************************************************************************)
(** * global acyclicity condition   *)
(******************************************************************************)

Lemma eco_in : eco ⊆ sb ∪ hbt^+ ;; sb^?.
Proof.
unfold Execution_eco.eco.
rewrite rfi_union_rfe.
arewrite (rfi ⊆ sb).
rewrite ct_begin.
rewrite rt_begin.
unfold TSO.hb.
basic_solver 40.
Qed.

Lemma psct : psc ⊆ sb ∪ sb ;; hbt^+ ;; sb.
Proof.
generalize (@sb_trans G); ins.
unfold imm.psc.
rewrite (wf_ecoD WF), !seqA.
rewrite eco_in.
rewrite hb_in.
arewrite (ppot ∪ rfe ⊆ hbt).
unfold TSO.hb; basic_solver 12.
relsf; unionL.
1: by unionR left; basic_solver 21.
all: unionR right.
- type_solver 21.
- basic_solver 21.
- rewrite !seqA.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^*) at 1.
relsf; type_solver 21.

- type_solver 21.
- rewrite !seqA.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite_id !⦗RW⦘; rels.
arewrite (⦗R⦘ ⨾ sb^? ⨾ sb ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^*) at 1.
relsf; type_solver 21.
- rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^*) at 1.
relsf; type_solver 21.
- rewrite !seqA.
arewrite (⦗R⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^*) at 1.
rewrite (dom_r (wf_ct_hbD WF)) at 1; rewrite !seqA.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppot^?).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot^? ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^*) at 1.
relsf; type_solver 21.
Qed.

Lemma ct_psct : 
  (sb^? ⨾ psc ⨾ sb^?)^+ ⊆ 
       sb^? ;; <|MFENCE|> ;; (sb ∪ sb ;; hbt^+ ;; sb) ;; <|MFENCE|> ;; sb^?.
Proof.
generalize (@sb_trans G); ins.

rewrite (@wf_pscD G), psct.
apply inclusion_t_ind_right.
basic_solver 21.
relsf; rewrite !seqA.
unionL.
1: unionR left; basic_solver 21.
all: unionR right.
1,2: basic_solver 42.
rewrite (dom_r (wf_ct_hbD WF)) at 1.
rewrite (dom_l (wf_ct_hbD WF)) at 2.
rewrite !seqA; relsf.
arewrite_id  ⦗MFENCE⦘ at 2.
relsf.
arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^* ) at 1.
relsf; basic_solver 21.
Qed.


Lemma C_EXT : acyc_ext G.
Proof.
generalize (@sb_trans G); ins.
apply (acyc_ext_helper WF).
arewrite (rfe ⊆ hbt⁺).
rewrite (ar_int_in_sb WF); relsf.
arewrite (⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppot).
rewrite TSO.ppo_alt; basic_solver 21.
arewrite (ppot ⊆ hbt⁺).
unfold TSO.hb; rewrite <- ct_step; basic_solver 12.
rewrite unionA; rels.
apply acyclic_union1.
- red.
rewrite ct_psct; relsf; unionL.
by generalize (sb_irr); basic_solver 21.
rewrite (wf_ct_hbD WF); rotate 4.
arewrite_id ⦗MFENCE⦘ at 1.
relsf.
arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
rels.
red; rels; eapply CON.
- red; rels; eapply CON.
- rewrite ct_psct; relsf.
rewrite !seqA.
rewrite (dom_r (wf_ct_hbD WF)) at 2.
rewrite (dom_l (wf_ct_hbD WF)) at 3.
rewrite !seqA; relsf.
arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb^? ⨾ ⦗RW⦘ ⊆ fence).
case_refl _; [type_solver|vauto].
arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
arewrite (hbt^+ ⊆ hbt^* ) at 2.
relsf.
arewrite (sb^? ⨾ ⦗MFENCE⦘ ⨾ sb ⊆ sb^?).
basic_solver.
arewrite (⦗MFENCE⦘ ⨾ sb^? ⨾ hbt⁺ ⊆ ⦗MFENCE⦘ ⨾ sb ⨾ hbt⁺).
rewrite (dom_l (wf_ct_hbD WF)) at 1; type_solver 12.
rels.
rewrite (wf_ct_hbD WF); rotate 1.
arewrite (⦗RW⦘ ⨾ sb^? ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence).
case_refl _; [type_solver|vauto].
arewrite (fence ⊆ hbt^?) by (unfold TSO.hb; basic_solver 12).
rels.
red; rels; eapply CON.
Qed.


(******************************************************************************)
(** * Final corollary   *)
(******************************************************************************)

Lemma IMM_consistent : imm_consistent G.
Proof.
cdes CON.
red; splits; eauto.
apply Coherence.
apply C_EXT.
Qed.

End immToTSO.



