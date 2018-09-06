(******************************************************************************)
(** * Definitions and properties of derived realtions for the simulation  *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
From promising Require Import Event.
Require Import Events Execution Execution_eco.
Require Import AuxRel.
Require Import imm_s_hb imm_s imm_common.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Relations.

Variable G : execution.
Variable sc : relation actid.

Notation "'E'" := G.(acts_set).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'sb'" := G.(sb).
Notation "'eco'" := G.(eco).
Notation "'fr'" := G.(fr).

Notation "'hb'" := G.(hb).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).

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

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Implicit Type WF : Wf G.
Implicit Type WF_SC : wf_sc G sc.
Implicit Type IMMCON : imm_consistent G sc.
Implicit Type CSC : coh_sc G sc.
Implicit Type COMP : complete G.
Implicit Type COH : coherence G.
Implicit Type ACYC_EXT : acyc_ext G sc.
Implicit Type AT : rmw_atomicity G.


(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition urr l := ⦗ W_ l ⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗ F∩₁Sc ⦘)^? ⨾ sc^? ⨾  hb^?.

Definition msg_rel l := urr l ⨾ release.

Definition c_rel i l l' codom := urr l ⨾  ⦗ Rel ⦘ ⨾  ⦗ W_ l' ∪₁ F⦘ ⨾  ⦗ Tid_ i ∪₁ Init ⦘ ⨾   ⦗ codom ⦘.
Definition c_cur i l    codom := urr l ⨾ ⦗ Tid_ i ∪₁ Init ⦘ ⨾ ⦗ codom ⦘.
Definition c_acq i l    codom := urr l ⨾ (release ⨾ rf )^? ⨾ ⦗ Tid_ i ∪₁ Init ⦘ ⨾ ⦗ codom ⦘.

Definition S_tmr l codom := ⦗ W_ l ⦘ ⨾  rf^? ⨾ hb ⨾  ⦗ F∩₁Sc ⦘ ⨾ ⦗ codom ⦘.

Definition t_rel i l l' codom := dom_rel (c_rel i l l' codom).
Definition t_cur i l    codom := dom_rel (c_cur i l codom).
Definition t_acq i l    codom := dom_rel (c_acq i l codom).
Definition S_tm l       codom := dom_rel (S_tmr l codom).

(*
Definition urr' := rf^? ⨾ (hb ⨾ ⦗ F∩₁Sc ⦘)^? ⨾ psc^? ⨾  hb^?.
Definition t_rel' i l l' codom :=  W_ l ∩₁  dom_rel (urr' ⨾  ⦗ Rel ⦘ ⨾  ⦗ W_ l' ∪₁ F⦘ ⨾  ⦗ Tid_ i ∪₁ Init ⦘ ⨾   ⦗ codom ⦘).
Definition t_cur' i l codom := W_ l ∩₁  dom_rel (urr' ⨾⦗ Tid_ i ∪₁ Init ⦘ ⨾ ⦗ codom ⦘).
Definition t_acq' i l codom :=  W_ l ∩₁  dom_rel (urr' ⨾(release ⨾ rf )^? ⨾ ⦗ Tid_ i ∪₁ Init ⦘ ⨾ ⦗ codom ⦘).
Definition S_tm' l codom := W_ l ∩₁ dom_rel (rf^? ⨾ hb ⨾  ⦗ F∩₁Sc ⦘ ⨾ ⦗ codom ⦘).
*)

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_urrD l: urr l ≡ ⦗W_ l⦘ ⨾ urr l.
Proof.
split; [|basic_solver].
unfold urr; rels.
Qed.

Lemma wf_c_relD i l l' codom: c_rel i l l' codom ≡ 
  ⦗W_ l⦘ ⨾ c_rel i l l' codom ⨾  ⦗ Rel ∩₁ (W_ l' ∪₁ F) ∩₁(Tid_ i ∪₁ Init) ∩₁ codom ⦘.
Proof.
split; [|basic_solver].
unfold c_rel.
rewrite wf_urrD.
basic_solver 21.
Qed.

Lemma wf_c_curD i l codom: c_cur i l codom ≡ 
  ⦗W_ l⦘ ⨾ c_cur i l codom ⨾   ⦗ (Tid_ i ∪₁ Init) ∩₁ codom ⦘.
Proof.
split; [|basic_solver].
unfold c_cur.
rewrite wf_urrD.
basic_solver 21.
Qed.

Lemma wf_c_acqD i l codom: c_acq i l codom ≡ 
  ⦗W_ l⦘ ⨾ c_acq i l codom ⨾  ⦗ (Tid_ i ∪₁ Init) ∩₁ codom ⦘.
Proof.
split; [|basic_solver].
unfold c_acq.
rewrite wf_urrD.
basic_solver 21.
Qed.

Lemma wf_S_tmrD l codom: S_tmr l codom ≡ 
  ⦗W_ l⦘ ⨾ S_tmr l codom ⨾ ⦗ F ∩₁ Sc ∩₁ codom ⦘.
Proof.
split; [|basic_solver].
unfold S_tmr.
basic_solver 21.
Qed.

Lemma wf_t_relD i l l' codom : t_rel i l l' codom ⊆₁ W_ l.
Proof.
unfold t_rel.
rewrite (wf_c_relD i l l' codom).
basic_solver 21.
Qed.

Lemma wf_t_curD i l codom : t_cur i l codom ⊆₁ W_ l.
Proof.
unfold t_cur.
rewrite (wf_c_curD i l codom).
basic_solver 21.
Qed.

Lemma wf_t_acqD i l codom : t_acq i l codom ⊆₁ W_ l.
Proof.
unfold t_acq.
rewrite (wf_c_acqD i l codom).
basic_solver 21.
Qed.

Lemma t_rel_urr_doma l' l a i C (T : t_rel i l l' C a) : W_ l a.
Proof.
apply (@wf_t_relD i l l' C) in T.
revert T; basic_solver 21.
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma urr_codom_n_init l WF WF_SC: urr l ⨾ ⦗ Init ⦘ ⊆ ⦗ Init ⦘.
Proof.
unfold urr.
rewrite (no_hb_to_init WF), (no_sc_to_init WF WF_SC), (no_rf_to_init WF).
unfolder; ins; desf; eauto.
Qed.


(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma urr_refl l : ⦗ W_ l ⦘ ⊆ urr l.
Proof. unfold urr; basic_solver 21. Qed.

Lemma urr_hb l : urr l ⨾ hb^? ⊆ urr l.
Proof. unfold urr; generalize (@hb_trans G); basic_solver 21. Qed.

Lemma urr_hb' l : urr l ⨾ hb ⊆ urr l.
Proof. unfold urr; generalize (@hb_trans G); basic_solver 21. Qed.

Lemma hb_in_urr l : ⦗ W_ l ⦘ ⨾ hb^? ⊆ urr l.
Proof.
unfold urr; basic_solver 42.
Qed.

Lemma urr_f_sc WF WF_SC ACYC_EXT l : urr l ⨾ ⦗ F∩₁Sc ⦘ ⊆ ⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^?.
Proof.
unfold urr; rewrite !seqA.
do 2 hahn_frame_l.
rewrite (crE sc) at 1; relsf; unionL.
by generalize (@hb_trans G); basic_solver 21. 
rewrite (crE hb); relsf; unionL; [basic_solver 12|].
rewrite (dom_r (wf_scD WF_SC)), !seqA.
rewrite (f_sc_hb_f_sc_in_sc WF WF_SC ACYC_EXT).
generalize (sc_trans WF_SC).
rewrite (dom_r (wf_scD WF_SC)) at 3.
basic_solver 21.
Qed.

Lemma urr_f_non_sc WF WF_SC l : urr l ⨾ ⦗ F∩₁set_compl Sc ⦘ ⊆ urr l ⨾ (release ⨾ rf)^? ⨾ sb.
Proof.
unfold urr; rewrite !seqA.
- case_refl hb.
  * rewrite (dom_r (wf_scD WF_SC)).
    rewrite (dom_r (wf_rfD WF)).
    type_solver 16.
  * do 4 (hahn_frame_l).
    unfold imm_s_hb.hb.
    rewrite ct_end at 1; relsf; unionL.
    basic_solver 16.
    unfold imm_s_hb.sw at 2.
rewrite !seqA.
hahn_frame_l.
    rewrite (dom_r (wf_rfD WF)) at 1.
    type_solver 36.
Qed.

Lemma urr_f_non_acq WF WF_SC l : urr l ⨾ ⦗ F∩₁set_compl Acq ⦘ ⊆ urr l ⨾ sb.
Proof.
unfold urr; rewrite !seqA.
- case_refl hb.
  * rewrite (dom_r (wf_scD WF_SC)).
    rewrite (dom_r (wf_rfD WF)).
    mode_solver 16.
  * do 4 (hahn_frame_l).
    unfold imm_s_hb.hb.
    rewrite ct_end at 1; relsf; unionL.
    basic_solver 16.
    rewrite (dom_r (wf_swD WF)).
    type_solver.
Qed.

Lemma urr_w WF WF_SC l : urr l ⨾ ⦗ W ⦘ ≡ urr l ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ l⦘.
Proof.
unfold urr; rewrite !seqA.
split.
- case_refl hb.
  * unionR right.
    rewrite (dom_r (wf_scD WF_SC)).
    rewrite (dom_r (wf_rfD WF)).
    type_solver.
  * unionR left.
    do 4 (hahn_frame_l).
    unfold imm_s_hb.hb.
    rewrite ct_end at 1; relsf; unionL.
    basic_solver.
    rewrite (dom_r (wf_swD WF)).
    type_solver.
- rewrite sb_in_hb.
  generalize (@hb_trans G); ins; relsf.
  basic_solver 21.
Qed.

Lemma urr_non_f WF WF_SC l : urr l ⨾ ⦗ set_compl F ⦘ ⊆ urr l ⨾ sb ∪ ⦗W_ l⦘ ⨾ rf^? ∪ msg_rel l ⨾ rf ⨾ ⦗ Acq ⦘.
Proof.
unfold urr; rewrite !seqA.
case_refl hb.
- arewrite (sc^? ⨾ ⦗set_compl F⦘ ⊆ ⦗set_compl F⦘).
by rewrite (dom_r (wf_scD WF_SC)); basic_solver.
arewrite ((hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ ⦗set_compl F⦘ ⊆ ⦗set_compl F⦘).
by basic_solver.
basic_solver 12.
- unfold imm_s_hb.hb.
rewrite ct_end at 2; relsf.
unionL.
basic_solver 21.
unfold imm_s_hb.sw at 3; rewrite !seqA.
arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗set_compl F⦘ ⊆ ⦗Acq⦘).
basic_solver.
unfold msg_rel, urr.
basic_solver 21.
Qed.

Lemma msg_rel_urr WF l : msg_rel l ⨾ rf ⨾ ⦗ Acq ⦘ ⊆ urr l.
Proof.
unfold msg_rel.
rewrite seqA, (release_rf_in_sw WF), sw_in_hb.
arewrite (hb ⊆ hb^?); apply urr_hb.
Qed.

(******************************************************************************)
(** ** simple inclusion properties *)
(******************************************************************************)

Lemma t_cur_in_t_acq i l codom:
  t_cur i l codom ⊆₁ t_acq i l codom.
Proof.
unfold t_cur, t_acq, c_cur, c_acq.
basic_solver 21.
Qed.

Lemma t_rel_in_t_cur i l l' codom:
  t_rel i l l' codom ⊆₁ t_cur i l codom.
Proof.
unfold t_rel, t_cur, c_rel, c_cur.
basic_solver 21.
Qed.

Lemma t_rel_in_t_acq i l l' codom:
  t_rel i l l' codom ⊆₁ t_acq i l codom.
Proof.
unfold t_rel, t_acq, c_rel, c_acq.
basic_solver 21.
Qed.

(******************************************************************************)
(** ** more *)
(******************************************************************************)

Lemma eco_urr_irr l WF WF_SC CSC COH: irreflexive (eco ⨾ urr l).
Proof.
unfold urr.
arewrite_id ⦗W_ l⦘.
arewrite_id ⦗F ∩₁ Sc⦘.
rels.
arewrite (rf^? ⊆ eco^?).
generalize (eco_trans WF); ins; relsf.
rewrite (crE sc).
relsf; repeat (splits; try apply irreflexive_union).
- 
generalize (@hb_trans G); ins; relsf.
rewrite (crE hb); relsf; apply irreflexive_union; splits.
by apply (eco_irr WF).
red in COH; revert COH; basic_solver 20.
- 
rewrite (wf_scD WF_SC).
rotate 3.
rewrite crE at 1; relsf; repeat (splits; try apply irreflexive_union);
 [rewrite (dom_l (wf_ecoD WF)); type_solver|].
rewrite crE at 1; relsf; repeat (splits; try apply irreflexive_union);
 [rewrite (dom_r (wf_ecoD WF)); type_solver|].
revert CSC; unfold coh_sc; basic_solver 21.
Qed.

Lemma transp_rf_co_urr_irr l WF WF_SC CSC COH: irreflexive (rf^{-1} ^? ⨾ co ⨾ urr l).
Proof.
arewrite ((rf⁻¹)^? ⨾ co ⊆ eco).
by unfold Execution_eco.eco, Execution.fr; basic_solver 21.
eby apply eco_urr_irr.
Qed.

Lemma release_co_urr_irr l WF WF_SC COMP CSC COH: irreflexive (release ⨾ co ⨾ urr l).
Proof.
rewrite release_in_hb_co; auto.
2: by apply coherence_sc_per_loc, COH.
rewrite seqA.
arewrite (co^? ⨾ co ⊆ co) by generalize (co_trans WF); basic_solver.
rotate 1.
sin_rewrite urr_hb.
arewrite (co ⊆ eco).
by unfold Execution_eco.eco, Execution.fr; basic_solver 21.
by rotate 1; apply eco_urr_irr.
Qed.

Lemma sb_transp_rf_co_urr_irr l WF WF_SC CSC COH: irreflexive (sb ⨾ rf^{-1} ^? ⨾ co ⨾ urr l).
Proof.
rotate 1.
rewrite sb_in_hb.
arewrite (hb ⊆ hb^?).
sin_rewrite urr_hb.
by rotate 2; apply transp_rf_co_urr_irr.
Qed.

Lemma urr_hb_irr l WF WF_SC CSC COH ACYC_EXT: irreflexive (urr l ⨾ hb).
Proof.

unfold urr.
arewrite_id ⦗W_ l⦘.
arewrite_id ⦗F ∩₁ Sc⦘.
rels.

arewrite (rf^? ⊆ eco^?).
generalize (eco_trans WF); ins; relsf.
rewrite (crE sc).

generalize (@hb_trans G); ins; relsf.

relsf; repeat (splits; try apply irreflexive_union).
-
by rotate 1; apply COH.
- 
rewrite crE at 1; relsf; repeat (splits; try apply irreflexive_union).
* rotate 1; relsf.
rewrite (wf_scD WF_SC).
rotate 1.
sin_rewrite (f_sc_hb_f_sc_in_sc WF WF_SC ACYC_EXT).
destruct WF_SC; relsf.
* 
rewrite (wf_scD WF_SC), !seqA.
rewrite crE; relsf; apply irreflexive_union; splits;
 [rewrite (dom_r (wf_ecoD WF)); type_solver|].
revert CSC; unfold coh_sc; basic_solver 21.
Qed.

(******************************************************************************)
(** ** simple union decompositions *)
(******************************************************************************)

Lemma c_cur_union thread l A B:
  c_cur thread l (A ∪₁ B) ≡ c_cur thread l A ∪ c_cur thread l B.
Proof. unfold c_cur; basic_solver 21. Qed.

Lemma t_cur_union thread l A B:
  t_cur thread l (A ∪₁ B) ≡₁ t_cur thread l A ∪₁ t_cur thread l B.
Proof. unfold t_cur; rewrite c_cur_union; basic_solver 21. Qed.

Lemma c_acq_union thread l A B:
  c_acq thread l (A ∪₁ B) ≡ c_acq thread l A ∪ c_acq thread l B.
Proof. unfold c_acq; basic_solver 21. Qed.

Lemma t_acq_union thread l A B:
  t_acq thread l (A ∪₁ B) ≡₁ t_acq thread l A ∪₁ t_acq thread l B.
Proof. unfold t_acq; rewrite c_acq_union; basic_solver 21. Qed.

Lemma c_rel_union thread l l' A B:
  c_rel thread l l' (A ∪₁ B) ≡ c_rel thread l l' A ∪ c_rel thread l l' B.
Proof. unfold c_rel; basic_solver 21. Qed.

Lemma t_rel_union thread l l' A B:
  t_rel thread l l' (A ∪₁ B) ≡₁ t_rel thread l l' A ∪₁ t_rel thread l l' B.
Proof. unfold t_rel; rewrite c_rel_union; basic_solver 21. Qed.

Lemma s_tmr_union l A B:
  S_tmr l (A ∪₁ B) ≡ S_tmr l A ∪ S_tmr l B.
Proof. unfold S_tmr; basic_solver 21. Qed.

Lemma s_tm_union l A B:
  S_tm l (A ∪₁ B) ≡₁ S_tm l A ∪₁ S_tm l B.
Proof. unfold S_tm; rewrite s_tmr_union; basic_solver. Qed.

(******************************************************************************)
(** ** in graph *)
(******************************************************************************)

Lemma wf_urrE WF WF_SC l: urr l ≡ ⦗ W_ l ⦘ ∪ ⦗ E ⦘ ⨾ urr l ⨾ ⦗ E ⦘.
Proof.
split.
- unfold urr.
rewrite (wf_rfE WF) at 1.
rewrite (wf_hbE WF) at 1 2.
rewrite (wf_scE WF_SC) at 1.
basic_solver 21.
- unionL; [|basic_solver].
unfold urr; basic_solver 12.
Qed.

Lemma wf_c_curE WF WF_SC i l codom (IN: codom ⊆₁ E): 
  c_cur i l codom ≡ ⦗ E ⦘ ⨾ c_cur i l codom ⨾ ⦗ E ⦘.
Proof.
split; [|basic_solver].
unfold c_cur.
rewrite (wf_urrE WF WF_SC l).
generalize IN.
basic_solver 21.
Qed.

Lemma wf_t_curE WF WF_SC i l codom (IN: codom ⊆₁ E): 
  t_cur i l codom ⊆₁ E.
Proof.
unfold t_cur.
rewrite (wf_c_curE WF WF_SC i l IN).
basic_solver 21.
Qed.

(******************************************************************************)
(** ** more *)
(******************************************************************************)

Lemma t_cur_other_thread
      C C' thread l
      (CINIT  : Init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a) :
      t_cur thread l C' ≡₁ t_cur thread l C.
Proof.
  unfold t_cur, c_cur. rewrite <- !id_inter.
  rewrite !set_inter_union_l.
  arewrite (Init ∩₁ C ≡₁ Init ∩₁ C').
  { split; [basic_solver|].
    rewrite CE. generalize CINIT. basic_solver. }
  basic_solver 21.
Qed.

Lemma t_acq_other_thread
      C C' thread l
      (CINIT : Init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a) :
      t_acq thread l C' ≡₁ t_acq thread l C.
Proof.
  unfold t_acq, c_acq. rewrite <- !id_inter.
  rewrite !set_inter_union_l.
  arewrite (Init ∩₁ C ≡₁ Init ∩₁ C').
  { split; [basic_solver|].
    rewrite CE. generalize CINIT. basic_solver. }
  basic_solver 21.
Qed.

Lemma t_rel_other_thread
      C C' thread l l'
      (CINIT : Init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a) :
      t_rel thread l l' C ≡₁ t_rel thread l l' C'.
Proof.
  unfold t_rel, c_rel. rewrite <- !id_inter.
  rewrite !set_inter_union_l.
  arewrite (Init ∩₁ C ≡₁ Init ∩₁ C').
  { split; [basic_solver|].
    rewrite CE. generalize CINIT. basic_solver. }
  basic_solver 21.
Qed.

Lemma s_tmr_helper l codom WF: 
  S_tmr l codom ≡ ⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ hb^? ⨾ (release ⨾ rf)^? ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗codom⦘.
Proof.
unfold S_tmr.
split.
- unfold imm_s_hb.hb.
  rewrite ct_end at 1; relsf.
  unionL; [basic_solver 21|].
  unfold imm_s_hb.sw at 2; rewrite !seqA.
  arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗F ∩₁ Sc⦘) at 1.
    by basic_solver.
  arewrite (rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗F ∩₁ Sc⦘ ⊆ rf ⨾ sb).
    by rewrite (dom_r (wf_rfD WF)) at 1; type_solver 22.
  basic_solver 42.
- arewrite_id ⦗F ∩₁ Sc⦘ at 1.
  generalize (@hb_trans G); ins; relsf.
  case_refl (release ⨾ rf).
  * rewrite (sb_in_hb); relsf.
  * arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗F ∩₁ Sc⦘) at 1.
      by basic_solver.
    arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Acq⦘) at 1 by mode_solver.
    arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
      by unfold imm_s_hb.sw; basic_solver 12.
    rewrite (sw_in_hb); relsf.
Qed.

(******************************************************************************)
(** ** furr *)
(******************************************************************************)

Definition furr := fun x y => exists l, urr l x y.

Lemma wf_furrE WF WF_SC: furr ≡ ⦗ W ⦘ ∪ ⦗ E ⦘ ⨾ furr ⨾ ⦗ E ⦘.
Proof.
unfold furr; unfolder; ins; desf.
split; ins; desf; eauto.
apply (wf_urrE WF WF_SC) in H.
unfolder in H; desf; splits; eauto.
forward (apply is_w_loc); ins; desf; eauto.
unfold urr; basic_solver 21.
Qed.

Lemma eco_furr_irr WF WF_SC CSC COH : irreflexive (eco ⨾ furr).
Proof.
unfold furr.
unfolder; ins; desf.
eapply eco_urr_irr; basic_solver.
Qed.

Lemma urr_alt l WF_SC : urr l ≡ ⦗W_ l⦘ ;; rf^? ⨾ hb^? ⨾ sc^? ⨾ hb^?.
Proof.
unfold urr.
split.
arewrite_id ⦗F ∩₁ Sc⦘; rels.
case_refl sc.
generalize (@hb_trans G); basic_solver 21.
rewrite (dom_l (wf_scD WF_SC)); basic_solver 21.
Qed.

Lemma furr_alt WF_SC : furr ≡ ⦗W⦘ ;; rf^? ⨾ hb^? ⨾ sc^? ⨾ hb^?.
Proof.
unfold furr; split; red; ins; desf.
apply (urr_alt l WF_SC) in H; unfolder in *; basic_solver 21.
unfolder in H; desc.
forward (apply is_w_loc); try edone.
ins; desc.
exists l.
apply (urr_alt l WF_SC).
basic_solver 21.
Qed.

(* Lemma furr_hb : furr ⨾ hb^? ⊆ furr. *)
(* Proof. rewrite furr_alt; generalize (@hb_trans G); basic_solver 21. Qed. *)

Lemma urr_hb_sc_hb l  WF WF_SC ACYC_EXT : urr l ⨾ hb ⨾ sc^? ⨾ hb^? ⊆ urr l.
Proof.
rewrite (urr_alt l WF_SC), !seqA.
case_refl sc.
generalize (@hb_trans G); basic_solver 21.
case_refl (sc).
generalize (@hb_trans G); basic_solver 21.
rewrite (dom_l (wf_scD WF_SC)) at 2.
arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ hb^? ⨾ sc ⨾ hb^? ⨾ hb ⊆ urr l).
rewrite (urr_alt l WF_SC).
generalize (@hb_trans G); basic_solver 21.
sin_rewrite (urr_f_sc WF WF_SC ACYC_EXT).
rewrite !seqA.
generalize (sc_trans WF_SC); ins; relsf.
basic_solver 21.
Qed.

Lemma furr_hb_sc_hb  WF WF_SC ACYC_EXT : furr ⨾ hb ⨾ sc^? ⨾ hb^? ⊆ furr.
Proof.
unfold furr; red; ins; desf.
unfolder in *; desc.
exists l.
apply (urr_hb_sc_hb WF WF_SC ACYC_EXT).
basic_solver 21.
Qed.

Lemma urr_hb_sc_hb_irr WF WF_SC CSC COH ACYC_EXT l: 
  irreflexive (urr l ;; hb ;; (sc ;; hb)^?).
Proof.
case_refl _.
apply (urr_hb_irr WF WF_SC CSC COH ACYC_EXT).
arewrite (urr l ⨾ hb ⨾ sc ⊆ urr l).
generalize (@urr_hb_sc_hb l WF WF_SC ACYC_EXT); basic_solver 21.
apply (urr_hb_irr WF WF_SC CSC COH ACYC_EXT).
Qed.

Lemma furr_hb_sc_hb_irr WF WF_SC CSC COH ACYC_EXT : 
  irreflexive (furr ;; hb ;; (sc ;; hb)^?).
Proof.
unfold furr; unfolder; ins; desc.
eapply urr_hb_sc_hb_irr; eauto.
basic_solver 21.
Qed.

End Relations.

Require Import Setoid.

Add Parametric Morphism G: (@urr G) with signature
  same_relation ==> eq ==> same_relation as t_urr_more.
Proof.
ins; unfold urr; rewrite H; done.
Qed.

Add Parametric Morphism G: (@t_rel G) with signature
  same_relation ==> eq ==> eq ==> eq ==> set_equiv ==> set_equiv as t_rel_more.
Proof.
ins; unfold t_rel, c_rel; ins; rewrite H0, H at 1; done.
Qed.

Add Parametric Morphism G: (@t_cur G) with signature
  same_relation ==> eq ==> eq ==> set_equiv ==> set_equiv as t_cur_more.
Proof.
by unfold t_cur, c_cur; ins; rewrite H0, H at 1; done.
Qed.

Add Parametric Morphism G: (@t_acq G) with signature
  same_relation ==> eq ==> eq ==> set_equiv ==> set_equiv as t_acq_more.
Proof.
by unfold t_acq, c_acq; ins; rewrite H0, H at 1; done.
Qed.

Add Parametric Morphism G: (@S_tm G) with signature
  eq ==> set_equiv ==> set_equiv as S_tm_more.
Proof.
by unfold S_tm, S_tmr; ins; rewrite H at 1.
Qed.

Add Parametric Morphism G: (@urr G) with signature
  inclusion ==> eq ==> inclusion as t_urr_mori.
Proof.
ins; unfold urr; rewrite H; done.
Qed.

Add Parametric Morphism G: (@t_rel G) with signature
  inclusion ==> eq ==> eq ==> eq ==> set_subset ==> set_subset as t_rel_mori.
Proof.
by unfold t_rel, c_rel; ins; rewrite H0, H at 1.
Qed.

Add Parametric Morphism G: (@t_cur G) with signature
  inclusion ==> eq ==> eq ==> set_subset ==> set_subset as t_cur_mori.
Proof.
by unfold t_cur, c_cur; ins; rewrite H0, H at 1.
Qed.

Add Parametric Morphism G: (@t_acq G) with signature
  inclusion ==> eq ==> eq ==> set_subset ==> set_subset as t_acq_mori.
Proof.
by unfold t_acq, c_acq; ins; rewrite H0, H at 1.
Qed.

Add Parametric Morphism G: (@S_tm G) with signature
  eq ==> set_subset ==> set_subset as S_tm_mori.
Proof.
by unfold S_tm, S_tmr; ins; rewrite H at 1.
Qed.