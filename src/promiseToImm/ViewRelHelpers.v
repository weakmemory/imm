From hahn Require Import Hahn.
From PromisingLib Require Import Basic DenseOrder Loc.

Require Import Events.
Require Import Execution.
Require Import imm_s.
Require Import imm_s_hb.
Require Import imm_bob imm_s_ppo.
Require Import CombRelations.
Require Import CombRelationsMore.
Require Import TraversalConfig.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ViewRelHelpers.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'release'" := G.(release).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'W_ex'" := G.(W_ex).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Lemma next_helper C a 
  (IC : is_init ∩₁ E ⊆₁ C)
  (CE : C ⊆₁ E)
  (CC : C ⊆₁ dom_cond sb C)
  (NEXT: next G C a) :
  ⦗Tid_ (tid a) ∪₁ Init⦘ ⨾ ⦗C⦘ ≡ ⦗dom_rel (sb ⨾ ⦗eq a⦘)⦘.
Proof using WF.
split.
- unfolder; ins; desc; splits; eauto; eexists; splits; eauto; subst.
  assert (~ is_init a) as NA.
  { intros H; apply NEXT, IC. split; auto.
    apply NEXT. }
  assert (E y) as EY.
    by apply CE.
  assert (E a) as EA.
    by apply NEXT.
  desf; [|by apply init_ninit_sb].
  symmetry in H0.
  eapply same_thread in H0; eauto.
  desf. exfalso. red in H0; desf; [by apply NEXT in H1|].
  apply NEXT.
  apply CC in H1.
  apply H1; basic_solver 8.
- rewrite sb_tid_init'.
  unfold same_tid; unfolder; ins; desf; splits; eauto.
  apply NEXT; basic_solver 10.
apply IC. split; auto.
apply (dom_l (@wf_sbE G)) in H2.
apply seq_eqv_l in H2. desf.
Qed.

Lemma next_helper' a 
(T : trav_config)
(TCCOH : tc_coherent G sc T)
  (NEXT: next G (covered T) a) :
  ⦗Tid_ (tid a) ∪₁ Init⦘ ⨾ ⦗covered T⦘ ≡ ⦗dom_rel (sb ⨾ ⦗eq a⦘)⦘.
Proof using WF.
apply next_helper; auto.
apply TCCOH.
all: intros x H; apply TCCOH in H; apply H.
Qed.

Lemma s_tm_cov_sc_fence T
      f ordf thread
      (TID: tid f = thread)
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (NEXT : next G (covered T) f)
      (FPARAMS : lab f = Afence ordf)
      (SC : Sc f) :
  forall l,
    S_tm G l (covered T ∪₁ eq f) ≡₁
    S_tm G l (covered T) ∪₁ t_acq G sc thread l (covered T).
Proof using WF.
  cdes IMMCON.
  intro l; split.
  - unfold S_tm, t_acq.
    rewrite s_tmr_union; relsf; unionL; splits; [basic_solver|].
    unionR right.
    rewrite (s_tmr_helper _ _ WF).
    unfold c_acq, urr.
    arewrite (sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗eq f⦘ ⊆ ⦗covered T⦘ ⨾ sb ⨾ ⦗eq f⦘).
      by revert NEXT; unfold next, dom_cond; basic_solver 21.
    arewrite (⦗covered T⦘ ⨾ sb ⨾ ⦗eq f⦘ ⊆ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗covered T⦘ ⨾ sb^?).
      by unfolder; ins; desf; splits; eauto using sb_tid_init.
    basic_solver 42.
  - unionL; [by unfold S_tm; rewrite s_tmr_union; basic_solver|].
  unfold t_acq, S_tm.
  rewrite s_tmr_union.
  relsf.
  unfold c_acq, urr.
  rewrite (crE sc); relsf; unionL; splits.
  { unionR right.
    rewrite (s_tmr_helper _ _ WF).
    arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗covered T⦘ ⊆ ⦗dom_rel(sb ⨾ ⦗eq f⦘)⦘).
    by rewrite <- TID; rewrite next_helper'; basic_solver.
    arewrite (⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗eq f⦘) at 1 by type_solver.
    basic_solver 42. }
  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗covered T⦘ ⊆ ⦗covered T⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘).
  basic_solver.

  arewrite ((release ⨾ rf)^? ⨾ ⦗covered T⦘ ⊆ ⦗covered T⦘ ⨾ (release ⨾ rf)^?).
  { by case_refl _;
      [basic_solver| rewrite !seqA; rewrite release_rf_covered; auto; basic_solver]. }
  arewrite (hb^? ⨾ ⦗covered T⦘ ⊆ ⦗covered T⦘ ⨾ hb^?).
  { by case_refl _; [basic_solver| rewrite hb_covered; auto; basic_solver]. }
  arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc ⊆ ⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sc).
  rewrite (dom_l (@wf_scD G sc Wf_sc)) at 1; rewrite (dom_r (wf_rfD WF)) at 1; hahn_frame_r; type_solver 42.
  sin_rewrite sc_covered; eauto.
  unfold S_tmr; basic_solver 21.
Qed.

Lemma msg_rel_alt T (TCCOH : tc_coherent G sc T)
      (Wf_sc : wf_sc G sc)
      w (WW : W w) (NCOV : ~ covered T w) (ISS : issuable G sc T w)
      locw (LOC : loc lab w = Some locw) l:
  dom_rel (msg_rel G sc l ⨾ ⦗ eq w ⦘) ≡₁
  (if is_rel lab w
   then t_cur G sc (tid w) l (covered T ∪₁ eq w)
   else t_rel G sc (tid w) l locw (covered T)) ∪₁
  dom_rel (msg_rel G sc l ⨾ (rf ⨾ rmw) ⨾ ⦗ eq w ⦘).
Proof using WF.
  assert (E w) as EW.
  { apply ISS. }
  assert (~ is_init w) as WNIT.
  { by intros H; apply NCOV; apply TCCOH; split. }

  assert (Rel w -> dom_rel (sb ⨾ ⦗eq w⦘) ≡₁ (Tid_ (tid w) ∪₁ Init) ∩₁ covered T) as TT.
  { intros REL. split.
    { intros x [y H]. apply seq_eqv_r in H; desf.
      split.
      { by destruct (sb_tid_init H); [left|right]. }
      apply ISS. eexists. apply seq_eqv_r; split; eauto.
      red. repeat left.
      apply seq_eqv_r; split; [|split]; auto. }
    intros x [TIDIN COV]. exists w.
    apply seq_eqv_r; split; auto.
    assert (E x) as EX.
    { cdes TCCOH. apply CC. apply COV. }
    destruct TIDIN as [TID|INIT].
    2: by eapply init_ninit_sb; eauto.
    edestruct same_thread as [H|H].
    3: by apply WNIT.
    { apply ISS. }
    { apply EX. }
    1,3: done.
    exfalso.
    destruct H as [|H]; [by desf|].
    apply TCCOH in COV.
    apply NCOV. apply COV.
    eexists. apply seq_eqv_r; eauto. }
  assert (Rel w -> dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ covered T) as TT'.
  { intros H. rewrite (TT H). basic_solver. }

  assert (~ Rel w ->
          ⦗Rel⦘ ⨾ fwbob G ⨾ ⦗eq w⦘ ⊆
          ⦗Rel⦘ ⨾ ⦗W_ locw ∪₁ F⦘ ⨾ ⦗Tid_ (tid w) ∪₁ Init⦘ ⨾ ⦗covered T⦘ ⨾ sb ⨾ ⦗eq w⦘) as QQ.
  { intros HH.
    arewrite (fwbob G ⨾ ⦗eq w⦘ ⊆ ⦗covered T⦘ ⨾ fwbob G ⨾ ⦗eq w⦘).
    { intros x y H. apply seq_eqv_l; split; [|done].
      apply ISS. eexists; eauto. }
    unfold fwbob; rewrite !seq_union_l. rewrite !seqA.
    arewrite (⦗W ∩₁ Rel⦘ ⨾ ⦗eq w⦘ ⊆ ∅₂) by basic_solver.
    arewrite (⦗F ∩₁ (fun a : actid => is_ra lab a)⦘ ⨾ ⦗eq w⦘ ⊆ ∅₂) by type_solver.
    relsf; unionL.
    - unfold same_loc; unfolder; ins; desf; splits; eauto.
      by left; splits; congruence.
      by apply (@sb_tid_init G).
    - generalize (@sb_tid_init G).
      basic_solver 21. }

  unfold msg_rel at 1.
  unfold imm_s_hb.release.
  unfold imm_s_hb.rs.
  rewrite rtE.
  rewrite !seq_union_r. rewrite seq_union_l.
  rewrite dom_union. apply set_equiv_union.
  2: { apply dom_rel_more.
       unfold msg_rel at 1. unfold imm_s_hb.release. unfold imm_s_hb.rs.
       rewrite ct_end. basic_solver. }
  rewrite seq_id_r.
  unfold t_cur, t_rel.
  split.
  { rewrite !seqA.
    arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾ ⦗eq w⦘ ⊆
              ⦗Rel⦘ ⨾ fwbob G ⨾ ⦗eq w⦘ ∪ ⦗Rel ∩₁ eq w⦘).
    { case_refl _; case_refl _.
      { basic_solver. }
      all: unfold fwbob.
      { basic_solver 42. }
      all: arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⊆ ⦗Rel⦘ ⨾ ⦗F ∩₁ (fun a => is_ra lab a)⦘) by mode_solver.
      2: arewrite (sb ⨾ ⦗W⦘ ⨾ sb ∩ same_loc lab ⊆ sb) by
          (generalize (@sb_trans G); basic_solver).
      all: basic_solver 42. }
    rewrite seq_union_r.
    desf.
    { arewrite (Rel ∩₁ eq w ≡₁ eq w); [basic_solver|].
      arewrite (urr G sc l ⨾ ⦗Rel⦘ ⨾ fwbob G ⨾ ⦗eq w⦘ ∪ urr G sc l ⨾ ⦗eq w⦘ ⊆
                urr G sc l ⨾ ⦗eq w⦘).
      { rewrite union_absorb_l; [done|].
        hahn_frame. etransitivity.
        2: by apply urr_hb.
        hahn_frame.
        rewrite fwbob_in_bob. rewrite bob_in_sb.
        rewrite sb_in_hb. basic_solver. }
      rewrite urr_w_alt_union_eqv; auto.
      apply dom_rel_mori.
      arewrite (⦗eq w⦘ ⊆ ⦗W⦘ ⨾ ⦗eq w⦘) at 1 by basic_solver.
      seq_rewrite (urr_w WF); relsf; unionL; [unionR left| basic_solver 12].
      generalize (TT' Heq); basic_solver 21. }
    arewrite (Rel ∩₁ eq w ≡₁ ∅) by basic_solver.
    rewrite <- dom_rel_ext with
        (r := c_rel G sc (tid w) l locw (covered T))
        (r' := (sb ⨾ ⦗ eq w ⦘) ).
    apply dom_rel_mori.
    unfold c_rel.
    rewrite crE. rewrite !seq_union_r. unionR right.
    rewrite !seqA; rewrite QQ; [basic_solver 12| by rewrite Heq]. }
  desf.
  { rewrite urr_w_alt_union_eqv; auto.
    relsf; unionL; splits; [|unfold urr; basic_solver 42].
    rewrite crE at 1; relsf; unionL; splits.
    - rewrite seq_eqvC; rewrite <- id_inter.
      rewrite <- (TT Heq).
      rewrite dom_rel_eqv_dom_rel.
      apply dom_rel_mori.
      rewrite !crE; relsf.
      unionR left -> left. rewrite !seqA.
      arewrite (⦗eq w⦘ ⊆ ⦗Rel⦘ ⨾ ⦗eq w⦘) at 1 by basic_solver.
      arewrite (⦗eq w⦘ ⊆ ⦗W⦘ ⨾ ⦗eq w⦘) at 1 by basic_solver.
      hahn_frame. etransitivity;[|by apply urr_hb].
      rewrite sb_in_hb. basic_solver.
    - rewrite sb_in_hb at 1.
      arewrite (hb ⊆ hb^?) at 1 .
      arewrite_id ⦗covered T⦘; rels.
      sin_rewrite (@urr_hb G sc l).
      basic_solver 21. }
  unfold c_rel.
  rewrite <- !id_inter.
  intros x [y [z [HH [H'' JJ]]]]; subst.
  exists w. apply seq_eqv_r; split; auto.
  exists y; split; auto.
  destruct JJ as [JJ1 [JJ2 [JJ3 JJ4]]].
  assert (E y) as EY.
  { apply TCCOH in JJ4. apply JJ4. }
  assert (sb y w) as SBYW.
  { destruct JJ3 as [TID|INIT].
    2: by eapply init_ninit_sb; eauto.
    edestruct same_thread as [H|H].
    3: by apply WNIT.
    { apply ISS. }
    { apply EY. }
    1,3: done.
    exfalso.
    destruct H as [|H]; [by desf|].
    apply TCCOH in JJ4.
    apply NCOV, JJ4.
    basic_solver 12. }
  apply seq_eqv_l; split; auto.
  destruct JJ2.
  { exists y; split; [by left|].
    apply seq_eqv_l; split; [apply H|].
    apply seq_eqv_r; split; auto.
    right; split; auto. red. rewrite LOC; apply H. }
  basic_solver 12.
Qed.

Lemma msg_rel_alt2 T (TCCOH : tc_coherent G sc T)
      (Wf_sc : wf_sc G sc)
      w (WW : W w) (NCOV : ~ covered T w) (ISS : issuable G sc T w)
      locw (LOC : loc lab w = Some locw) l:
  dom_rel (msg_rel G sc l ⨾ ⦗ eq w ⦘) ≡₁
  (if is_rel lab w
   then t_cur G sc (tid w) l (covered T)
   else t_rel G sc (tid w) l locw (covered T)) ∪₁
  dom_rel (msg_rel G sc l ⨾ (rf ⨾ rmw) ⨾ ⦗ eq w ⦘) ∪₁
  Rel ∩₁ Loc_ l ∩₁ eq w.
Proof using WF.
  rewrite msg_rel_alt; eauto.
  desf.
  2: by arewrite (Rel ∩₁ Loc_ l ∩₁ eq w ≡₁ ∅); basic_solver 10. 
  rewrite t_cur_urr_union_eqv_w; auto.
  { arewrite (Rel ∩₁ Loc_ l ∩₁ eq w ≡₁ Loc_ l ∩₁ eq w).
    2: by unfold t_cur, c_cur; basic_solver 10.
    basic_solver 10. }
  destruct ISS as [[_ ISS] _].
  red in ISS.
  assert (sb ⨾ ⦗eq w⦘ ⊆ fwbob G ⨾ ⦗eq w⦘) as HH.
  2: generalize ISS HH; basic_solver 10.
  unfold fwbob; basic_solver 12.
Qed.

Lemma msg_rel_rfrmw_helper T (TCCOH : tc_coherent G sc T)
      w (WW : W w) (NCOV : ~ covered T w) (ISS : issuable G sc T w)
      locw (LOC : loc lab w = Some locw) l:
  dom_rel ((urr G sc l ⨾ release) ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ⊆₁
  dom_rel (urr G sc l ⨾ ⦗Rel⦘ ⨾ ⦗W_ locw ∪₁ F⦘ ⨾ ⦗Tid_ (tid w) ∪₁ Init⦘ ⨾ ⦗covered T⦘)
  ∪₁ dom_rel ((urr G sc l ⨾ release) ⨾ (⦗W_ex⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗eq w⦘).
Proof using WF.
rewrite rfi_union_rfe; relsf; unionL; splits.
2: basic_solver 12.
unfold imm_s_hb.release.
unfold imm_s_hb.rs.
rewrite rtE; relsf.
unionL; splits; cycle 1.
rewrite rmw_W_ex at 1.
rewrite <- !seqA.
rewrite inclusion_ct_seq_eqv_r.
unionR right -> left -> right; basic_solver 21.
unionR left.
rewrite !seqA.
arewrite ((sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾ rfi ⨾ rmw ⊆ sb ∩ same_loc lab).
{ arewrite_id ⦗W⦘; rewrite (rfi_in_sbloc' WF), (rmw_in_sb_loc WF).
  generalize (@sb_same_loc_trans G); ins; relsf. }
arewrite (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ sb ∩ same_loc lab ⨾ ⦗eq w⦘
   ⊆ ⦗Rel⦘ ⨾ ⦗W_ locw ∪₁ F⦘ ⨾ ⦗Tid_ (tid w) ∪₁ Init⦘ ⨾ fwbob G ⨾ ⦗eq w⦘).
{ 
rewrite crE at 1; relsf; unionL.
- unfold fwbob.
rewrite sb_tid_init' at 1.
rewrite (init_pln WF) at 1.
unfold same_tid.
relsf.
unionR left -> left -> right.
unfolder; ins; desf; splits; eauto 20.
unfold same_loc in *; desf; eauto; left; splits; congruence.
unfold same_loc in *; desf; eauto; left; splits; congruence.
mode_solver 42.
- 
rewrite !seqA.
arewrite (sb ⨾ ⦗W⦘ ⨾ sb ∩ same_loc lab ⊆ sb).
by generalize (@sb_trans G); basic_solver.
arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗eq w⦘ ⊆ ⦗Rel⦘ ⨾ ⦗F⦘ ⨾ ⦗Tid_ (tid w)⦘ ⨾ fwbob G ⨾ ⦗eq w⦘).
{ unfold fwbob.
rewrite sb_tid_init' at 1.
rewrite (init_w WF).
unfold same_tid.
mode_solver 21. }
basic_solver.

}

arewrite (⦗eq w⦘ ⊆ ⦗dom_cond (fwbob G) (covered T)⦘).
by revert ISS; unfold issuable; basic_solver 10.
rewrite dom_cond_elim.
basic_solver 12.
Qed.

Lemma t_rel_msg_rel_rfrmw T (TCCOH : tc_coherent G sc T)
      w (WW : W w) (NCOV : ~ covered T w) (ISS : issuable G sc T w)
      locw (LOC : loc lab w = Some locw) l:
  t_rel G sc (tid w) l locw (covered T) ∪₁ dom_rel (msg_rel G sc l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
  t_rel G sc (tid w) l locw (covered T) ∪₁
  dom_rel (msg_rel G sc l ⨾ (⦗ W_ex ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗eq w⦘).
Proof using WF.
ins; split; unionL; desf.
1,3: basic_solver.
2: rewrite rfi_union_rfe; basic_solver 12.
unfold t_rel, c_rel, msg_rel.
by apply msg_rel_rfrmw_helper.
Qed.

Lemma t_cur_msg_rel_rfrmw T (TCCOH : tc_coherent G sc T)
      w (WW : W w) (NCOV : ~ covered T w) (ISS : issuable G sc T w) l:
  t_cur G sc (tid w) l (covered T) ∪₁ dom_rel (msg_rel G sc l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
  t_cur G sc (tid w) l (covered T) ∪₁
  dom_rel (msg_rel G sc l ⨾ (⦗ W_ex ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗eq w⦘).
Proof using WF.
ins; split; unionL; desf.
1,3: basic_solver.
2: rewrite rfi_union_rfe; basic_solver 12.
unfold t_cur, c_cur, msg_rel.
assert (exists locw, loc lab w = Some locw).
by unfold loc, is_w in *; destruct (lab w); eauto.
desc.
rewrite msg_rel_rfrmw_helper; try edone.
basic_solver 21.
Qed.

Lemma t_cur_n_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (Wf_sc : wf_sc G sc)
      f (FENCE : F f) (NSC : ~ Sc f) (NEXT : next G (covered T) f)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T):
  forall l,
    t_cur G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    if is_acq lab f
    then t_acq G sc (tid f) l (covered T)
    else t_cur G sc (tid f) l (covered T).
Proof using WF.
ins; split; rewrite t_cur_union; unionL; desf.
by apply t_cur_in_t_acq.
4: basic_solver.
all: unfold t_cur, t_acq, c_cur, c_acq.
- arewrite (⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘) by basic_solver.
  arewrite (⦗eq f⦘ ⊆ ⦗ F ∩₁ set_compl Sc ⦘ ⨾ ⦗eq f⦘) by basic_solver.
  sin_rewrite (urr_f_non_sc WF); auto.
  rewrite next_helper'; basic_solver 21.
- arewrite (⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘) by basic_solver.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁set_compl Acq ⦘ ⨾ ⦗eq f⦘) by basic_solver.
  sin_rewrite (urr_f_non_acq WF); auto.
  rewrite next_helper'; basic_solver 21.
- rewrite crE at 1; relsf; unionL; splits; [basic_solver 12|].
  unionR right.
  rewrite next_helper'; auto.
  rewrite <- !seqA.
  rewrite !dom_rel_eqv_dom_rel.
  rewrite !seqA.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by basic_solver.
  arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
  unfold imm_s_hb.sw; basic_solver 16.
  arewrite (sw ⊆ hb^?).
  sin_rewrite urr_hb.
  basic_solver 21.
Qed.

Lemma t_acq_n_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (Wf_sc : wf_sc G sc)
      f (FENCE : F f) (NSC : ~ Sc f) (NEXT : next G (covered T) f):
  forall l,
    t_acq G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    t_acq G sc (tid f) l (covered T).
Proof using WF.
ins; split; rewrite t_acq_union; unionL; splits; desf; [|basic_solver].
unfold t_acq, c_acq.
arewrite (⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘) by basic_solver.
rewrite next_helper'; auto.
rewrite <- !seqA.
rewrite !dom_rel_eqv_dom_rel.
rewrite !seqA.
rewrite (dom_r (wf_rfD WF)) at 1.
rewrite crE at 1; relsf; unionL; splits; [|type_solver].
arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁set_compl Sc ⦘ ⨾ ⦗eq f⦘) at 1 by basic_solver.
sin_rewrite (urr_f_non_sc WF); auto.
basic_solver 21.
Qed.

Lemma t_rel_n_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (Wf_sc : wf_sc G sc)
      f (FENCE : F f) (NSC : ~ Sc f) (NEXT : next G (covered T) f):
  forall l l',
    t_rel G sc (tid f) l l' (covered T ∪₁ eq f) ∪₁
    (if LocSet.Facts.eq_dec l l'
     then W ∩₁ Loc_ l' ∩₁ Tid_ (tid f) ∩₁ (covered T ∪₁ eq f)
     else ∅) ≡₁
    if is_acqrel lab f
    then t_acq G sc (tid f) l (covered T)
    else
      if is_rel lab f
      then t_cur G sc (tid f) l (covered T)
      else
        t_rel G sc (tid f) l l' (covered T) ∪₁
        (if LocSet.Facts.eq_dec l l'
         then W ∩₁ Loc_ l' ∩₁ Tid_ (tid f) ∩₁ (covered T)
         else ∅).
Proof using WF.
ins; split; try rewrite t_rel_union; unionL; desf.
by apply t_rel_in_t_acq.
by apply t_rel_in_t_cur.
all: try rewrite set_inter_union_r.
all: unionL.
all: try  basic_solver 8.
all: try type_solver.
5: unfold t_acq, c_acq, urr; basic_solver 42.
5: unfold t_cur, c_cur, urr; basic_solver 42.
all: try rewrite set_union_empty_r.
all: unfold t_rel, c_rel, t_acq, c_acq, t_cur, c_cur.
all: rewrite next_helper'; auto.
all: rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
- arewrite ( ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F∩₁set_compl Sc⦘ ⨾ ⦗eq f⦘).
  type_solver.
  sin_rewrite (urr_f_non_sc WF); auto.
  basic_solver 21.
- arewrite ( ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F∩₁set_compl Acq⦘ ⨾ ⦗eq f⦘).
  mode_solver.
  sin_rewrite (urr_f_non_acq WF); auto.
  basic_solver 21.
- arewrite ( ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F∩₁set_compl Acq⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗eq f⦘).
  mode_solver.
  sin_rewrite (urr_f_non_acq WF); auto.
  basic_solver 21.
- arewrite ( ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F∩₁set_compl Acq⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗eq f⦘).
  mode_solver.
  sin_rewrite (urr_f_non_acq WF); auto.
  basic_solver 21.
- arewrite ((release ⨾ rf)^? ⨾ sb ⨾ ⦗eq f⦘ ⊆ hb^? ⨾ ⦗eq f⦘) at 1.
  { rewrite crE at 1; relsf; unionL.
    arewrite (sb ⊆ hb^?) at 1; basic_solver.
    arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
    arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
    unfold imm_s_hb.sw; basic_solver 16.
    arewrite (sw ⊆ hb^?); basic_solver. }
  sin_rewrite urr_hb.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Rel ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
  basic_solver 21.
- arewrite ((release ⨾ rf)^? ⨾ sb ⨾ ⦗eq f⦘ ⊆ hb^? ⨾ ⦗eq f⦘) at 1.
  { rewrite crE at 1; relsf; unionL.
    arewrite (sb ⊆ hb^?) at 1; basic_solver.
    arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
    arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
    unfold imm_s_hb.sw; basic_solver 16.
    arewrite (sw ⊆ hb^?); basic_solver. }
  sin_rewrite urr_hb.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Rel ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
  basic_solver 21.
- arewrite (sb ⊆ hb^?) at 1.
  sin_rewrite urr_hb.
  basic_solver 21.
- arewrite (sb ⊆ hb^?) at 1.
  sin_rewrite urr_hb.
  basic_solver 21.
Qed.

Lemma sc_helper' T (TCCOH : tc_coherent G sc T) (Wf_sc : wf_sc G sc)
 f (FENCE : F f) (SC : Sc f) (COV : coverable G sc T f) (NCOV : ~ covered T f) :
 ⦗F ∩₁ Sc⦘ ⨾ ⦗covered T⦘ ≡ ⦗dom_rel (sc ⨾ ⦗eq f⦘)⦘.
Proof using.
cdes TCCOH; unfold coverable, dom_cond in *.
unfolder in *; desf; [type_solver| type_solver|].
split.
- ins; desf; splits; eauto.
  eexists; splits; eauto.
  eapply tot_ex.
  * apply Wf_sc.
  * basic_solver.
  * generalize (coveredE TCCOH); basic_solver.
  * intro; apply NCOV.
    specialize (CC y H1); desf; [type_solver|type_solver|].
    apply CC2; eauto.
  * intro; subst; eauto.
- ins; desf.
  hahn_rewrite (wf_scD Wf_sc) in H0.
  unfolder in *; desf; splits; eauto 20.
Qed.

Lemma t_cur_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      f (FENCE : F f) (SC: Sc f) 
      (COV : coverable G sc T f) (NCOV : ~ covered T f) :
  forall l,
    t_cur G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    S_tm G l (covered T) ∪₁ t_acq G sc (tid f) l (covered T).
Proof using WF.
  cdes IMMCON.
ins; split; try rewrite t_cur_union; unionL; desf.
by rewrite t_cur_in_t_acq; basic_solver.
all: unfold t_cur, c_cur, S_tm, S_tmr, t_acq, c_acq, t_rel, c_rel.
- arewrite (⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘).
  basic_solver.
  sin_rewrite (urr_f_sc WF); auto.
  rewrite !seqA.
  arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ ⦗eq f⦘ ⊆ ⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sc^? ⨾ ⦗eq f⦘).
  { rewrite (dom_r (wf_rfD WF)) at 1.
    arewrite (⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘) at 1 by basic_solver.
    rewrite (dom_l (wf_scD Wf_sc)) at 1.
    hahn_frame_r; unfolder; ins; desf; eauto 20; type_solver. }
  rewrite (crE sc); relsf.
  rewrite <- !dom_eqv1.
  unionL; splits.
  * arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗eq f⦘ ⊆ S_tmr G l (eq f)).
    rewrite (s_tmr_helper l (eq f) WF).
    rewrite next_helper'; auto.
    2: by split; [apply COV|apply NCOV].
    rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
    unfold urr.
    unionR right; basic_solver 42.
  * unfold urr.
    rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
    basic_solver 21.
- unfold urr.
  rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  rewrite (dom_l (wf_scD Wf_sc)) at 1.
  unionR right; basic_solver 21.
- rewrite crE at 1; relsf; unionL; splits; [basic_solver 12|].
  unionR right.
  rewrite next_helper'; auto.
  2: by split; [apply COV|apply NCOV].
  rewrite <- !seqA.
  rewrite !dom_rel_eqv_dom_rel.
  rewrite !seqA.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
  arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
  unfold imm_s_hb.sw; basic_solver 16.
  arewrite (sw ⊆ hb^?).
  sin_rewrite urr_hb.
  basic_solver 21.
Qed.

Lemma t_acq_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      f (FENCE : F f) (SC: Sc f) (COV : coverable G sc T f) (NCOV : ~ covered T f):
  forall l,
    t_acq G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    t_acq G sc (tid f) l (covered T) ∪₁
    S_tm G l (covered T).
Proof using WF.
  cdes IMMCON.
ins; split; try rewrite t_acq_union; unionL; desf.
1,3: basic_solver.
all: unfold t_cur, c_cur, S_tm, S_tmr, t_acq, c_acq, t_rel, c_rel.
- arewrite (⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘).
  basic_solver.
  arewrite ((release ⨾ rf)^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘).
  rewrite (dom_r (wf_rfD WF)) at 1; type_solver.
  sin_rewrite (urr_f_sc WF); auto.
  rewrite !seqA.
  arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ ⦗eq f⦘ ⊆ ⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sc^? ⨾ ⦗eq f⦘).
  { rewrite (dom_r (wf_rfD WF)) at 1.
    arewrite (⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘) at 1 by basic_solver.
    rewrite (dom_l (wf_scD Wf_sc)) at 1.
    hahn_frame_r; unfolder; ins; desf; eauto 20; type_solver. }
  rewrite (crE sc); relsf; rewrite <- !dom_eqv1; unionL; splits.
  * arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗eq f⦘ ⊆ S_tmr G l (eq f)).
    rewrite (s_tmr_helper l (eq f) WF).
    rewrite next_helper'; auto.
    2: by split; [apply COV|apply NCOV].
    rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
    unfold urr.
    unionR left; basic_solver 42.
  * unfold urr.
    rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
    basic_solver 21.
- unfold urr.
  rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  rewrite (dom_l (wf_scD Wf_sc)) at 1.
  unionR right; basic_solver 42.
Qed.

Lemma t_rel_sc_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      f (FENCE : F f) (SC: Sc f) (COV : coverable G sc T f) (NCOV : ~ covered T f) :
  forall l l',
    t_rel G sc (tid f) l l' (covered T ∪₁ eq f) ∪₁
    (if LocSet.Facts.eq_dec l l'
     then W ∩₁ Loc_ l' ∩₁ Tid_ (tid f) ∩₁ (covered T ∪₁ eq f)
     else ∅) ≡₁
     S_tm G l (covered T) ∪₁ t_acq G sc (tid f) l (covered T).
Proof using WF.
  cdes IMMCON.
ins; split; try rewrite t_rel_union; unionL; desf.
by rewrite t_rel_in_t_acq; basic_solver.
all: unfold t_cur, c_cur, S_tm, S_tmr, t_acq, c_acq, t_rel, c_rel.
2: by unfold urr; type_solver 42.
- arewrite (⦗Rel⦘ ⨾ ⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘ ⨾ ⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘ ⨾ ⦗Tid_ (tid f) ∪₁ Init⦘).
  basic_solver.
  sin_rewrite (urr_f_sc WF); auto.
  rewrite !seqA.
  arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ sc^? ⨾ ⦗eq f⦘ ⊆ ⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sc^? ⨾ ⦗eq f⦘).
  { rewrite (dom_r (wf_rfD WF)) at 1.
    arewrite (⦗eq f⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾  ⦗eq f⦘) at 1 by basic_solver.
    rewrite (dom_l (wf_scD Wf_sc)) at 1.
    hahn_frame_r; unfolder; ins; desf; eauto 20; type_solver. }
  rewrite (crE sc); relsf; rewrite <- !dom_eqv1; unionL; splits.
  * arewrite (⦗W_ l⦘ ⨾ rf^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⨾ ⦗eq f⦘ ⊆ S_tmr G l (eq f)).
    rewrite (s_tmr_helper l (eq f) WF).
    rewrite next_helper'; auto.
    2: by split; [apply COV|apply NCOV].
    rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
    unfold urr.
    unionR right; basic_solver 42.
  * unfold urr.
    rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
    basic_solver 21.
- unfold urr.
  rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  rewrite (dom_l (wf_scD Wf_sc)) at 1.
  assert (Rel f) by mode_solver.
  unionR left -> right; basic_solver 42.
- unfold urr.
  rewrite (sc_helper' TCCOH Wf_sc FENCE); auto.
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  rewrite (dom_l (wf_scD Wf_sc)) at 1.
  assert (Rel f) by mode_solver.
  unionR left -> right; basic_solver 42.
- rewrite next_helper'; auto.
  2: by split; [apply COV|apply NCOV].
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  arewrite ((release ⨾ rf)^? ⨾ sb ⨾ ⦗eq f⦘ ⊆ hb^? ⨾ ⦗eq f⦘) at 1.
  { rewrite crE at 1; relsf; unionL.
    arewrite (sb ⊆ hb^?) at 1; basic_solver.
    arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
    arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
    unfold imm_s_hb.sw; basic_solver 16.
    arewrite (sw ⊆ hb^?); basic_solver. }
  sin_rewrite urr_hb.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Rel ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
  basic_solver 21.
- rewrite next_helper'; auto.
  2: by split; [apply COV|apply NCOV].
  rewrite <- !seqA, dom_rel_eqv_dom_rel, !seqA.
  arewrite ((release ⨾ rf)^? ⨾ sb ⨾ ⦗eq f⦘ ⊆ hb^? ⨾ ⦗eq f⦘) at 1.
  { rewrite crE at 1; relsf; unionL.
    arewrite (sb ⊆ hb^?) at 1; basic_solver.
    arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Acq ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
    arewrite (release ⨾ rf ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆ sw).
    unfold imm_s_hb.sw; basic_solver 16.
    arewrite (sw ⊆ hb^?); basic_solver. }
  sin_rewrite urr_hb.
  arewrite (⦗eq f⦘ ⊆ ⦗ F∩₁ Rel ⦘ ⨾ ⦗eq f⦘) at 1 by mode_solver.
  basic_solver 21.
Qed.

Lemma t_cur_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      f (FENCE : F f) (COV : coverable G sc T f) (NCOV : ~ covered T f):
  forall l,
    t_cur G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    if is_sc lab f
    then S_tm G l (covered T) ∪₁ t_acq G sc (tid f) l (covered T)
    else
      if is_acq lab f
      then t_acq G sc (tid f) l (covered T)
      else t_cur G sc (tid f) l (covered T).
Proof using WF.
  destruct (is_sc lab f) eqn: H.
  apply t_cur_sc_fence_step; auto.
  apply t_cur_n_sc_fence_step; auto.
  by apply IMMCON.
  by ins; desf.
  by split; [apply COV|apply NCOV].
Qed.

Lemma t_acq_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      f (FENCE : F f) (COV : coverable G sc T f) (NCOV : ~ covered T f):
  forall l,
    t_acq G sc (tid f) l (covered T ∪₁ eq f) ≡₁
    t_acq G sc (tid f) l (covered T) ∪₁
    if is_sc lab f
    then S_tm G l (covered T)
    else ∅.
Proof using WF.
  destruct (is_sc lab f) eqn: H.
  apply t_acq_sc_fence_step; auto.
  ins; rewrite set_union_empty_r; apply t_acq_n_sc_fence_step; auto.
  by apply IMMCON.
  by ins; desf.
  by split; [apply COV|apply NCOV].
Qed.

Lemma t_rel_fence_step T (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      f (FENCE : F f) (COV : coverable G sc T f) (NCOV : ~ covered T f) :
  forall l l',
    t_rel G sc (tid f) l l' (covered T ∪₁ eq f) ∪₁
    (if LocSet.Facts.eq_dec l l'
     then W ∩₁ Loc_ l' ∩₁ Tid_ (tid f) ∩₁ (covered T ∪₁ eq f)
     else ∅) ≡₁
    if is_sc lab f
    then S_tm G l (covered T) ∪₁ t_acq G sc (tid f) l (covered T)
    else 
      if is_acqrel lab f
      then t_acq G sc (tid f) l (covered T)
      else
        if is_rel lab f
        then t_cur G sc (tid f) l (covered T)
        else
          (t_rel G sc (tid f) l l' (covered T) ∪₁
           (if LocSet.Facts.eq_dec l l'
            then W ∩₁ Loc_ l' ∩₁ Tid_ (tid f) ∩₁ (covered T)
            else ∅)).
Proof using WF.
  destruct (is_sc lab f) eqn: H.
  apply t_rel_sc_fence_step; auto.
  apply t_rel_n_sc_fence_step; auto.
  by apply IMMCON.
  by ins; desf.
  by split; [apply COV|apply NCOV].
Qed.

End ViewRelHelpers.
