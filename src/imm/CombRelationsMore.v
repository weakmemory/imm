Require Import Classical Peano_dec.

Require Import Setoid.

From hahn Require Import Hahn.
From promising Require Import Basic DenseOrder Event.
Require Import AuxRel.
Require Import Events Execution.
Require Import imm_s_hb imm_s imm_common.
Require Import CombRelations. 

Set Implicit Arguments.
Remove Hints plus_n_O.

Section CombRelationsMore.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable Wf_sc : wf_sc G sc.

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

Lemma urr_n_f_alt_union_eqv l A r thread
  (SB : dom_rel (sb ⨾ ⦗ eq r ⦘) ⊆₁ A)
  (NF : ~ F r)
  (TID : tid r = thread):
  c_cur G sc thread l (A ∪₁ eq r)
      ≡
  urr G sc l ⨾ ⦗A⦘ ⨾ (sb ⨾ ⦗eq r⦘)^? ⨾ ⦗ Tid_ thread ∪₁ Init ⦘ ∪
  ⦗ W_ l ⦘ ⨾ ⦗eq r⦘ ∪
  ⦗ Loc_ l ⦘ ⨾ rf ⨾ ⦗eq r⦘ ∪
  (msg_rel G sc l ∪ ⦗ Loc_ l ⦘) ⨾
    rf ⨾ ⦗ Acq ⦘ ⨾ ⦗eq r⦘.
Proof.
rewrite c_cur_union.
unfold c_cur; split.
- unionL; [basic_solver 21|].
  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq r⦘ ⊆ ⦗ set_compl F ⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq r⦘).
  by basic_solver 21.
  sin_rewrite (urr_non_f WF).
  relsf; unionL.
  * arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq r⦘ ⊆ ⦗eq r⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘) by basic_solver.
    unionR left -> left -> left.
    hahn_frame; revert SB; basic_solver.
  * basic_solver 21.
  * basic_solver 21.
  * done.
- unionL.
  * case_refl (sb ⨾ ⦗eq r⦘).
    by basic_solver 21.
    arewrite_id ⦗A⦘; rels.
    arewrite (sb ⊆ hb^?).
    sin_rewrite urr_hb; basic_solver 12.
  * by unfold urr; basic_solver 21.
  * by unfold urr; rewrite (dom_l (wf_rfD WF)) at 1; basic_solver 21.
  * relsf; unionL.
    by sin_rewrite (msg_rel_urr WF); basic_solver 12.
    unfold urr; rewrite (dom_l (wf_rfD WF)) at 1; basic_solver 21.
Qed.

Lemma urr_w_alt_union_eqv l A w thread
  (SB : dom_rel (sb ⨾ ⦗ eq w ⦘) ⊆₁ A)
  (WW : W w)
  (TID : tid w = thread):
  c_cur G sc thread l (A ∪₁ eq w)
      ≡
  urr G sc l ⨾ ⦗A⦘ ⨾ (sb ⨾ ⦗eq w⦘)^? ⨾ ⦗ Tid_ thread ∪₁ Init ⦘ ∪
  ⦗ W_ l ⦘ ⨾ ⦗eq w⦘.
Proof.
  rewrite urr_n_f_alt_union_eqv; auto.
  rewrite (dom_r (wf_rfD WF)); type_solver 21.
  type_solver 21.
Qed.

Lemma urr_acq_n_f_alt_union_eqv l A r thread
  (SB : dom_rel (sb ⨾ ⦗eq r⦘) ⊆₁ A)
  (NF : ~ F r)
  (TID : tid r = thread) :
  c_acq G sc thread l (A ∪₁ eq r)
      ≡
  (urr G sc l ⨾ ⦗A⦘ ⨾ (sb ⨾ ⦗eq r⦘)^? ⨾ ⦗ Tid_ thread ∪₁ Init ⦘ ∪
   (msg_rel G sc l ⨾ rf ⨾ ⦗ Tid_ thread ∪₁ Init ⦘ ⨾ ⦗A⦘)) ∪
  ⦗ W_ l ⦘ ⨾ ⦗eq r⦘ ∪
  ⦗ Loc_ l ⦘ ⨾ rf ⨾ ⦗eq r⦘ ∪
  (msg_rel G sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗eq r⦘.
Proof.
  unfold c_acq; rewrite crE at 1.
  rewrite seq_union_l; rewrite seq_union_r; rewrite seq_id_l.
  arewrite (urr G sc l ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗A ∪₁ eq r⦘ ≡
            c_cur G sc thread l (A ∪₁ eq r)).
  rewrite (id_union A); rewrite (unionC ⦗A⦘).
  rewrite !seq_union_r.
  arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq r⦘ ≡ ⦗eq r⦘) by basic_solver.
  rewrite urr_n_f_alt_union_eqv; eauto.
  unfold msg_rel.
  basic_solver 21.
Qed.

Lemma urr_rel_n_f_alt_union_eqv l l' A w thread
  (SB : dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ A)
  (WW : W w)
  (TID : tid w = thread):
  c_rel G sc thread l l' (A ∪₁ eq w) ≡
  c_rel G sc thread l l' A ∪ ⦗Rel⦘ ⨾ ⦗Loc_ l⦘ ⨾ ⦗Loc_ l'⦘ ⨾ ⦗eq w⦘ ∪
  urr G sc l ⨾ ⦗A⦘ ⨾ sb ⨾ ⦗Rel⦘ ⨾ ⦗Loc_ l'⦘ ⨾ ⦗eq w⦘.
Proof.
unfold c_rel.
split.
- rewrite (id_union A) at 1; relsf.
  unionL.
  * basic_solver 21.
  * arewrite (⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq w⦘ ⊆ ⦗ set_compl F ⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq w⦘).
    by type_solver 21.
    arewrite (⦗Rel⦘ ⨾ ⦗W ∩₁ Loc_ l' ∪₁ F⦘ ⨾ ⦗set_compl F⦘ ⊆ ⦗set_compl F⦘  ⨾ ⦗Rel⦘ ⨾ ⦗W ∩₁ Loc_ l' ∪₁ F⦘).
    by type_solver 21.
    sin_rewrite (urr_non_f WF).
    relsf; unionL.
    + unionR right; revert SB; type_solver 21.
    + unionR left -> right; rewrite (dom_r (wf_rfD WF)); type_solver 21.
    + rewrite (dom_r (wf_rfD WF)); type_solver 21.
    + done.
- unionL.
  * basic_solver.
  * unfold urr; basic_solver 21.
  * arewrite_id ⦗A⦘; rels.
    arewrite (sb ⊆ hb^?).
    sin_rewrite urr_hb; basic_solver.
Qed.

(*
Lemma dom_rel_sb_clos B A r thread
    (SB : dom_rel (sb ⨾ ⦗ eq r ⦘) ⊆₁ A) :
    dom_rel (B ⨾ ⦗A⦘ ⨾ (sb ⨾ ⦗eq r⦘)^? ⨾ ⦗Tid_ thread ∪₁ Init⦘) ≡₁
    dom_rel (B ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗A⦘).
Proof.
split.
rewrite (@no_sb_to_init G); generalize (@sb_tid_init G); basic_solver 20.
revert SB; basic_solver 20.
Qed.
*)

Lemma dom_rel_r l locr thread w r
  (LOC : loc lab r = Some locr)
  (RF : rf w r)
  (TID : tid r = thread) :
    (dom_rel
       (⦗Loc_ l⦘ ⨾ rf ⨾ ⦗eq r⦘) ≡₁
       if LocSet.Facts.eq_dec l locr then eq w else ∅).
Proof.
split.
- unfolder; ins; desf.
  generalize (wf_rff WF); basic_solver.
  apply n; eauto.
  generalize (((wf_rfl WF) x y) H0); unfold same_loc; ins; congruence.
- assert (loc lab w = Some locr).
  by generalize (((wf_rfl WF) w r) RF); unfold same_loc; ins; congruence.
  desf; basic_solver 21.
Qed.

Lemma t_cur_urr_union_eqv l A thread r
  (SB : dom_rel (sb ⨾ ⦗eq r⦘) ⊆₁ A)
  (NF : ~ F r)
  (TID : tid r = thread) :
  t_cur G sc thread l (A ∪₁ eq r) ≡₁
  dom_rel (urr G sc l ⨾ ⦗Tid_ thread ∪₁ Init ⦘⨾ ⦗A⦘) ∪₁
  (W_ l ∩₁ eq r ∪₁
   dom_rel (⦗Loc_ l⦘ ⨾ rf ⨾ ⦗eq r⦘) ∪₁
   dom_rel
     ((msg_rel G sc l ∪ ⦗Loc_ l⦘)
      ⨾ rf ⨾ ⦗fun a : actid => Acq a⦘ ⨾ ⦗eq r⦘)).
Proof.
  unfold t_cur.
  rewrite urr_n_f_alt_union_eqv; auto.
  rewrite (@no_sb_to_init G); generalize (@sb_tid_init G); basic_solver 20.
Qed.

Lemma t_cur_urr_union_eqv_w l A thread w
  (SB : dom_rel (sb ⨾ ⦗eq w⦘) ⊆₁ A)
  (WW : W w)
  (TID : tid w = thread) :
  t_cur G sc thread l (A ∪₁ eq w) ≡₁
  dom_rel (urr G sc l ⨾ ⦗Tid_ thread ∪₁ Init ⦘⨾ ⦗A⦘) ∪₁
  Loc_ l ∩₁ eq w.
Proof.
  rewrite t_cur_urr_union_eqv; auto.
  2: by intros H; type_solver.
  split; [|basic_solver 10].
  arewrite_id ⦗ Acq ⦘; rewrite seq_id_l.
  arewrite (rf ⨾ ⦗ eq w ⦘ ⊆ ∅₂).
  2: basic_solver 10.
  rewrite (dom_r WF.(wf_rfD)).
  type_solver.
Qed.

Lemma t_acq_urr_union_eqv l A thread r
  (SB : dom_rel (sb ⨾ ⦗ eq r ⦘) ⊆₁ A)
  (NF : ~ F r)
  (TID : tid r = thread) :
  t_acq G sc thread l (A ∪₁ eq r) ≡₁
  t_acq G sc thread l A ∪₁
  (W_ l ∩₁ eq r ∪₁
   dom_rel (⦗Loc_ l⦘ ⨾ rf ⨾ ⦗eq r⦘) ∪₁
   dom_rel ((msg_rel G sc l ∪ ⦗Loc_ l⦘) ⨾ rf ⨾ ⦗eq r⦘)).
Proof.
  unfold t_acq.
  rewrite urr_acq_n_f_alt_union_eqv; eauto.
  unfold c_acq.
  unfold msg_rel.
  rewrite (@no_sb_to_init G); generalize (@sb_tid_init G); basic_solver 20.
Qed.

Lemma t_rel_union_eqv l l' A thread r
  (SB : dom_rel (sb ⨾ ⦗ eq r ⦘) ⊆₁ A)
  (RR : R r)
  (TID : tid r = thread) :
  t_rel G sc thread l l' (A ∪₁ eq r) ≡₁ t_rel G sc thread l l' A.
Proof.
  unfold t_rel, c_rel.
  rewrite (id_union A); rewrite !seq_union_r.
  arewrite (⦗W_ l' ∪₁ F⦘ ⨾ ⦗Tid_ thread ∪₁ Init⦘ ⨾ ⦗eq r⦘ ≡ ∅₂); rels.
  type_solver 21.
Qed.

Lemma t_rel_w_union_eqv l l0 A thread w locw
  (NINIT : ~ is_init w)
  (CCLOS : doma (sb ⨾ ⦗ A ⦘) A)
  (AACTS : A ⊆₁ E)
  (NINA  : ~ A w)
  (SB : doma (sb ⨾ ⦗eq w⦘) A)
  (ACTS: E w)
  (WW : W w)
  (LOC : loc lab w = Some locw)
  (TID : tid w = thread)
  (FREFL : forall l y (Ws : W y) (LOC : loc lab y = Some l), urr G sc l y y)
  (CREL : forall l l',
    c_rel G sc thread l l' (A ∪₁ eq w)
        ≡
    c_rel G sc thread l l' A ∪
    ⦗fun _ => l' = l⦘ ⨾
    ⦗Rel⦘ ⨾ ⦗Loc_ l'⦘ ⨾ ⦗eq w⦘ ∪
    urr G sc l ⨾ ⦗A⦘ ⨾ sb ⨾ ⦗ Rel ⦘ ⨾ ⦗Loc_ l'⦘ ⨾ ⦗eq w⦘)
  :
  t_rel G sc thread l0 l (A ∪₁ eq w) ∪₁
  (if Loc.eq_dec l0 l
   then W ∩₁ Loc_ l ∩₁ Tid_ thread ∩₁ (A ∪₁ eq w)
   else ∅)
    ≡₁
  if Loc.eq_dec l locw
  then (if (is_rel lab w)
        then t_cur G sc thread l0 A 
        else t_rel G sc thread l0 l A ∪₁
             (if Loc.eq_dec l0 l
              then W ∩₁ Loc_ l ∩₁ Tid_ thread ∩₁ A
              else ∅)) ∪₁
       (if Loc.eq_dec l0 locw then eq w else ∅)
  else
    t_rel G sc thread l0 l A ∪₁
    (if Loc.eq_dec l0 l
     then W ∩₁ Loc_ l ∩₁ Tid_ thread ∩₁ A
     else ∅).
Proof.
  rewrite !ite_alt; rewrite !iteb_alt; rewrite !ite_alt.
  rewrite !set_inter_union_r.
  rewrite ite_union_t.
  unfold t_rel at 1; rewrite CREL; auto.
  arewrite (W ∩₁ Loc_ l ∩₁ Tid_ thread ∩₁ eq w ≡₁ Loc_ l ∩₁ eq w) by basic_solver 12.
  assert (forall l,
          dom_rel (urr G sc l ⨾ ⦗A⦘ ⨾ sb ⨾ ⦗eq w⦘) ≡₁
          dom_rel (c_cur G sc (tid w) l A)) as CSB.
  { intros; unfold c_cur.
    split; intros x H; destruct H as [y H].
    all: hahn_rewrite <- seqA in H.
    hahn_rewrite <- seqA in H.
    all: apply seq_eqv_r in H; destruct H as [H X]; subst.
    { destruct H as [z [H PSB]].
      apply seq_eqv_r in H; desf.
      exists z; hahn_rewrite <- seqA; apply seq_eqv_r; split; auto.
      apply seq_eqv_r; split; auto.
      eapply sb_tid_init; eauto. }
    apply seq_eqv_r in H; desc.
    exists w; hahn_rewrite <- seqA; hahn_rewrite <- seqA.
    apply seq_eqv_r; split; auto.
    exists y; split.
    by basic_solver.
    destruct (classic (is_init y)) as [IN|NIN].
    { apply init_ninit_sb; auto. }
    destruct (same_thread G y w) as [[ST|ST]|ST]; desf.
    { by apply AACTS. }
    revert H0; basic_solver.
    exfalso; revert CCLOS; basic_solver. }
  assert (forall l' l'',
          dom_rel (c_rel G sc (tid w) l' l'' A) ∪₁
          dom_rel (c_cur G sc (tid w) l' A) ≡₁
          dom_rel (c_cur G sc (tid w) l' A)) as CURREL.
  by unfold c_rel, c_cur; basic_solver 12.

  destruct (classic (l = locw)) eqn:LL1; subst.
  { rewrite <- !ite_alt; rewrite !Loc.eq_dec_eq.
    rename locw into l.
    rewrite !ite_alt.
    arewrite (⦗Loc_ l⦘ ⨾ ⦗eq w⦘ ≡ ⦗eq w⦘) by basic_solver.
    rewrite !dom_union.
    destruct (classic (l0 = l)) eqn:LL2; subst.
    { rewrite <- !ite_alt; rewrite !Loc.eq_dec_eq.
      arewrite (⦗fun _ : actid => l = l⦘ ≡ ⦗fun _ : actid => True⦘).
      { split; intros x y H; red; red in H; split; desf. }
      rewrite seq_id_l.
      rewrite (fun x => set_unionC x (dom_rel (⦗Rel⦘ ⨾ ⦗eq w⦘))).
      rewrite !set_unionA; rewrite set_unionC.
      rewrite !set_unionA.
      arewrite (Loc_ l ∩₁ eq w ≡₁ eq w) by basic_solver.
      arewrite (eq w ∪₁ dom_rel (⦗fun a : actid => Rel a⦘ ⨾ ⦗eq w⦘) ≡₁ eq w) by basic_solver.
      rewrite <- !set_unionA.
      repeat (apply set_equiv_union; [|done]).
      rewrite <- iteb_alt.
      destruct (is_rel lab w) eqn:RELEQ.
      { arewrite (⦗Rel⦘ ⨾ ⦗eq w⦘ ≡ ⦗eq w⦘).
        { by apply seq_eqvK_l; ins; subst. }
        unfold t_cur.
        rewrite CSB; rewrite CURREL.
        split; intros x H; [|by left]; destruct H; desf.
        unfold c_cur.
        revert H; basic_solver 21. }
      arewrite (⦗fun a : actid => Rel a⦘ ⨾ ⦗eq w⦘ ≡ ∅₂) by basic_solver.
        by rels. }
    rewrite <- !ite_alt.
    rewrite !Loc.eq_dec_neq; auto.
    arewrite (⦗fun _ : actid => l = l0⦘ ≡ ∅₂).
    { split; rels; intros x y H; inv H. }
    rels.
    rewrite <- iteb_alt; destruct (is_rel lab w) eqn: REL.
    { arewrite (⦗Rel⦘ ⨾ ⦗eq w⦘ ≡ ⦗eq w⦘).
      { by apply seq_eqvK_l; ins; subst. }
      by rewrite CSB; rewrite CURREL. }
    arewrite (⦗Rel⦘ ⨾ ⦗eq w⦘ ≡ ∅₂).
    { split; rels; intros x y H; apply seq_eqv_r in H; desf; red in H; desf. }
    by rels. }
  rewrite <- !ite_alt; rewrite (@Loc.eq_dec_neq _ l locw); auto.
  rewrite !ite_alt.
  rewrite <- !id_inter.
  arewrite (Loc_ l ∩₁ eq w ≡₁ ∅) by basic_solver.
  unfold ifthenelse, t_rel; basic_solver 21.
Qed.

Lemma t_cur_urr_init
      wi (C : actid -> Prop) l thread
      (INC : C wi) (INIT : is_init wi) (LOC : Loc_ l wi):
  t_cur G sc thread l C wi.
Proof.
unfold t_cur, c_cur, urr.
generalize (init_w WF); unfold seq; basic_solver 42.
Qed.

Lemma urr_refl l y (YW : W y) (LOC : loc lab y = Some l):
  urr G sc l y y.
Proof.
unfold urr.
basic_solver 21.
Qed.

Lemma t_rel_if_other_thread
      C C' thread l l'
      (CINIT : Init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (CE : C' ⊆₁ E)
      (COVSTEP : forall a, tid a = thread -> C' a -> C a) :
  (t_rel G sc thread l l' C' ∪₁
   (if LocSet.Facts.eq_dec l l'
    then
      W ∩₁ Loc_ l' ∩₁ Tid_ thread ∩₁ C'
    else ∅)) ≡₁
  (t_rel G sc thread l l' C ∪₁
   (if LocSet.Facts.eq_dec l l'
    then
      W ∩₁ Loc_ l' ∩₁ Tid_ thread ∩₁ C
    else ∅)).
Proof.
  apply set_equiv_union; [by symmetry; apply t_rel_other_thread|].
  desf; basic_solver 21.
Qed.

Lemma s_tm_n_f_steps
      C C' l 
      (CINIT : Init ∩₁ E ⊆₁ C)
      (CINCL : C ⊆₁ C')
      (COVSTEP : forall a, C' a -> ~ C a -> ~ (F∩₁Sc) a) :
  S_tm G l C' ≡₁ S_tm G l C.
Proof.
  unfold S_tm, S_tmr.
  arewrite (⦗F∩₁Sc⦘ ⨾ ⦗C'⦘ ≡ ⦗F∩₁Sc⦘ ⨾ ⦗C⦘); [|done].
  split; [|by rewrite CINCL].
  unfolder; ins; desf.
  destruct (classic (C y)) as [H|H]; auto.
  exfalso; eapply COVSTEP; basic_solver.
Qed.


End CombRelationsMore.
