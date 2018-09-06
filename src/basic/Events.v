(******************************************************************************)
(** * Definition of execution graph events and labels *)
(******************************************************************************)

Require Import List.
From hahn Require Import Hahn.
From promising Require Import Basic Event.
Require Import AuxRel.

Set Implicit Arguments.

Definition thread_id := Basic.Ident.t.
Definition location := Loc.t.
Definition value := Const.t.

(******************************************************************************)
(** ** Execution graph events  *)
(******************************************************************************)

Inductive actid := 
  | InitEvent (l : location)
  | ThreadEvent (thread : thread_id) (index : nat).

Definition tid a := 
  match a with
    | InitEvent l => Coq.Numbers.BinNums.xH
    | ThreadEvent i _ => i
  end.

Definition is_tid i a : Prop := tid a = i.

Definition index a := 
  match a with
    | InitEvent l => 0
    | ThreadEvent _ n => n
  end.

Definition is_init a := 
  match a with
    | InitEvent _ => true
    | ThreadEvent _ _ => false
  end.

(******************************************************************************)
(** ** Same tid restriction *)
(******************************************************************************)

Definition same_tid := (fun x y => tid x = tid y).

Lemma restr_eq_rel_same_tid r :  restr_eq_rel tid r  ≡ r ∩ same_tid.
Proof. unfold same_tid; basic_solver. Qed.

Lemma loceq_same_tid (r: relation actid) (H: funeq tid r):
 r ⊆ r ∩ same_tid.
Proof.
unfold same_tid; basic_solver.
Qed.

Lemma same_tid_loceq (r: relation actid) (H: r ⊆ r ∩ same_tid):
 funeq tid r.
Proof.
unfold same_tid; unfolder; firstorder.
Qed.

(******************************************************************************)
(** ** Decidable equality *)
(******************************************************************************)

Lemma eq_dec_actid :
  forall x y : actid, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Qed.

(******************************************************************************)
(** ** Labels  *)
(******************************************************************************)

Inductive mode := 
  | Opln
  | Orlx
  | Oacq
  | Orel
  | Oacqrel
  | Osc.

Definition mode_le lhs rhs :=
  match lhs, rhs with
    | Opln, _ => true
    | _, Opln => false
    | Orlx, _ => true
    | _, Orlx => false
    | Oacq, Oacq
    | Oacq, Oacqrel
    | Orel, Orel
    | Orel, Oacqrel
    | Oacqrel, Oacqrel
    | _, Osc => true
    | _ , _ => false
  end.

Inductive x_mode := 
  | Xpln
  | Xacq.

Inductive label := 
  | Aload  (ex:bool) (o:mode) (l:location) (v:value)
  | Astore (s:x_mode) (o:mode) (l:location) (v:value)
  | Afence (o:mode).


(*
   The meaning of the modes in each case:
   (currently Opln is redundant, easy to remove in the future)

                  IMM        POWER      ARM 
   =================================================
   Aload Opln       rlx       ld         ldr
   Aload Orlx       rlx       ld         ldr
   Aload Oacq       acq       ld         ldapr (?)
   Aload Orel       rlx       ld         ldr
   Aload Oacqrel    acq       ld         ldapr (?)
   Aload Osc        acq       ld         ldapr (?)

   Astore Opln      rlx       st         str
   Astore Orlx      rlx       st         str
   Astore Oacq      rlx       st         str
   Astore Orel      rel       st         stlr
   Astore Oacqrel   rel       st         stlr
   Astore Osc       rel       st         stlr

   Afence Opln      no-op     no-op      no-op
   Afence Orlx      no-op     isync      F-ld
   Afence Oacq      acq       lwsync     F-ld
   Afence Orel      rel       lwsync     F-sy
   Afence Oacqrel   acq-rel   lwsync     F-sy
   Afence Osc       sc        sync       F-sy

 *)

Section Labels.

Variable A : Type.
Variable lab : A -> label.

Definition loc a :=
  match lab a with
  | Aload _ _ l _
  | Astore _ _ l _ => Some l
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload  _ _ _ v
  | Astore _ _ _ v => Some v
  | _ => None
  end.

Definition mod a :=
  match lab a with
  | Aload  _ o _ _
  | Astore _ o _ _
  | Afence o => o
  end.

Definition xmod a :=
  match lab a with
  | Astore x _ _ _ => Some x
  | _ => None
  end.

Definition is_r a := 
  match lab a with
  | Aload  _ _ _ _ => true
  | _ => false
  end.

Definition is_w a := 
  match lab a with
  | Astore _ _ _ _ => true
  | _ => false
  end.

Definition is_f a := 
  match lab a with
  | Afence _ => true
  | _ => false
  end.

Definition is_only_pln a : bool :=
  match mod a with
  | Opln => true
  | _ => false
  end.
Definition is_rlx a : bool := mode_le Orlx (mod a).
Definition is_acq a : bool := mode_le Oacq (mod a).
Definition is_rel a : bool := mode_le Orel (mod a).
Definition is_acqrel a : bool := mode_le Oacqrel (mod a).
Definition is_sc a : bool :=
  match mod a with
  | Osc => true
  | _ => false
  end.

Definition is_ra a : bool := is_acq a || is_rel a.

Lemma lab_rwf a : is_r a \/ is_w a \/ is_f a.
Proof. unfold is_r, is_w, is_f; destruct (lab a); auto. Qed.

Definition is_xacq a := 
  match xmod a with
  | Some Xacq => true
  | _ => false
  end.

Definition R_ex a :=
  match lab a with
  | Aload r _ _ _ => r
  | _ => false
  end.

Lemma R_ex_in_R : R_ex ⊆₁ is_r.
Proof.
unfold R_ex, is_r; basic_solver.
Qed.

Definition rmwmod a :=
  match lab a with
  | Aload r _ _ _ => Some r
  | _ => None
  end.


(******************************************************************************)
(** ** Same location restriction *)
(******************************************************************************)

Definition same_loc := (fun x y => loc x = loc y).

Lemma restr_eq_rel_same_loc r :  restr_eq_rel loc r  ≡ r ∩ same_loc.
Proof. unfold same_loc; basic_solver. Qed.

Lemma loceq_same_loc (r: relation A) (H: funeq loc r):
 r ⊆ r ∩ same_loc.
Proof.
unfold same_loc; basic_solver.
Qed.

Lemma same_loc_loceq (r: relation A) (H: r ⊆ r ∩ same_loc):
 funeq loc r.
Proof.
unfold same_loc; unfolder; firstorder.
Qed.

Lemma same_loc_trans : transitive same_loc.
Proof. unfold same_loc; red; ins. by rewrite H. Qed.

Lemma same_loc_sym : symmetric same_loc.
Proof. unfold same_loc; red; ins. Qed.

(******************************************************************************)
(** ** Values and locations getters  *)
(******************************************************************************)

Lemma is_w_val x (WX : is_w x) : exists v, val x = Some v.
Proof. unfold is_w, val in *; desf. eexists; eauto. Qed.

Lemma is_w_loc x (WX : is_w x) : exists l, loc x = Some l.
Proof. unfold is_w, loc in *; desf. eexists; eauto. Qed.

Lemma is_r_val x (WX : is_r x) : exists v, val x = Some v.
Proof. unfold is_r, val in *; desf. eexists; eauto. Qed.

Lemma is_r_loc x (WX : is_r x) : exists l, loc x = Some l.
Proof. unfold is_r, loc in *; desf. eexists; eauto. Qed.

End Labels.

(******************************************************************************)
(** ** Identical labeling up to value  *)
(******************************************************************************)

Definition same_label_up_to_value label1 label2 :=
  match label1, label2 with
  | Aload  r1 o1 l1 _, Aload  r2 o2 l2 _ => r1 = r2 /\ o1 = o2 /\ l1 = l2
  | Astore s1 o1 l1 _, Astore s2 o2 l2 _ => s1 = s2 /\ o1 = o2 /\ l1 = l2
  | Afence o1, Afence o2 => o1 = o2
  | _,_ => False
  end.

Definition same_lab_up_to_value lab1 lab2 :=
  forall (e : actid), same_label_up_to_value (lab1 e) (lab2 e).


Lemma same_label_loc lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  loc lab1 = loc lab2.
Proof.
unfold loc, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_mod lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  mod lab1 = mod lab2.
Proof.
unfold mod, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_xmod lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  xmod lab1 = xmod lab2.
Proof.
unfold xmod, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_is_r lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_r lab1 = is_r lab2.
Proof.
unfold is_r, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_is_w lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_w lab1 = is_w lab2.
Proof.
unfold is_w, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_is_f lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_f lab1 = is_f lab2.
Proof.
unfold is_f, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_R_ex lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  R_ex lab1 = R_ex lab2.
Proof.
unfold R_ex, same_lab_up_to_value, same_label_up_to_value in *.
extensionality a; specialize (SAME a).
desf; desf.
Qed.

Lemma same_label_is_only_pln lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_only_pln lab1 = is_only_pln lab2.
Proof.
unfold is_only_pln; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_rlx lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_rlx lab1 = is_rlx lab2.
Proof.
unfold is_rlx; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_acq lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_acq lab1 = is_acq lab2.
Proof.
unfold is_acq; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_rel lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_rel lab1 = is_rel lab2.
Proof.
unfold is_rel; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_acqrel lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_acqrel lab1 = is_acqrel lab2.
Proof.
unfold is_acqrel; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_sc lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_sc lab1 = is_sc lab2.
Proof.
unfold is_sc; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_ra lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_ra lab1 = is_ra lab2.
Proof.
unfold is_ra, is_rel, is_acq; erewrite same_label_mod; eauto.
Qed.

Lemma same_label_is_xacq lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  is_xacq lab1 = is_xacq lab2.
Proof.
unfold is_xacq; erewrite same_label_xmod; eauto.
Qed.


Lemma same_label_same_loc lab1 lab2 (SAME: same_lab_up_to_value lab1 lab2) :
  same_loc lab1 = same_loc lab2.
Proof.
unfold same_loc; erewrite same_label_loc; eauto.
Qed.

(******************************************************************************)
(** ** Sequenced-Before *)
(******************************************************************************)

Require Import Omega.

Definition ext_sb a b := 
  match a, b with 
    | _, InitEvent _ => False
    | InitEvent _, ThreadEvent _ _ => True
    | ThreadEvent t i, ThreadEvent t' i' => t = t' /\ i < i' 
   end.

Lemma ext_sb_trans : transitive ext_sb.
Proof.
unfold ext_sb; red; ins.
destruct x,y,z; ins; desf; splits; eauto.
by rewrite H2.
Qed.

Lemma ext_sb_irr : irreflexive ext_sb.
Proof.
unfold ext_sb; red; ins.
destruct x; firstorder.
Qed.

Lemma ext_sb_to_non_init : ext_sb ⊆ ext_sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
unfold is_init, ext_sb; basic_solver.
Qed.

Lemma ext_sb_semi_total_l x y z 
  (N: ~ is_init x) (NEQ: index y <> index z) (XY: ext_sb x y) (XZ: ext_sb x z): 
  ext_sb y z \/ ext_sb z y.
Proof.
unfold ext_sb in *.
destruct x,y,z; ins; desf.
cut(index1 < index2 \/ index2 < index1).
tauto.
omega.
Qed.

Lemma ext_sb_semi_total_r x y z 
  (NEQ: index y <> index z) (XY: ext_sb y x) (XZ: ext_sb z x): 
  ext_sb y z \/ ext_sb z y.
Proof.
unfold ext_sb in *.
destruct x,y,z; ins; desf; eauto.
cut(index1 < index2 \/ index2 < index1).
tauto.
omega.
Qed.

Lemma ext_sb_tid_init x y (SB : ext_sb x y): tid x = tid y \/ is_init x.
Proof.
unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

Lemma ext_sb_tid_init': ext_sb ⊆ ext_sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ ext_sb.
Proof.
generalize ext_sb_tid_init; firstorder.
Qed.

Lemma tid_ext_sb: same_tid ⊆ ext_sb^? ∪ ext_sb^{-1} ∪ (is_init × is_init).
Proof.
unfold ext_sb, same_tid, tid, is_init, cross_rel; unfolder.
ins; destruct x, y; desf; eauto.
cut(index0 < index1 \/ index1 < index0 \/ index0 = index1).
by ins; desf; eauto.
omega.
Qed.

Lemma tid_n_init_ext_sb: same_tid ⨾ ⦗set_compl is_init⦘ ⊆ ext_sb^? ∪ ext_sb^{-1}.
Proof.
rewrite tid_ext_sb at 1.
unfold cross_rel.
basic_solver 12.
Qed.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

Hint Unfold set_union set_inter is_r is_w is_f R_ex : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "type_solver" int_or_var(index) := 
  type_unfolder; basic_solver index.

Tactic Notation "type_solver" :=  type_solver 4.

Hint Unfold set_union set_inter is_r is_w is_f R_ex : mode_unfolderDb.
Hint Unfold is_only_pln is_rlx is_rel is_acq is_acqrel is_sc is_ra is_xacq : mode_unfolderDb.
Tactic Notation "mode_unfolder" :=  repeat autounfold with mode_unfolderDb in *.

Tactic Notation "mode_solver" int_or_var(index) := 
  mode_unfolder; basic_solver index.

Tactic Notation "mode_solver" :=  mode_solver 4.