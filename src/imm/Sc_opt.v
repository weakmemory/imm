(******************************************************************************)
(** * Weakening redundant SC accesses in IMM *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Dom.
Require Import Events Execution Execution_eco.
Require Import imm_common imm_hb imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Sc_opt.

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
Notation "'detour'" := G.(detour).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).
Notation "'rs'" := G.(rs).
Notation "'hb'" := G.(hb).
Notation "'ppo'" := G.(ppo).
Notation "'psc'" := G.(psc).
Notation "'bob'" := G.(bob).
Notation "'scb'" := G.(scb).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'sb_neq_loc'" := (sb \ same_loc).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type COH : coherence G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Notation "'sb''" := (sb \ rmw).
Notation "'ar'" := (ar G).
Notation "'br'" := (br G).

Lemma global_sc_helper WF
  (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb) :
  ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^? ⨾
    (⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW∩₁Sc⦘)^* ⨾
      eco^? ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ br⁺.
Proof.
  assert (transitive eco) as TECO by (by apply eco_trans).
  assert (transitive hb ) as THB  by (by apply hb_trans).

  assert (⦗F ∩₁ Sc⦘ ⨾ hb ⨾ eco^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ br⁺) as HH.
  { rewrite crE. relsf.
    unionL.
    { by apply f_sc_hb_f_sc_in_br. }
    rewrite <- ct_step. unfold imm.br, imm.psc.
      by unionR left. }

  eapply rt_ind_left with
      (P:= fun __ => ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ __ ⨾ eco ^? ⨾ hb ⨾ ⦗F∩₁Sc⦘).
  { eauto with hahn. }
  { relsf. }
  intros k IH.
  arewrite (⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW∩₁Sc⦘ ⊆
            ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ∪ eco)
    by basic_solver 42.
  rewrite HSC.
  arewrite (⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ (hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb ∪ eco) ⊆ 
            ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^? ∪
              ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^?)
    by basic_solver 42.
  relsf.
  rewrite !seqA.
  rewrite <- seq_eqvK at 2; rewrite !seqA.
  sin_rewrite IH.
  apply inclusion_union_l; try done.
  rewrite <- !seqA with (r3 := br⁺).
  sin_rewrite HH.
  apply transitiveI. apply transitive_ct.
Qed.

Lemma RW_scb_RW :
  ⦗RW∩₁Sc⦘ ⨾ scb ⨾ ⦗RW∩₁Sc⦘ ⊆
  ⦗RW∩₁Sc⦘ ⨾
    (sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ (hb∩same_loc) ⨾ ⦗RW⦘ ∪ co ∪ fr)
      ⨾ ⦗RW∩₁Sc⦘.
Proof. unfold imm.scb; basic_solver 42. Qed.

Lemma global_sc WF 
      (COH: irreflexive (hb ⨾ eco^?))
      (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
      (ACYC: acyclic br) :
  acyclic ar.
Proof.
  assert (transitive eco) as TECO by (by apply eco_trans).
  assert (transitive hb ) as THB  by (by apply hb_trans).
  unfold imm.ar, imm_common.ar_int.
  admit.
Admitted.
  
(* TODO: continue from here *)
  (* eapply acyc_dom with (d:= RW∩₁Sc) (e:= F∩₁Sc); try edone. *)
  (* { unfold imm.ar,imm.psc, imm.psc_base. *)
  (*   arewrite (⦗Sc⦘ ≡ ⦗RW∩₁Sc⦘ ∪ ⦗F∩₁Sc⦘) by type_solver 42. *)
  (*   basic_solver 42. *)
  (*   basic_solver 42. } *)
  (* { solve_type_mismatch 6. } *)
  (* { unfold imm.psc, imm.psc_base; relsf; rewrite !seqA. *)
  (*   arewrite_false !(⦗RW∩₁Sc⦘ ⨾ ⦗F∩₁Sc⦘). *)
  (*   solve_type_mismatch 6. *)
  (*   arewrite_false !( ⦗F∩₁Sc⦘ ⨾ ⦗RW∩₁Sc⦘). *)
  (*   solve_type_mismatch 6. *)
  (*   rels. *)
  (*   arewrite (⦗RW∩₁Sc⦘ ⨾ ⦗Sc⦘ ⊆ ⦗RW∩₁Sc⦘). *)
  (*   arewrite (⦗Sc⦘ ⨾ ⦗RW∩₁Sc⦘ ⊆ ⦗RW∩₁Sc⦘). *)
  (*   rewrite RW_scb_RW. *)
  (*   rewrite hb_loc_in_eco; auto. *)
  (*   arewrite (sb_neq_loc ⊆ sb'). *)
  (*   { by apply sb_neq_loc_in_sb_minus_rmw; auto. } *)
  (*   arewrite (sb ⊆ sb' ∪ rmw) at 1. *)
  (*   { by unfold inclusion, minus_rel, union; ins; tauto. } *)
  (*   rewrite rmw_in_rb at 2; auto. *)
  (*   rewrite mo_in_eco; auto. *)
  (*   rewrite rb_in_eco; auto. *)
  (*   rewrite <- !unionA. *)
  (*   relsf. *)
  (*   arewrite (⦗RW∩₁Sc⦘ ⨾ sb' ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb). *)
  (*   { by rewrite <- HSC; rels. } *)
  (*   arewrite (⦗RW∩₁Sc⦘ ⨾ sb' ⨾ hb ⨾ sb' ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb). *)
  (*   { by rewrite <- HSC; rels; basic_solver 10. } *)
  (*   eapply acyclic_mon with (r := hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb ∪ ⦗RW∩₁Sc⦘ ⨾ eco ⨾ ⦗RW∩₁Sc⦘). *)
  (*   2: repeat apply inclusion_union_l; rels. *)
  (*   apply acyclic_utt; splits. *)
  (*   { apply transitiveI; arewrite_id ⦗F∩₁Sc⦘ at 1; relsf. } *)
  (*   { apply transitiveI. *)
  (*     arewrite_id ⦗RW∩₁Sc⦘ at 2; relsf. *)
  (*     arewrite_id ⦗RW∩₁Sc⦘ at 2; relsf. } *)
  (*   { arewrite_id ⦗F∩₁Sc⦘ at 1; relsf. *)
  (*       by apply irr_hb. } *)
  (*   { arewrite_id ⦗RW∩₁Sc⦘; relsf. *)
  (*       by apply irr_eco. } *)
  (*   arewrite (⦗F∩₁Sc⦘ ⊆ ⦗F∩₁Sc⦘ ⨾ ⦗F∩₁Sc⦘) by basic_solver. *)
  (*   do 2 (apply acyclic_seqC; try rewrite !seqA). *)
  (*   eapply acyclic_mon with (r := psc); try done. *)
  (*   unfold imm.psc. *)
  (*   basic_solver 12. *)
  (* { by rewrite psc_f. } *)
  (* rewrite psc_rw_rw; try assumption. *)
  (* rewrite RW_scb_RW. *)
  (* arewrite ( *)
  (*     sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ hb|loc ⨾ ⦗RW⦘ ∪ mo ∪ rb  *)
  (*                                                       ⊆ sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco *)
  (*   ). *)
  (* { arewrite (sb ⊆ sb' ∪ rmw) by (by apply inclusion_union_minus). *)
  (*   rewrite rmw_in_rb at 2; try assumption. *)
  (*   rewrite rb_in_eco, mo_in_eco, sb_neq_loc_in_sb_minus_rmw, hb_loc_in_eco; try assumption. *)
  (*   basic_solver 10. } *)
  (* sin_rewrite psc_rw_f; try assumption. *)
  (* sin_rewrite psc_rw; try assumption. *)
  (* rewrite psc_f; try assumption. *)
  (* arewrite_id ⦗RW∩₁Sc⦘ at 1. *)
  (* arewrite_id ⦗RW∩₁Sc⦘ at 3. *)
  (* rels. *)
  (* rewrite <- !seqA with (r3 := psc ^* ), global_sc_helper; try assumption. *)
  (* red; rels. *)

(* Definition change_mode (l: label) (m: mode) : label := 
  match l with
  | Aload l v _ => Aload l v m
  | Astore l v _ => Astore l v m
  | Afence _ => Afence m
  end. *)
  
(* Definition change_modes (G: execution) (A: event -> Prop) (m: mode): execution :=
  Build_execution 
    acts
    (fun a => if (A a) then change_mode (lab a) m else lab a)
    sb rmw rf mo. *)

(* Lemma transf_g
  (NO_SC: ⦗Sc⦘ ≡ ∅₂)
  A (A_SUB: A ⊆₁ R_acq ∪₁ W_rel)
  (A1: ⦗A⦘ ⨾ (sb' ∪ sb'⨾hb⨾sb') ⨾ ⦗A⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
  (A2: ⦗A⦘ ⨾ rmw ≡ rmw ⨾ ⦗A⦘)
  (G' : execution) (CHANGE: G' = G)
  : consistent G'.
Proof.
Admitted. *)

End Sc_opt.