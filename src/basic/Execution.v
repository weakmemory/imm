(******************************************************************************)
(** * Definition of executions (common basis for all types of executions) *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

(** Definition of an execution *)
Record execution :=
  { acts : list actid;
    lab : actid -> label;
    rmw : actid -> actid -> Prop ;
    data : actid -> actid -> Prop ;   (** data dependency *)
    addr : actid -> actid -> Prop ;   (** address dependency *)
    ctrl : actid -> actid -> Prop ;   (** control dependency *)

    (** Representation of a data dependency to failed RMW.
        It goes from a read to an exclusive read.
        Consider the example:

        a := [x];
        CAS(y, a, 1);
        
        There is an execution w/ failing CAS. In the execution,
        there is an rmw_dep edge between a read event representing `a := [x]'
        and a read event representing failed `CAS(y, a, 1)'.
     *)
    rmw_dep : actid -> actid -> Prop ;


(*     ctrli : relation actid ;  (** control+isync on Power *) *)
    rf : actid -> actid -> Prop ;
    co : actid -> actid -> Prop ;
  }.

Section Execution.

Variable G : execution.

Definition acts_set := fun x => In x G.(acts).

Notation "'E'" := acts_set.
Notation "'lab'" := G.(lab).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

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

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition sb := ⦗E⦘ ⨾ ext_sb ⨾  ⦗E⦘.

Record Wf :=
  {  wf_index : forall a b, 
    E a /\ E b /\ a <> b /\ tid a = tid b /\ ~ is_init a -> index a <> index b ;
    data_in_sb : data ⊆ sb ;
    wf_dataD : data ≡ ⦗R⦘ ⨾ data ⨾ ⦗W⦘ ;
    addr_in_sb : addr ⊆ sb ;
    wf_addrD : addr ≡ ⦗R⦘ ⨾ addr ⨾ ⦗RW⦘ ;
    ctrl_in_sb : ctrl ⊆ sb ;
    wf_ctrlD : ctrl ≡ ⦗R⦘ ⨾ ctrl ;
    ctrl_sb : ctrl ⨾ sb ⊆ ctrl ;
    wf_rmwD : rmw ≡ ⦗R_ex⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    wf_rmwl : rmw ⊆ same_loc ;
    wf_rmwi : rmw ⊆ immediate sb ;
    wf_rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ;
    wf_rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ;
    wf_rfl : rf ⊆ same_loc ;
    wf_rfv : funeq val rf ;
    wf_rff : functional rf⁻¹ ;
    wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    wf_col : co ⊆ same_loc ;
    co_trans : transitive co ;
    wf_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co ;
    co_irr : irreflexive co ;
    wf_init : forall l, (exists b, E b /\ loc b = Some l) -> E (InitEvent l) ;
    wf_init_lab : forall l, lab (InitEvent l) = Astore Xpln Opln l 0 ;

    rmw_dep_in_sb : rmw_dep ⊆ sb ;
    wf_rmw_depD : rmw_dep ≡ ⦗R⦘ ⨾ rmw_dep ⨾ ⦗R_ex⦘ ;
(*     failed_rmw_fail : rmw_dep ⨾ rmw ⊆ ∅₂ ; *)
  }.
(*   ⟪  wf_rmw_deps : rmw ⊆ data ∪ addr ∪ ctrl ⟫ /\
  ⟪  wf_rmw_ctrl : rmw ⨾ sb ⊆ ctrl ⟫. *)

Implicit Type WF : Wf.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* reads-before, aka from-read *)
Definition fr := rf⁻¹ ⨾ co.

Definition deps := data ∪ addr ∪ ctrl.

(******************************************************************************)
(** ** Consistency definitions  *)
(******************************************************************************)

Definition complete := E ∩₁ R  ⊆₁ codom_rel rf.
Definition rmw_atomicity := rmw ∩ ((fr \ sb) ⨾ (co \ sb)) ⊆ ∅₂.

(******************************************************************************)
(** ** Basic transitivity properties *)
(******************************************************************************)

Lemma sb_trans : transitive sb.
Proof.
unfold sb; unfolder; ins; desf; splits; auto.
eby eapply ext_sb_trans.
Qed.

Lemma sb_sb : sb ⨾ sb ⊆ sb.
Proof.
generalize sb_trans; basic_solver 21.
Qed.

Lemma sb_same_loc_trans: transitive (sb ∩ same_loc).
Proof.
apply transitiveI.
unfold Events.same_loc.
unfolder; ins; desf; eauto.
splits.
generalize sb_trans; basic_solver 21.
congruence.
Qed.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_neq_loc_in_sb : sb \ same_loc ⊆ sb.
Proof. basic_solver. Qed.

Lemma fr_co WF : fr ⨾ co ⊆ fr.
Proof. by unfold fr; rewrite seqA, rewrite_trans; [|apply WF]. Qed.

Lemma rmw_in_sb WF: rmw ⊆ sb.
Proof. rewrite wf_rmwi; basic_solver. Qed.

Lemma deps_in_sb WF: deps ⊆ sb.
Proof. unfold deps; unionL; apply WF. Qed.

(*
Lemma rmw_in_deps WF : rmw ⊆ deps.
Proof. apply WF. Qed.
Lemma rmw_ctrl WF : rmw ⨾ sb ⊆ ctrl.
Proof. apply WF. Qed.
*)

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma loceq_rf WF : funeq loc rf.
Proof. apply WF. Qed.

Lemma loceq_co WF : funeq loc co.
Proof. apply WF. Qed.

Lemma loceq_rmw WF : funeq loc rmw.
Proof. apply WF. Qed.

Lemma loceq_fr WF : funeq loc fr.
Proof.
unfold funeq.
unfold fr; unfolder; ins; desf.
generalize (loceq_co WF), (loceq_rf WF).
transitivity (loc z); [symmetry; eauto|eauto].
Qed.

Lemma wf_frl WF : fr ⊆ same_loc.
Proof.
unfold fr.
rewrite (wf_rfl WF), (wf_col WF).
unfold Events.same_loc.
unfolder; ins; desc; congruence. 
Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘.
Proof. 
split; [|basic_solver].
unfold sb; basic_solver 42. 
Qed.

Lemma wf_dataE WF: data ≡ ⦗E⦘ ⨾ data ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (data ⊆ data ∩ data) at 1.
rewrite (data_in_sb WF) at 1.
rewrite wf_sbE at 1.
basic_solver.
Qed.

Lemma wf_addrE WF: addr ≡ ⦗E⦘ ⨾ addr ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (addr ⊆ addr ∩ addr) at 1.
rewrite (addr_in_sb WF) at 1.
rewrite wf_sbE at 1.
basic_solver.
Qed.

Lemma wf_ctrlE WF: ctrl ≡ ⦗E⦘ ⨾ ctrl ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (ctrl ⊆ ctrl ∩ ctrl) at 1.
rewrite (ctrl_in_sb WF) at 1.
rewrite wf_sbE at 1.
basic_solver.
Qed.

Lemma wf_rmw_depE WF: rmw_dep ≡ ⦗E⦘ ⨾ rmw_dep ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (rmw_dep ⊆ rmw_dep ∩ rmw_dep) at 1.
rewrite (rmw_dep_in_sb WF) at 1.
rewrite wf_sbE at 1.
basic_solver.
Qed.

Lemma wf_depsE WF: deps ≡ ⦗E⦘ ⨾ deps ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold deps.
rewrite (wf_dataE WF) at 1.
rewrite (wf_ctrlE WF) at 1.
rewrite (wf_addrE WF) at 1.
basic_solver.
Qed.

Lemma wf_rmwE WF : rmw ≡ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (rmw ⊆ rmw ∩ rmw) at 1.
rewrite (wf_rmwi WF) at 1.
arewrite (immediate sb ⊆ sb).
rewrite wf_sbE.
basic_solver.
Qed.

Lemma wf_frE WF : fr ≡ ⦗E⦘ ⨾ fr ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold fr.
rewrite (wf_rfE WF) at 1.
rewrite (wf_coE WF) at 1.
basic_solver.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_frD WF : fr ≡ ⦗R⦘ ⨾ fr ⨾ ⦗W⦘.
Proof.
split; [|basic_solver].
unfold fr.
rewrite (wf_rfD WF) at 1.
rewrite (wf_coD WF) at 1.
basic_solver.
Qed.

Lemma wf_depsD WF : deps ≡ ⦗R⦘ ⨾ deps.
Proof.
split; [|basic_solver].
unfold deps.
rewrite (wf_dataD WF) at 1.
rewrite (wf_ctrlD WF) at 1.
rewrite (wf_addrD WF) at 1.
basic_solver.
Qed.

(******************************************************************************)
(** ** Irreflexive relations *)
(******************************************************************************)

Lemma sb_irr : irreflexive sb.
Proof.
unfold sb; unfolder; ins; desf.
eby eapply ext_sb_irr.
Qed.

Lemma fr_irr WF : irreflexive fr.
Proof.
rewrite (wf_frD WF); type_solver.
Qed.

(******************************************************************************)
(** ** Acyclic relations *)
(******************************************************************************)

Lemma sb_acyclic : acyclic sb.
Proof.
apply trans_irr_acyclic; [apply sb_irr| apply sb_trans]. 
Qed.

Lemma co_acyclic WF: acyclic co.
Proof.
by apply trans_irr_acyclic; [apply co_irr| apply co_trans]. 
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma init_w WF: is_init ⊆₁ W.
Proof.
unfolder; ins.
unfold is_init in *; destruct x; desf.
specialize (wf_init_lab WF l); unfold is_w; desf.
Qed.

Lemma init_pln WF: is_init ⊆₁ Pln.
Proof.
unfolder; ins.
unfold is_init in *; destruct x; desf.
specialize (wf_init_lab WF l); unfold is_only_pln, Events.mod; desf.
Qed.

Lemma read_or_fence_is_not_init WF a (A: R a \/ F a) : ~ is_init a.
Proof.
generalize ((init_w WF) a).
type_solver.
Qed.

Lemma no_sb_to_init : sb ≡ sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
unfold sb; rewrite ext_sb_to_non_init at 1; basic_solver.
Qed.

Lemma no_rf_to_init WF : rf ≡ rf ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite (wf_rfD WF) at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma rmw_from_non_init WF : rmw ≡ ⦗fun x => ~ is_init x⦘ ⨾ rmw.
Proof.
split; [|basic_solver].
rewrite (wf_rmwD WF), R_ex_in_R at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

Lemma init_same_loc WF a b (A: is_init a) (B: is_init b) (LOC: loc a = loc b): 
  a = b.
Proof.
destruct a, b; desf.
cut (l = l0); [by ins; subst|].
unfold Events.loc in LOC.
rewrite (wf_init_lab WF l), (wf_init_lab WF l0) in LOC; desf.
Qed.

(******************************************************************************)
(** ** More properties *)
(******************************************************************************)

Lemma sb_semi_total_l x y z 
  WF (N: ~ is_init x) (NEQ: y <> z) (XY: sb x y) (XZ: sb x z): 
  sb y z \/ sb z y.
Proof.
unfold sb in *; unfolder in *; desf.
cut (ext_sb y z \/ ext_sb z y); [basic_solver 12|].
eapply ext_sb_semi_total_l; eauto.
eapply WF; splits; eauto.
by unfold ext_sb in *; destruct y,z; ins; desf; desf.
by unfold ext_sb in *; destruct y,z; ins; desf; desf.
Qed.

Lemma sb_semi_total_r x y z 
  WF (N: ~ is_init z) (NEQ: y <> z) (XY: sb y x) (XZ: sb z x): 
  sb y z \/ sb z y.
Proof.
cut ((sb ∪ sb⁻¹) y z); [basic_solver|].
unfold sb in *; unfolder in *; desf.
destruct (classic (is_init y)).
unfold ext_sb; basic_solver.
cut (ext_sb y z \/ ext_sb z y); [basic_solver|].
eapply ext_sb_semi_total_r; eauto.
eapply WF; splits; eauto.
unfold ext_sb in *; destruct y,z; ins; desf; desf.
Qed.

Lemma sb_tid_init x y (SB : sb x y): tid x = tid y \/ is_init x.
Proof.
generalize ext_sb_tid_init; unfold sb in *.
unfolder in *; basic_solver.
Qed.

Lemma sb_tid_init': sb ≡ sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ sb.
Proof.
split; [|basic_solver].
unfold sb.
rewrite ext_sb_tid_init' at 1.
basic_solver 42.
Qed.

Lemma tid_sb: ⦗E⦘ ⨾ same_tid ⨾  ⦗E⦘ ⊆ sb^? ∪ sb^{-1} ∪ (is_init × is_init).
Proof.
unfold sb.
rewrite tid_ext_sb.
basic_solver 21.
Qed.

Lemma tid_n_init_sb: ⦗E⦘ ⨾ same_tid ⨾ ⦗set_compl is_init⦘  ⨾  ⦗E⦘ ⊆ sb^? ∪ sb^{-1}.
Proof.
unfold sb.
sin_rewrite tid_n_init_ext_sb.
basic_solver 21.
Qed.

Lemma init_ninit_sb (WF : Wf) x y (INIT : is_init x) (ININE : E x) (INE : E y)
      (NINIT : ~ is_init y): sb x y.
Proof. 
unfold sb, ext_sb; basic_solver.
Qed.

Lemma same_thread x y (X : E x) (Y : E y)
      (NINIT : ~ is_init x) (ST : tid x = tid y):
  sb^? x y \/ sb y x.
Proof.
cut (sb^? y x \/ sb x y); [basic_solver|].
generalize tid_n_init_sb.
unfold same_tid; basic_solver 10.
Qed.

Lemma sb_immediate_adjacent WF:
 ⦗fun a => ~ is_init a⦘ ⨾ immediate sb ≡ ⦗fun a => ~ is_init a⦘ ⨾ (adjacent sb ∩ sb).
Proof.
apply immediate_adjacent.
- unfolder; ins; desf; destruct (classic (x=y)); auto.
  forward (apply (@sb_semi_total_r z y x)); eauto; tauto.
- unfolder; ins; desf; destruct (classic (x=y)); auto.
  forward (apply (@sb_semi_total_l z y x)); eauto; tauto.
- apply sb_trans.
- apply sb_irr.
Qed.

Lemma sb_transp_rmw  WF : sb ⨾ rmw ^{-1} ⊆ sb^?.
Proof.
rewrite (rmw_from_non_init WF).
rewrite (wf_rmwi WF); clear -WF.
rewrite (sb_immediate_adjacent WF).
unfold adjacent; basic_solver.
Qed.

Lemma transp_rmw_sb  WF :  rmw ^{-1} ⨾ sb ⊆ sb^?.
Proof.
rewrite (rmw_from_non_init WF).
rewrite (wf_rmwi WF); clear -WF.
rewrite (sb_immediate_adjacent WF).
unfold adjacent; basic_solver.
Qed.

Lemma rf_rf WF : rf ⨾ rf ≡ ∅₂.
Proof. rewrite (wf_rfD WF); type_solver. Qed.
Lemma rf_co WF : rf ⨾ co ≡ ∅₂.
Proof. rewrite (wf_rfD WF), (wf_coD WF); type_solver. Qed.
Lemma co_transp_rf WF : co ⨾  rf⁻¹ ≡ ∅₂.
Proof. rewrite (wf_rfD WF), (wf_coD WF); type_solver. Qed.
Lemma co_fr WF : co ⨾ fr ≡ ∅₂.
Proof. rewrite (wf_coD WF), (wf_frD WF); type_solver. Qed.
Lemma fr_fr WF : fr ⨾ fr ≡ ∅₂.
Proof. rewrite (wf_frD WF); type_solver. Qed.
Lemma rf_transp_rf WF: rf ⨾ rf⁻¹ ⊆ ⦗fun _ => True⦘.
Proof. by apply functional_alt, WF. Qed.
Lemma rf_fr WF : rf ⨾ fr ⊆ co.
Proof. unfold fr; sin_rewrite rf_transp_rf; rels. Qed.
Lemma rmw_in_sb_loc WF: rmw ⊆ sb ∩ same_loc.
Proof. by rewrite (loceq_same_loc (loceq_rmw WF)), (rmw_in_sb WF). Qed.
Lemma rf_irr WF: irreflexive rf.
Proof. rewrite (wf_rfD WF); type_solver. Qed.
Lemma co_co WF: co ⨾ co ⊆ co.
Proof. apply rewrite_trans, WF. Qed.

(*
Lemma rmw_sb_ct WF: (rmw ⨾ sb)⁺ ⊆ rmw ⨾ sb.
Proof.
rewrite ct_begin. 
hahn_frame. rewrite (rmw_in_sb WF).
generalize sb_trans; ins; relsf.
Qed.

Lemma rmw_sb_rt WF: (rmw ⨾ sb)＊ ⊆ (rmw ⨾ sb)^?.
Proof. 
rewrite rtE, (rmw_sb_ct WF); basic_solver.
Qed.

Lemma rmw_sb_trans WF: transitive (rmw ⨾ sb).
Proof.
apply transitiveI.
arewrite (rmw ⨾ sb ⊆ (rmw ⨾ sb)＊) at 2.
rewrite <- seqA; rewrite <- ct_begin.
by rewrite (rmw_sb_ct WF).
Qed.
*)

Lemma wf_rmwt WF: rmw ⊆ same_tid.
Proof.
rewrite (rmw_from_non_init WF).
rewrite (rmw_in_sb WF), sb_tid_init'.
basic_solver.
Qed.

Lemma wf_rmwf WF: functional rmw.
Proof.
rewrite (rmw_from_non_init WF).
rewrite (wf_rmwi WF).
rewrite (sb_immediate_adjacent WF).
unfolder; ins; desc.
eapply adjacent_uniqe1; eauto.
apply sb_acyclic.
Qed.

Lemma wf_rmw_invf WF: functional (rmw)⁻¹.
Proof.
rewrite (rmw_from_non_init WF).
rewrite (wf_rmwi WF).
rewrite (sb_immediate_adjacent WF).
unfolder; ins; desc.
eapply adjacent_uniqe2; eauto.
apply sb_acyclic.
Qed.


(******************************************************************************)
(** ** external-internal restrictions *)
(******************************************************************************)

Definition rfe := rf \ sb.
Definition coe := co \ sb.
Definition fre := fr \ sb.
Definition rfi := rf ∩ sb.
Definition coi := co ∩ sb.
Definition fri := fr ∩ sb.

Lemma ri_union_re r : r ≡ r ∩ sb ∪ r \ sb.
Proof. unfolder; split; ins; desf; tauto. Qed.

Lemma rfi_union_rfe : rf ≡ rfi ∪ rfe.
Proof. apply ri_union_re. Qed.
Lemma coi_union_coe : co ≡ coi ∪ coe.
Proof. apply ri_union_re. Qed.
Lemma fri_union_fre : fr ≡ fri ∪ fre.
Proof. apply ri_union_re. Qed.

Lemma ri_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r ∩ sb ⊆ ⦗d1⦘ ⨾ r ∩ sb ⨾ ⦗d2⦘.
Proof. rewrite DOM at 1; basic_solver. Qed.
Lemma re_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r \ sb ⊆ ⦗d1⦘ ⨾ (r \ sb) ⨾ ⦗d2⦘.
Proof. rewrite DOM at 1; basic_solver. Qed.

Lemma wf_rfiE WF: rfi ≡ ⦗E⦘ ⨾ rfi ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_rfE WF)). Qed.
Lemma wf_coiE WF: coi ≡ ⦗E⦘ ⨾ coi ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_coE WF)). Qed.
Lemma wf_friE WF: fri ≡ ⦗E⦘ ⨾ fri ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_frE WF)). Qed.
Lemma wf_rfeE WF: rfe ≡ ⦗E⦘ ⨾ rfe ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_rfE WF)). Qed.
Lemma wf_coeE WF: coe ≡ ⦗E⦘ ⨾ coe ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_coE WF)). Qed.
Lemma wf_freE WF: fre ≡ ⦗E⦘ ⨾ fre ⨾ ⦗E⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_frE WF)). Qed.
Lemma wf_rfiD WF : rfi ≡ ⦗W⦘ ⨾ rfi ⨾ ⦗R⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_rfD WF)). Qed.
Lemma wf_coiD WF : coi ≡ ⦗W⦘ ⨾ coi ⨾ ⦗W⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_coD WF)). Qed.
Lemma wf_friD WF : fri ≡ ⦗R⦘ ⨾ fri ⨾ ⦗W⦘.
Proof. split; [|basic_solver]. apply (ri_dom (wf_frD WF)). Qed.
Lemma wf_rfeD WF : rfe ≡ ⦗W⦘ ⨾ rfe ⨾ ⦗R⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_rfD WF)). Qed.
Lemma wf_coeD WF : coe ≡ ⦗W⦘ ⨾ coe ⨾ ⦗W⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_coD WF)). Qed.
Lemma wf_freD WF : fre ≡ ⦗R⦘ ⨾ fre ⨾ ⦗W⦘.
Proof. split; [|basic_solver]. apply (re_dom (wf_frD WF)). Qed.

(******************************************************************************)
(** ** properties of external/internal relations *)
(******************************************************************************)

Lemma seq_ii r1 r2 r3 (A: r1 ⨾ r2 ⊆ r3): r1 ∩ sb ⨾ r2 ∩ sb ⊆ r3 ∩ sb.
Proof.
generalize sb_trans.
unfolder in *; basic_solver 21.
Qed.

Lemma re_ri WF  r r' (IRR: irreflexive r)  (IRR2: irreflexive (r ⨾ sb))
  (N: r ⊆ r ⨾  ⦗ fun x => ~ is_init x ⦘): (r \ sb) ⨾ (r' ∩ sb) ⊆ r ⨾  r' \ sb.
Proof.
rewrite N at 1.
unfolder; ins; desf; splits; eauto.
intro.
eapply sb_semi_total_r with (x:=y) (y:=x) in H1; eauto.
by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.

Lemma ri_re WF  r r' (IRR: irreflexive r')  (IRR2: irreflexive (r' ⨾ sb)): 
 ⦗ fun x => ~ is_init x ⦘ ⨾ (r ∩ sb) ⨾ (r' \ sb) ⊆ r ⨾  r' \ sb.
Proof.
unfolder; ins; desf; splits; eauto.
intro.
eapply sb_semi_total_l with (x:=x) (y:=z) (z:=y) in H4; eauto.
by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.

Lemma rfi_in_sbloc WF : rf ∩ sb ⊆ restr_eq_rel loc sb.
Proof. rewrite wf_rfl; basic_solver 12. Qed.
Lemma coi_in_sbloc WF : co ∩ sb ⊆ restr_eq_rel loc sb.
Proof. rewrite wf_col; basic_solver 12. Qed.
Lemma fri_in_sbloc WF : fr ∩ sb ⊆ restr_eq_rel loc sb.
Proof. rewrite (loceq_same_loc (loceq_fr WF)).
unfolder; unfold Events.same_loc in *.
ins; desf; splits; eauto; congruence.
Qed.
Lemma rfi_in_sbloc' WF : rfi ⊆ sb ∩ same_loc.
Proof. generalize (wf_rfl WF); unfold rfi; basic_solver 12. Qed.
Lemma coi_in_sbloc' WF : coi ⊆ sb ∩ same_loc.
Proof. generalize (wf_col WF); unfold coi; basic_solver 12. Qed.
Lemma fri_in_sbloc' WF : fri ⊆ sb ∩ same_loc.
Proof. generalize (wf_frl WF); unfold fri; basic_solver 12. Qed.

Lemma rf_rmw_sb_minus_sb WF: (rf ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘) \ sb ⊆ rfe ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘.
Proof.
rewrite (seq_minus_transitive sb_trans).
unionL; [by unfold rfe; basic_solver 12|].
rewrite (rmw_in_sb WF) at 1.
arewrite (sb ⨾ sb^? ⨾ ⦗W⦘ ⊆ sb) by generalize sb_trans; basic_solver 21.
relsf.
Qed.

Lemma rf_rmw_sb_rt_rf WF: ((rf ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊ ⨾ rf) \ sb ⊆ sb^? ⨾ rfe ⨾ (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ rf)＊.
Proof.
rewrite rtE; relsf.
rewrite rtE, minus_union_l.
relsf; unionL; [by unfold rfe; basic_solver 12|].
rewrite (seq_minus_transitive sb_trans).
unionL; [|by unfold rfe; basic_solver 12].
unionR right.
rewrite (ct_minus_transitive sb_trans).
arewrite ((rf ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘) ∩ sb ⊆ sb).
generalize sb_trans; ins; relsf.
rewrite (rf_rmw_sb_minus_sb WF).
rewrite !seqA.
arewrite (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw ⨾ sb^? ⨾ ⦗W⦘)＊ ⨾ rf ⊆ (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ rf )⁺); [|done].
rewrite rtE; relsf; unionL; [by econs|].
rewrite ct_seq_swap, !seqA.
rewrite ct_begin at 2.
by rewrite inclusion_t_rt, !seqA.
Qed.

Lemma rmw_rf_ct WF : (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ rf)⁺ ⊆ (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)⁺ ⨾ rf.
Proof.
apply inclusion_t_ind_left.
- hahn_frame; vauto.
- rewrite ct_begin; hahn_frame; relsf.
  arewrite (rfe ⊆ rf) at 2.
  seq_rewrite (rf_rf WF).
  relsf.
  rewrite rfi_union_rfe; relsf; unionL.
  * arewrite (rfi ⊆ sb).
    rewrite (rmw_in_sb WF) at 2.
    arewrite (sb^? ⨾ ⦗W⦘ ⨾ sb ⨾ sb ⨾ sb^? ⊆ sb^?).
    generalize sb_trans; basic_solver 21.
    basic_solver 21.
  * rewrite rt_begin at 2.
    rewrite rt_begin at 2.
    basic_solver 42.
Qed.

Lemma rmw_rf_rt_1 WF : (rmw ⨾ sb^? ⨾ ⦗W⦘ ⨾ rf)＊ ⊆ (rmw ⨾ sb^? ⨾ ⦗W⦘ ∪ rfe)＊ ⨾ rfi^?.
Proof.
rewrite rtE; unionL; [basic_solver 12|].
rewrite (rmw_rf_ct WF).
rewrite rfi_union_rfe; relsf.
rewrite inclusion_t_rt.
relsf; unionL.
basic_solver 12.
rewrite rt_end at 2; basic_solver 12.
Qed.

(******************************************************************************)
(** ** detour *)
(******************************************************************************)

Definition detour := (coe ⨾ rfe) ∩ sb.

Lemma wf_detourE WF: detour ≡ ⦗E⦘ ⨾ detour ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold detour.
sin_rewrite (wf_coeE WF).
sin_rewrite (wf_rfeE WF).
basic_solver 42.
Qed.

Lemma wf_detourD WF: detour ≡ ⦗W⦘ ⨾ detour ⨾ ⦗R⦘.
Proof.
split; [|basic_solver].
unfold detour.
sin_rewrite (wf_coeD WF).
sin_rewrite (wf_rfeD WF).
basic_solver 42.
Qed.

Lemma detour_fr_in_co WF: detour ⨾ fr ⊆ co.
Proof.
unfold detour, coe, rfe.
generalize (rf_fr WF) (co_trans WF).
basic_solver 42.
Qed.

Lemma detour_transp_rfi WF: detour ⨾ rfi^{-1} ⊆ ∅₂.
Proof.
unfold detour, rfe, rfi.
unfolder; ins; desf.
assert (y=z0); subst; auto.
eapply WF; basic_solver.
Qed.

Lemma detour_in_sb : detour ⊆ sb.
Proof. unfold detour; basic_solver. Qed.

Lemma detour_to_codom_rfe WF: detour ⊆ detour ⨾ ⦗ codom_rel rfe ⦘.
Proof.
unfold detour, rfe, rfi.
unfolder; ins; desf; eauto 20.
Qed.

(******************************************************************************)
(** ** exclusive reads/writes *)
(******************************************************************************)

Definition W_ex := codom_rel rmw.


Lemma W_ex_in_W WF : W_ex ⊆₁ W.
Proof.
unfold W_ex; rewrite (dom_r (wf_rmwD WF)); basic_solver.
Qed.

Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

  Lemma W_ex_acq_in_W WF : W_ex_acq ⊆₁ W.
  Proof.
    rewrite (W_ex_in_W WF); basic_solver.
  Qed.

Lemma rmw_W_ex : rmw ⊆ rmw ⨾ ⦗W_ex⦘.
Proof.
unfold W_ex; basic_solver.
Qed.


(******************************************************************************)
(** ** rf ⨾ rmw *)
(******************************************************************************)

Lemma wf_rfrmwE WF: rf ⨾ rmw ≡ ⦗ E ⦘ ⨾ (rf ⨾ rmw) ⨾ ⦗ E ⦘.
Proof.
split; [|basic_solver].
rewrite WF.(wf_rfE) at 1. 
rewrite WF.(wf_rmwE) at 1.
basic_solver.
Qed.

Lemma wf_rfrmwD WF: rf ⨾ rmw ≡ ⦗ W ⦘ ⨾ (rf ⨾ rmw) ⨾ ⦗ W ⦘.
Proof.
split; [|basic_solver].
rewrite WF.(wf_rfD) at 1. 
rewrite WF.(wf_rmwD) at 1.
basic_solver.
Qed.

Lemma wf_rfrmwl WF: rf ⨾ rmw ⊆ same_loc. 
Proof.
rewrite WF.(wf_rfl), WF.(wf_rmwl).
generalize same_loc_trans; basic_solver.
Qed.

Lemma wf_rfrmwf WF: functional (rf ⨾ rmw)⁻¹.
Proof.
hahn_rewrite transp_seq.
by apply functional_seq; [apply wf_rmw_invf|apply WF].
Qed.

Lemma rt_rf_rmw : (rf ⨾ rmw)＊ ⊆ (rfi ⨾ rmw)＊ ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)＊.
Proof.
eapply rt_ind_left with (P:=fun r=> r); eauto with hahn.
basic_solver 12.
intros k H.
rewrite !seqA, H.
rewrite rfi_union_rfe; relsf; unionL.
- rewrite rt_begin at 3.
  basic_solver 21.
- rewrite (rt_begin (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)＊)) at 2.
  basic_solver 21.
Qed.

End Execution.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

Hint Unfold rfe coe fre rfi coi fri : ie_unfolderDb.
Tactic Notation "ie_unfolder" :=  repeat autounfold with ie_unfolderDb in *.
