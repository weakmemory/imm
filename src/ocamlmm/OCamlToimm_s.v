(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section OCamlMM_TO_IMM_S.

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

Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ar).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Init'" := (fun a => is_true (is_init a)).

Hypothesis LocSameMode : forall l,
    << LM : Loc_ l \₁ Init  ⊆₁ Rlx \₁ Sc >> \/
    << LM : Loc_ l \₁ Init  ⊆₁ Sc >>.

Hypothesis Wsc_is_succ_RMW : W∩₁Sc ≡₁ codom_rel rmw.
Hypothesis RMW_always_sc  : rmw ≡ ⦗Sc⦘ ;; rmw ;; ⦗Sc⦘.

Hypothesis Wrlx_succs_Facqrel : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acq/Rel|> ;; immediate sb).
Hypothesis Rsc_succs_Facq : R∩₁Sc ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

Lemma rf_sb_on_SC_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ;; sb ⊆ hb.
Proof.
   arewrite (⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ⊆ sw).
   2: { rewrite sw_in_hb, sb_in_hb.
         (* error occurs without admit; in original proof it wasn't *)
        apply rewrite_trans; auto. admit. }
   arewrite (Sc ⊆₁ Rel) at 1 by mode_solver.
   arewrite (Sc ⊆₁ Acq)      by mode_solver.
   unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
   rewrite !seqA.
   hahn_frame.
   rewrite (dom_l WF.(wf_rfD)) at 1.
   basic_solver 40.
Admitted. (* due to error with 'focus' *)

Lemma co_immediates_closure_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  (immediate (⦗Sc⦘ ;; co ;; ⦗Sc⦘))⁺ ⊆ hb.
Proof.
  assert (transitive hb) as hb_is_transitive by apply hb_trans.  
  apply inclusion_t_ind; (* only show that single edge is in hb *)
    auto. (* ';': run auto on all subgoals *) (* ? only _sub_ goals ? *)
  (* prove that given relation belongs to a subset of hb *)
  arewrite (immediate (⦗Sc⦘ ;; co ;; ⦗Sc⦘) ⊆ ⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ;; sb).
  2: {apply (rf_sb_on_SC_in_hb WF IPC). }
  
  rewrite (dom_r WF.(wf_coD)).  (* ? why only right part of co is extended ? *)
  rewrite !seqA. (* ? exclamation ? *) (* use associativity *)
  rewrite <- id_inter.          (* intersect (why only last ?) *)
  rewrite Wsc_is_succ_RMW.      (* treat Wsc as codom of rmw *)
  intros w_cur w_next.                   (* ? where are they coming from ? *)
  intros T.
  destruct T as [w_cur_next_co w_next_succs_cur]. (* ? how 'immediate' is being destructed ? *)
  (* now the goal is to show rf;sb between cur and next *)
  apply seq_eqv_l in w_cur_next_co. destruct w_cur_next_co as [w_cur_is_SC w_cur_next_co].
  apply seq_eqv_r in w_cur_next_co. destruct w_cur_next_co as [w_cur_next_co w_next_by_rmw].
  (* ? implicit relation argument ? *)
  destruct w_next_by_rmw as [r_next rw_next_rmw].
  apply seq_eqv_l.
  split; (* subgoal is is_sc lab w_cur *)
    auto.
  assert (Sc r_next) as r_next_is_SC.    (* not used ?  *)
  { apply RMW_always_sc in rw_next_rmw. generalize rw_next_rmw. basic_solver. }

  assert (E r_next) as EZ.      (* ? why ever prove that events belong to graph ? *)
  { (* ? why E is introduced only at left ? *)
    apply (dom_l WF.(wf_rmwE)) in rw_next_rmw.
    generalize rw_next_rmw.
    basic_solver.               (* ? works only with goal like X->Y ? *)
  }
  assert (R r_next) as r_next_is_read.
  { apply (dom_l WF.(wf_rmwD)) in rw_next_rmw.
    generalize rw_next_rmw. type_solver. }

  (* goal: rf;SC;po between w_cur and w_next *)
  exists r_next.                (* ? where substitution is being done ? *)
  (* ? r_next is inserted between writes ? *)
  (* goal is transformed to rf to r_next and po from r_next*)
  split.
  2: { apply seq_eqv_l. split; auto.
       apply rmw_in_sb; auto. }

  (* introduce the write that r_next reads from *)
  assert (exists v, rf v r_next) as [w_of_r_next RF].
  { apply IPC. split; auto. }
  assert (E w_of_r_next) as EV. 
  { apply WF.(wf_rfE) in RF. generalize RF. basic_solver. }
  assert (W w_of_r_next) as w_of_r_next_is_write. 
  { apply WF.(wf_rfD) in RF. generalize RF. basic_solver. }

  destruct (classic (w_cur = w_of_r_next)) as [|NEQ]; desf. 
  (* ? Was original case processed ? *)
  (* now show contradiction with w_cur != w_of_r_next *)
  
  set (w_of_r_next_at_l := w_of_r_next_is_write).
  apply is_w_loc in w_of_r_next_at_l. desf. 
  
  assert (loc r_next = Some l) as r_next_at_l.
  { rewrite <- w_of_r_next_at_l. symmetry.
    apply wf_rfl; auto. }       (* ? when to use ; instead of . ? *)

  assert (writes_co: co w_of_r_next w_cur \/ co w_cur w_of_r_next).
  {admit. }
  destruct writes_co as [w_of_r_next_co_before | w_of_r_next_co_after].
  (* ? unable to set 1:, 2: ? *)
  2: { (* w_cur before w_of_r_next *)
    (* cycle: hb_loc(@l), (co)^*, rf *)
    (* show hb_loc *)
    (* appeal to coherence *)
    unfold imm_psc_consistent in IPC. destruct IPC as [IMMcons _].
    unfold imm_consistent in IMMcons.
    destruct IMMcons as [_ [_ [_ [Coh _]]]].
    (* rewrite coherence_expanded_eq in Coh.  *)  (* ? cannot find it ?*)
    (* assert (Coh_exp: coherent_expanded G).  *) (* ? also fails ?*)
    assert (irr_co_rf_hb: irreflexive (co ;; rf ;; hb)).
    {admit. }
    assert (irr_co_hb: irreflexive (co ;; hb)).
    {admit. }
    (* w_of_r_next is either w_next or after it *)
    destruct (classic (w_of_r_next = w_next))
      as [w_of_r_next_same | w_of_r_next_other](* ; auto.  *). (* ? *)
    2: { assert (w_of_r_next_co_after_w_next: co w_next w_of_r_next).
         {admit. }    (* ? use classic again or call solver ? *)
         (* now we can show a cycle with co *)
         admit. 
    }
    1: {
      (* here we can show a cycle without co *)
      admit. 
    }
  }
  1: {    
    (* w_of_r_next is before w_cur - it contradicts RMW atomicity *)
    unfold imm_psc_consistent in IPC. destruct IPC as [IMMcons _].
    unfold imm_consistent in IMMcons.
    destruct IMMcons as [_ [_ [_ [_ [_ RMW_ATOM]]]]].
    unfold rmw_atomicity in RMW_ATOM.
    assert (r_next_fr_w_cur: fr r_next w_cur).
    { generalize w_of_r_next_co_before. generalize RF.
      (* basic_solver 100. *) admit. 
    }    
    assert (w_cur_breaks_atomicity: ((fr ;; co) r_next w_next) = rmw r_next w_next). 
    { admit. }
    admit. 
  }  
  (* done  *)
  
  (*  *)
  (* prev proof rest below *)
  destruct (classic (Init w_of_r_next)) as [INIT|NINIT].
  { admit. }
  (* assume that w_of_r_next is not an initializer *)
  assert (Sc w_of_r_next) as SCV.
  { specialize (LocSameMode l).
    destruct LocSameMode as [CC|CC].
    2: { apply CC. split; auto. }
    exfalso.
    assert (~ is_init r_next) as NINITZ.
    { eapply read_or_fence_is_not_init; eauto. }
    assert ((Loc_ l \₁ Init) r_next) as DD.
    { split; auto. }
   apply CC in DD.
   destruct DD. desf. }

  assert (codom_rel rmw w_of_r_next) as RMWV.
  { apply Wsc_is_succ_RMW. split; auto. }

  assert (E w_cur) as EX.
  { apply (dom_l WF.(wf_coE)) in w_cur_next_co.
    generalize w_cur_next_co. basic_solver. }
  assert (W w_cur) as WX.
  { apply (dom_l WF.(wf_coD)) in w_cur_next_co.
    generalize w_cur_next_co. basic_solver. }
  
  eapply wf_co_total in NEQ; eauto.
  3: { split; [split|]; auto. }
  2: { split; [split|]; auto.
       rewrite w_of_r_next_at_l, <- r_next_at_l.
       arewrite (loc r_next = loc w_next) by (by apply WF.(wf_rmwl)).
       apply WF.(wf_col); auto. }

  cdes IPC. cdes IC.
  assert (sc_per_loc G) as SCPL by (by apply coherence_sc_per_loc).
  
  exfalso.
  destruct NEQ as [NEQ|NEQ].
  2: { eapply atomicity_alt; eauto.
       split; eauto.
       do 2 (eexists; split; eauto). }
  apply w_next_succs_cur with (c:=w_of_r_next).
  { apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto. }
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  2: { eexists; eauto. }
  apply rf_rmw_in_co; auto.
  eexists. eauto.
Admitted.


Lemma co_sc_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  <|Sc|> ;; co ;; <|Sc|> ⊆ hb.
Proof.
  (* replace co chain with its immediate edges  *)
  rewrite fsupp_imm_t with (r:=⦗Sc⦘ ;; co ;; ⦗Sc⦘).
  (* prove premises to this rewrite *)
  (* 4: co is transitive *)
  4: { generalize WF.(co_trans). (* ? just puts it into context ? *)
       basic_solver. }           (* ? auto: the proof is focused ?  *)
  (* 3: co is irreflexive; same as above *)
  3: { generalize WF.(co_irr). basic_solver. }
  (* 2: has finite amount of predecessors *)
  2: { (* ? replaces with more general hypothesis ? *)
       arewrite (⦗Sc⦘ ;; co ;; ⦗Sc⦘ ⊆ co) by basic_solver.
       rewrite WF.(wf_coE). unfold acts_set. (* ? fun+rel composition ? *)
       red.                     (* ??? *)
       ins.                     (* ~intros y *)
       (* current goal: there exists a finite set containing all co-precs of y *)
       eexists.                 (* ? '?findom' ? *)
       basic_solver. }

  (* prove initial statement with Sc;co;Sc replaced by immediates' closure *)
  (* ? why it's easier ? *)
  (* ? why we should specify exactly these arguments ? *)
  apply (co_immediates_closure_in_hb WF IPC).
Qed.
  
 
Lemma s_imm_consistentimplies_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  red. splits; auto.

  rewrite co_in_eco.
  2: rewrite fr_in_eco. 
  1,2: by arewrite (eco ⊆ eco^?); apply Cint.

Admitted.

End OCamlMM_TO_IMM_S.
