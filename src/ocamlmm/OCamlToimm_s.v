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

Hypothesis LocSameMode': forall l, (forall e, E e -> loc e = Some l -> ~ is_init e -> is_sc lab e) \/ (forall e, E e -> loc e = Some l  ->  ~ is_init e -> ~ is_sc lab e). 

Hypothesis Wsc_is_succ_RMW : W∩₁Sc ≡₁ codom_rel rmw.
Hypothesis RMW_always_sc  : rmw ≡ ⦗Sc⦘ ;; rmw ;; ⦗Sc⦘.

Hypothesis Wrlx_succs_Facqrel : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acq/Rel|> ;; immediate sb).
Hypothesis Rsc_succs_Facq : R∩₁Sc ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

(* Lemma rf_same_sc_type  (WF : Wf G) sc *)
(*       (IPC : imm_s.imm_psc_consistent G sc): *)
(*   forall w r, rf w r -> E w -> E r -> (is_sc lab w <-> is_sc lab r). *)
(* Proof. *)
(*   intros w r H. *)
(*   split. *)
(*   - intros H'. edestruct LocSameMode'; auto.  *)
(*     + auto.  *)
                                        
  


Lemma rf_sb_on_SC_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ;; sb ⊆ hb.
Proof.
  assert (transitive hb) as hb_is_transitive by apply hb_trans.  
  arewrite (⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ⊆ sw).
  2: { rewrite sw_in_hb, sb_in_hb.
       apply rewrite_trans; auto. }
  arewrite (Sc ⊆₁ Rel) at 1 by mode_solver.
  arewrite (Sc ⊆₁ Acq)      by mode_solver.
  unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.  
  rewrite !seqA.
  hahn_frame.
  rewrite (dom_l WF.(wf_rfD)) at 1.
  basic_solver 40.
Qed.

Lemma co_immediates_closure_in_hb (WF : Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  (immediate (⦗Sc⦘ ;; co ;; ⦗Sc⦘))⁺ ⊆ hb.
Proof.
  assert (transitive hb) as hb_is_transitive by apply hb_trans.  
  apply inclusion_t_ind; (* only show that single edge is in hb *)
    auto. (* ';': run auto on all subgoals *) (* ? only _sub_ goals ? *)
  (* prove that given relation belongs to a subset of hb *)
  arewrite (immediate (⦗Sc⦘ ;; co ;; ⦗Sc⦘) ⊆ ⦗Sc⦘ ;; rf ;; ⦗Sc⦘ ;; sb).
  2: { eapply rf_sb_on_SC_in_hb; eauto. }
  
  (* rewrite (dom_r WF.(wf_coD)).  (* ? why only right part of co is extended ? *) *)
  (* rewrite !seqA. (* ? exclamation ? *) (* use associativity *) *)
  (* rewrite <- id_inter.          (* intersect (why only last ?) *) *)
  (* rewrite Wsc_is_succ_RMW.      (* treat Wsc as codom of rmw *) *)

  (* w1 and w2 are co-immediate writes, r2 is w2-rmw-corresponding read  *)
  (* we want to show "rf w1 r2" *)
  (* later, we'll show a contradiction for "rf w' r2", where w' != w1 *)  
  intros w1 w2 T.
  destruct T as [w1_co_w2 w2_succs_w1]. (* ? how 'immediate' is being destructed ? *)
  apply seq_eqv_lr in w1_co_w2. destruct w1_co_w2 as [w1_SC [w1_co_w2 w2_SC]].
  assert (w1_w2_writes: W w1 /\ W w2).
  {apply (WF.(wf_coD)) in w1_co_w2. generalize w1_co_w2. basic_solver. } 
  assert (w1_w2_events: E w1 /\ E w2).
  {apply (WF.(wf_coE)) in w1_co_w2. generalize w1_co_w2. basic_solver. }
  destruct w1_w2_writes as [w1_W w2_W]. destruct w1_w2_events as [w1_E w2_E].
  (* now the goal is to show rf;sb between cur and next *)
  (* apply seq_eqv_r in w1_co_w2. destruct w1_co_w2 as [w1_co_w2 w2_by_rmw]. *)
  assert (w2_by_rmw: codom_rel rmw w2).
  {apply Wsc_is_succ_RMW. basic_solver. }

  (* ? implicit relation argument ? *)
  destruct w2_by_rmw as [r2 rw2_rmw].
  apply seq_eqv_l.
  split; (* subgoal is is_sc lab w1 *)
    auto.
  assert (Sc r2) as r2_is_SC.    (* not used ?  *)
  { apply RMW_always_sc in rw2_rmw. generalize rw2_rmw. basic_solver. }

  assert (E r2) as EZ.      (* ? why ever prove that events belong to graph ? *)
  { apply (dom_l WF.(wf_rmwE)) in rw2_rmw.
    generalize rw2_rmw.
    basic_solver. }
  assert (R r2) as r2_is_read.
  { apply (dom_l WF.(wf_rmwD)) in rw2_rmw.
    generalize rw2_rmw. type_solver. }
  exists r2.
  split.
  2: { apply seq_eqv_l. split; auto.
       apply rmw_in_sb; auto. }

  (* introduce the write that r2 reads from *)
  assert (exists v, rf v r2) as [w' RF].
  { apply IPC. split; auto. }
  assert (E w') as w'_E. 
  { apply WF.(wf_rfE) in RF. generalize RF. basic_solver. }
  assert (W w') as w'_W. 
  { apply WF.(wf_rfD) in RF. generalize RF. basic_solver. }
  (* assert (Sc w') as w'_SC. *)
  (* { apply WF.(wf_rfD) in RF. generalize RF.  } *)

  destruct (classic (w1 = w')) as [|NEQ]; desf. (* eq processed by desf *)
  
  (* now show contradiction with w1 != w' *)
  set (w'_at_l := w'_W).
  apply is_w_loc in w'_at_l. desf. 
  
  assert (loc r2 = Some l) as r2_at_l.
  { rewrite <- w'_at_l. symmetry.
    apply wf_rfl; auto. }       (* ? when to use ; instead of . ? *)

  assert (writes_co: co w' w1 \/ co w1 w').
  (* proposed proof is MUCH shorter, should understand where simplification is done *)
  { (* ? see wf_co_total def: where is the second condition needed by is_total ? *)
    eapply WF.(wf_co_total). (* ; eauto.  *)
    (* prove that w' satisfies condition in wf_co_total *)
    (* namely, it is a graph event, a write and accesses some location *)
    - split.                    (* first two *)
      + split; auto.            (* split further *)
      + apply w'_at_l. (* give a witness for location *)
    - split.                    (* same *)
      + split; auto. 
      + apply (WF.(wf_col)) in w1_co_w2. (* ? check how \subset is rewritten ? *)
        rewrite <- r2_at_l.
        (* ? cannot unfold same_loc ? *)
        apply (WF.(wf_rmwl)) in rw2_rmw.
        apply same_loc_sym in rw2_rmw. 
        apply (same_loc_trans w1_co_w2 rw2_rmw). 
    - auto. 
  }

  cdes IPC. cdes IC.
  destruct writes_co as [w'_co_w1 | w1_co_w'].
  2: { (* w1 before w', so w' is either w2 or its co-child *)
    unfold coherence in Cint. unfold irreflexive in Cint.
    (* unfold Execution_eco.eco in Cint. *)
    exfalso. 
    assert (r2_cycle: (hb ⨾ eco^?) r2 r2).
    {red. unfold Execution_eco.eco.  exists w2.
     split.
     { 
       (* ? how to easily get plain sb from it ? *)
       (* unfold Relations.clos_trans. *)
       (* ? incorrect: rewrite (HahnRelationsBasic.immediate Execution.sb) in rw2_rmw.  ? *)
       assert (rmw_hb: rmw <<= hb).
       {unfold imm_s_hb.hb. rewrite WF.(wf_rmwi).
        apply WF.(wf_rmwi) in rw2_rmw.
        rewrite <- (inclusion_union_r1) with (r:=sb) (r':=sw).
        basic_solver. 
       }
       basic_solver. 
     }
     red. right. red. left.
     (* unfold union.  *)
     assert (co_opt_rf_in_eco: (co^? ;; rf) <<= (rf ∪ co ⨾ rf^?)).
     {basic_solver 50. }
     assert (w'_geq_w2: co^? w2 w').
     { destruct (classic (is_init w')) as [w'_INIT | w'_NINIT].
       - exfalso. apply no_co_to_init in w1_co_w'; auto.
         + apply seq_eqv_r in w1_co_w'. destruct w1_co_w'. auto.
         + apply coherence_sc_per_loc. auto.
       - assert (w'_SC: is_sc lab w').
         {admit. }
         exfalso. 
         apply w2_succs_w1 with (c:=w').
         all: apply seq_eqv_lr; split; auto.
         split; auto. 
         destruct (classic (w2 = w')) as [w'_eq_w2 | w'_neq_w2].
         + exfalso. apply Cint with (x:=r2).
           red. exists w2. split.
           * apply WF.(wf_rmwi) in rw2_rmw.
             admit.
           * red. right. red. basic_solver.
         + assert (co': co w2 w' \/ co w' w2).
           {eapply WF.(wf_co_total); eauto.
            - split; auto. split; auto.
            - split. 
              + split; auto.
              + apply WF.(wf_col) in w1_co_w'. apply WF.(wf_col) in w1_co_w2.
                apply same_loc_sym in w1_co_w'. apply (same_loc_trans w1_co_w' w1_co_w2).             
           }
           destruct co'; admit. 
     }


     (* {destruct (classic (w2 = w')) as [w'_eq_w2 | w'_neq_w2]. *)
     (*  - basic_solver. *)
     (*  - unfold clos_refl. right. *)
     (*    assert (co': co w2 w' \/ co w' w2). *)
     (*    {eapply WF.(wf_co_total); eauto. *)
     (*     - split; auto. split; auto. *)
     (*     - split.  *)
     (*       + split; auto. *)
     (*       + apply WF.(wf_col) in w1_co_w'. apply WF.(wf_col) in w1_co_w2. *)
     (*         apply same_loc_sym in w1_co_w'. apply (same_loc_trans w1_co_w' w1_co_w2).              *)
     (*    }         *)
     (*    destruct co'. *)
     (*    + auto. *)
     (*    + destruct (classic (is_sc lab w')) as [w'_SC | w'_RLX]. *)
     (*      * exfalso. apply w2_succs_w1 with (c:=w'); basic_solver. *)
     (*      * exfalso. apply w2_succs_w1 with (c:=w'). *)
     (*        all: apply seq_eqv_lr; splits; auto. *)
     (*        apply no_co_to_init in w1_co_w'; auto. *)
     (*        ++ destruct (classic (is_init w')). *)
     (*           +++  *)
     (*        (* apply seq_eqv_r in w1_co_w'. *) *)
     (*        (* ++ admit. *) *)
     (*        (* all: auto. *) *)
            
               
     (* } *)
     apply (co_opt_rf_in_eco).
     exists w'. auto. 
    }
    apply Cint in r2_cycle. auto. 
  }

  (* w' is before w1 - it contradicts RMW atomicity *)
  exfalso.
  eapply atomicity_alt; eauto.
  { by apply coherence_sc_per_loc. }
  split; eauto.
  exists w1.
  split; auto.
  red. basic_solver.
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
  eapply co_immediates_closure_in_hb; eauto.
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
