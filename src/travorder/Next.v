From hahn Require Import Hahn.

From imm Require Import AuxDef Events Execution.
From imm Require Import Execution_eco imm_s_hb imm_s imm_bob.
From imm Require Import imm_s_ppo CombRelations.
From imm Require Import imm_s_rfppo.
From imm Require Import FinExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.
From imm Require Import SimClosure.
Require Import TlsEventSets.
Require Import EventsTraversalOrder.

Section Next.
  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'eco'" := (eco G).

  Notation "'bob'" := (bob G).
  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).
  Notation "'release'" := (release G).
  Notation "'sw'" := (sw G).
  Notation "'hb'" := (hb G).

  Notation "'ar'" := (ar G sc).

  Notation "'urr'" := (urr G sc).
  Notation "'c_acq'" := (c_acq G sc).
  Notation "'c_cur'" := (c_cur G sc).
  Notation "'c_rel'" := (c_rel G sc).
  Notation "'t_acq'" := (t_acq G sc).
  Notation "'t_cur'" := (t_cur G sc).
  Notation "'t_rel'" := (t_rel G sc).
  Notation "'S_tm'" := (S_tm G).
  Notation "'S_tmr'" := (S_tmr G).
  Notation "'msg_rel'" := (msg_rel G sc).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := (acts_set G).
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

Definition next C := E ∩₁ dom_cond sb C ∩₁ set_compl C.
  
Lemma next_helper C a 
  (IC : is_init ∩₁ E ⊆₁ C)
  (CE : C ⊆₁ E)
  (CC : C ⊆₁ dom_cond sb C)
  (NEXT: next C a) :
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


Lemma next_helper' a T
      (TCOH : tls_coherent G T)
      (ICOH : iord_coherent G sc T)
  (NEXT: next (covered T) a) :
  ⦗Tid_ (tid a) ∪₁ Init⦘ ⨾ ⦗covered T⦘ ≡ ⦗dom_rel (sb ⨾ ⦗eq a⦘)⦘.
Proof using WF IMMCON.
  apply next_helper; auto using init_covered, coveredE.
  apply dom_rel_to_cond. eapply dom_sb_covered; eauto.  
Qed.

  Lemma next_n_init T e
        (NEXT : next (covered T) e)
        (TCOH: tls_coherent G T):
    ~ Init e.
  Proof using.
    intros HH. apply NEXT.
    eapply init_covered; eauto. split; auto.
    apply NEXT.
  Qed.

  Lemma issuable_next_w T 
    (TCOH: tls_coherent G T)
    (ICOH: iord_coherent G sc T):
    W ∩₁ next (covered T) ⊆₁ issuable G sc T.
  Proof using WF IMMCON.
    unfold issuable, next.
    apply set_subset_inter_r; split.
    { basic_solver 10. }
    rewrite !set_interA.
    arewrite (dom_cond sb (covered T) ∩₁ set_compl (covered T) ⊆₁ dom_cond sb (covered T)).
    { basic_solver 10. }
    rewrite !dom_cond_alt. rewrite <- !set_bunion_inter_compat_l.
    apply set_subset_bunion_l. ins.
    rewrite <- !set_bunion_inter_compat_r. rewrite set_collect_bunion.
    apply set_subset_bunion_r with (a := mkTL ta_issue x).
    2: { unfolder. ins. desc. eexists. splits; vauto. }

    filter_iord_seq.
    rewrite <- id_inter, set_inter_absorb_l; [| basic_solver].
    rewrite inclusion_restr. rewrite dom_union. apply set_subset_union_l. split.
    { assert (T ∩₁ action ↓₁ eq ta_cover ⊆₁ T) as <-; [basic_solver| ].
      apply dom_rel_collect_event2; [basic_solver| ].
      rewrite <- COND. rewrite fwbob_in_sb. basic_solver. } 
    assert (T ∩₁ action ↓₁ eq ta_issue ⊆₁ T) as <-; [basic_solver| ].
    apply dom_rel_collect_event2; [basic_solver| ].
    rewrite event_collect_eq. 
    
    rewrite ct_end, !seqA.
    arewrite (ar ∪ rf ⨾ ppo ∩ same_loc ⊆ (ar ∪ sb)^? ⨾ ar) at 2.
    { apply inclusion_union_l; [basic_solver|].
      rewrite rfi_union_rfe. rewrite rfe_in_ar, ppo_in_ar.
      arewrite (rfi ⊆ sb). basic_solver 10. }
    arewrite (ar ⨾ ⦗W⦘ ⊆ sb).
    { unfold imm_s.ar.
      rewrite !seq_union_l. rewrite (ar_int_in_sb WF).
      rewrite wf_scD with (sc:=sc); [|by apply IMMCON].
      rewrite (wf_rfeD WF). type_solver. }    
    apply dom_rel_helper_in in COND. rewrite COND.
    arewrite ((ar ∪ sb)^? ⨾ ⦗covered T⦘ ⊆ ⦗covered T ∪₁ issued T⦘ ⨾ (ar ∪ sb)^? ⨾ ⦗covered T⦘).
    2: { etransitivity.
         2: apply ar_rf_ppo_loc_rt_CI_in_I; eauto.
         { basic_solver 20. }
         apply IMMCON. }
    apply dom_rel_helper_in.
    rewrite crE, !seq_union_l, !dom_union, seq_id_l.
    unionL; [basic_solver| |].
    2: { rewrite dom_sb_covered; basic_solver. }
    apply ar_C_in_CI; eauto. apply IMMCON.
  Qed. 

End Next. 

Global Add Parametric Morphism : next with signature
       eq ==> (@set_equiv actid) ==> (@set_equiv actid) as next_more. 
Proof using. ins. unfold next. rewrite H. basic_solver. Qed. 

