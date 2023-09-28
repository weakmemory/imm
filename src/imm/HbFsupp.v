Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import FairExecution.
Require Import ImmFair.
Require Import CombRelations.
Import ListNotations.
From imm Require Import imm_s.
From imm Require Import imm_s_hb.
Require Import FairExecution. 
Require Import FinThreads.

Section HbFsupp.
  Variable (G: execution) (sc: relation actid). 
  Hypothesis (WF: Wf G) (IMMCON: imm_consistent G sc).
  Hypothesis (FAIR: mem_fair G) (FSUPP_SC: fsupp sc).
  Hypothesis (TB: fin_threads G). 
  
  Lemma fsupp_rs : fsupp (⦗set_compl is_init⦘ ⨾ rs G).
  Proof using WF IMMCON FAIR.
    assert (sc_per_loc G) as SCPL.
    { apply coherence_sc_per_loc, IMMCON. }
    unfold imm_s_hb.rs.
    rewrite <- !seqA.
    apply fsupp_seq.
    2: { rewrite rf_rmw_in_co; auto.
         rewrite rt_of_trans; [| apply co_trans; auto].
         apply fsupp_cr. apply FAIR. }
    rewrite inclusion_seq_eqv_r, seqA, inclusion_seq_eqv_l with (dom := is_w _).
    rewrite inclusion_inter_l1. rewrite crE. relsf.
    apply fsupp_union; auto using fsupp_eqv, fsupp_sb. 
  Qed.

  Lemma fsupp_release : fsupp (release G).
  Proof using WF IMMCON FAIR. 
    rewrite no_release_from_init; auto. 
    unfold imm_s_hb.release.
    rewrite inclusion_seq_eqv_l with (dom := is_rel _).
    eapply fsupp_mori.
    2: { apply fsupp_seq with (r1 := ⦗set_compl is_init⦘ ⨾ (sb G)^?).
         2: { apply fsupp_rs. }
         rewrite crE. relsf. apply fsupp_union; auto using fsupp_sb, fsupp_eqv. }
    red. rewrite no_sb_to_init at 1. basic_solver 10. 
  Qed. 
    
  Lemma fsupp_sw : fsupp (sw G).
  Proof using WF IMMCON FAIR.
    unfold imm_s_hb.sw.
    rewrite (no_rf_to_init WF).
    rewrite !seqA. rewrite <- seqA with (r2 := rf G). 
    apply fsupp_seq.
    2: { rewrite !inclusion_seq_eqv_r.
         rewrite crE. relsf. apply fsupp_union; auto using fsupp_sb, fsupp_eqv. }
    apply fsupp_seq; auto using fsupp_rf, fsupp_release.
  Qed.  

  Lemma fsupp_hb : fsupp (⦗set_compl is_init⦘ ⨾ hb G).
  Proof using TB WF IMMCON FAIR.
    rewrite (dom_l (wf_hbE WF)), <- !seqA.
    rewrite <- id_inter, set_interC, <- set_minusE.
    unfold imm_s_hb.hb.
    rewrite clos_trans_domb_l_strong.
    2: { rewrite no_sb_to_init, no_sw_to_init, wf_sbE, wf_swE; basic_solver. }
    rewrite inclusion_seq_eqv_r. 
    arewrite (acts_set G \₁ is_init ⊆₁ set_compl is_init); [basic_solver| ]. 
    rewrite seq_union_r.
    eapply fsupp_ct with (s := acts_set G \₁ is_init), fsupp_union; ins; eauto. 
    { rewrite 2!inclusion_seq_eqv_l.
      cdes IMMCON. red in Cint. 
      generalize Cint. unfold acyclic, hb. basic_solver 10. }
    { rewrite (dom_l (@wf_sbE G)), (dom_l (wf_swE WF)); basic_solver 10. }
    { rewrite <- inclusion_union_r1.
      eapply (@has_finite_antichains_sb G); eauto. apply WF. }
    { apply fsupp_sb; auto. }
    eapply fsupp_mori; [| apply fsupp_sw]. red. basic_solver 10. 
  Qed.

  Lemma fsupp_furr:
    fsupp (⦗set_compl is_init⦘ ⨾ furr G sc).
  Proof using WF IMMCON FSUPP_SC TB FAIR.
    assert (wf_sc G sc) as WFSC by (apply IMMCON). 
    rewrite furr_alt; auto.
    rewrite !crE, !seq_union_l, !seq_union_r.
    rewrite !seq_id_l, !seq_id_r.
    arewrite (hb G ⨾ hb G ⊆ hb G).
    rewrite <- !seqA.
    arewrite ((⦗set_compl (is_init)⦘ ;; ⦗is_w (lab G)⦘) ⨾ rf G ⊆ rf G) by basic_solver 10.
    assert (⦗is_w (lab G)⦘ ⨾ sc ⊆ ∅₂) as AA.
    { rewrite (wf_scD WFSC); type_solver. }
    arewrite (⦗is_w (lab G)⦘ ⨾ sc ⊆ ∅₂); auto.
    arewrite (⦗set_compl (is_init)⦘ ;; ⦗is_w (lab G)⦘ ⨾ sc ⊆ ∅₂).
    { rewrite AA. basic_solver. }
    rewrite <- !seqA.
    arewrite (rf G ⨾ sc ⊆ ∅₂).
    { rewrite (wf_scD WFSC), wf_rfD; auto. type_solver. }
    rewrite seq_false_r, seq_false_l, union_false_l, union_false_r.
    rewrite <- !seqA.
    arewrite ((⦗set_compl is_init⦘ ⨾ ⦗is_w (lab G)⦘) ⨾ hb G ⊆ ⦗set_compl (is_init)⦘ ;; hb G)
      by basic_solver 10.
    assert (fsupp (rf G ⨾ hb G)) as CC.
    { rewrite no_rf_to_init, seqA; auto.
      apply fsupp_seq; auto using fsupp_hb, fsupp_rf. }
    assert (fsupp (sc ⨾ hb G)) as DD.
    { rewrite (no_sc_to_init WF WFSC). rewrite seqA; auto.      
      apply fsupp_seq; auto using fsupp_hb. }
    rewrite <- id_inter.
    repeat apply fsupp_union; try by auto using fsupp_rf, fsupp_hb, fsupp_eqv. 
    all: try rewrite <- seqA.
    all: apply fsupp_seq; auto using fsupp_rf, fsupp_hb, fsupp_eqv.
  Qed.
  
End HbFsupp. 
