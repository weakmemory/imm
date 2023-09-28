Require Import Lia.
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt. 
Require Import Events.
Require Import Execution.
Import ListNotations.
Require Import FinExecution.

Definition mem_fair (G: execution) := fsupp (co G) /\ fsupp (fr G). 

Section FairExecution.
  Variable G: execution.
  Hypothesis FAIR: mem_fair G.
  Hypothesis WF: Wf G. 

  Lemma co_imm:
    co G ≡ (immediate (co G))⁺.
  Proof using WF FAIR. apply fsupp_imm_t; apply WF || apply FAIR. Qed. 

  Lemma nS_imm_co_in_sb
        (S : actid -> Prop) w wnext
        (WW : is_w (lab G) w)
        (NSW : ~ S w)
        (NCOIMM : immediate ((co G) ⨾ ⦗S⦘) w wnext)
        (FOR_SPLIT : ⦗set_compl S⦘ ⨾ immediate (co G) ⊆ sb G) :
    sb G w wnext.
  Proof using WF FAIR.
    assert (transitive (co G)) as COTRANS.
    { apply (co_trans WF). }

    assert (S wnext /\ co G w wnext) as [ISSNEXT CONEXT].
    { generalize NCOIMM. basic_solver. }
    apply clos_trans_of_transitiveD; [apply sb_trans|].
    apply (inclusion_t_t FOR_SPLIT).
    eapply fsupp_imm_t in CONEXT; cycle 1.
    { apply FAIR. }
    { apply (co_irr WF). }
    { apply (co_trans WF). }
    apply t_rt_step in CONEXT. destruct CONEXT as [z [IMMS IMM]].
    apply t_rt_step. exists z; split; [|apply seq_eqv_l; split; [|done]].
    { apply rtE in IMMS. destruct IMMS as [IMMS|IMMS].
      { red in IMMS; desf. apply rt_refl. }
      assert (immediate ((co G) ⨾ ⦗S⦘) z wnext) as IMM'.
      { red; split; [apply seq_eqv_r; split; auto|].
        { (* TODO: is the last tactic needed? *)
          apply clos_trans_immediate1; auto; try by apply ct_step. }
        ins. eapply NCOIMM; [|by apply R2].
        apply seq_eqv_r in R1; destruct R1 as [R1 R3].
        apply seq_eqv_r; split; auto.
        eapply (co_trans WF); [|by apply R1].
        apply clos_trans_immediate1; auto. }
      clear IMM.
      induction IMMS.
      { apply rt_step. apply seq_eqv_l; split; auto. }
      assert (co G y wnext) as YNEXT.
      { apply clos_trans_immediate1; auto.
        eapply transitive_ct; [by apply IMMS2|].
        eapply same_relation_exp.
        { symmetry. apply fsupp_imm_t; apply FAIR || apply WF. }
        unfolder in IMM'. basic_solver. }
      assert (immediate ((co G) ⨾ ⦗S⦘) y wnext) as YNEXTIMM.
      { red; split; [by apply seq_eqv_r; split|].
        ins. eapply NCOIMM; [|by apply R2].
        apply seq_eqv_r in R1; destruct R1 as [R1 R3].
        apply seq_eqv_r; split; auto.
        eapply (co_trans WF); [|by apply R1].
        apply clos_trans_immediate1; auto. }
      eapply rt_trans.
      { by apply IHIMMS1. }
      apply IHIMMS2; auto.
      { apply (wf_coD WF) in YNEXT.
        apply seq_eqv_l in YNEXT; desf. }
      intros NISS. eapply NCOIMM; apply seq_eqv_r; split; auto.
      2: by apply NISS.
      2: done.
      apply clos_trans_immediate1; auto. }
    intros HH. apply rtE in IMMS; destruct IMMS as [IMSS|IMMS].
    { red in IMSS; desf. }
    eapply NCOIMM; apply seq_eqv_r; split; auto.
    2: by apply HH.
    all: apply clos_trans_immediate1; auto.
    all: by apply ct_step.
  Qed.
  
  Lemma fsupp_rf: fsupp (rf G).
  Proof using WF.
    apply functional_inv_fsupp. by inversion WF.
  Qed.

  Lemma fsupp_sb:
    fsupp (⦗set_compl is_init⦘ ⨾ sb G).
  Proof using WF.
    unfold sb, ext_sb; unfolder; ins.
    destruct y; [exists nil; ins; desf|].
    exists (map (fun i => ThreadEvent thread i) (List.seq 0 index)).
    intros e ((NIe & E0) & (SB & E)).
    destruct e; [done| ]. destruct SB as [-> LT].
    apply in_map_iff. eexists. split; eauto. by apply in_seq0_iff.
  Qed.

  Lemma fsupp_sb_loc:
    fsupp (sb G ∩ same_loc (lab G)).
  Proof using WF.
    rewrite <- seq_id_l.
    rewrite set_full_split with (S := is_init), id_union, seq_union_l.
    apply fsupp_union.
    2: { eapply fsupp_mori; [| by apply fsupp_sb; eauto].
         red. basic_solver. }
    
    red. ins.
    remember (loc (lab G) y) as ly. destruct ly. 
    { exists [InitEvent l].
      intros x REL%seq_eqv_l. desc. destruct x; [| done].
      simpl. left. f_equal. apply proj2 in REL0.
      red in REL0.
      unfold Events.loc in REL0 at 1. rewrite wf_init_lab in REL0; auto.
      congruence. }
    exists []. red. intros x REL%seq_eqv_l. desc.
    apply proj2 in REL0. red in REL0.
    destruct x; [| done]. 
    unfold Events.loc in REL0 at 1. rewrite wf_init_lab in REL0; auto.
    congruence.
  Qed.
  
  
End FairExecution.

Lemma fin_exec_fair G (WF: Wf G) (FIN: fin_exec G):
  mem_fair G.
Proof using.
  red. apply fsupp_union_iff.
  arewrite (co G ∪ fr G ≡ ⦗acts_set G⦘ ⨾ (co G ∪ fr G) ⨾ ⦗is_w (lab G)⦘).
  { rewrite wf_coE, wf_frE, wf_coD, wf_frD; eauto. basic_solver 10. }
  red. intros w.
  destruct (classic (is_w (lab G) w)) as [W | NW].
  2: { exists []. intros. apply seq_eqv_lr in REL. by desc. }
  forward eapply is_w_loc as [l Lw]; eauto. 
  destruct FIN as [findom FIN].
  exists (InitEvent l :: findom).
  intros r REL%seq_eqv_lr. desc.
  destruct r eqn:RR.
  { simpl. left. f_equal. eapply hahn_inclusion_exp in REL0.
    2: { rewrite wf_col, wf_frl, unionK; eauto. reflexivity. }
    red in REL0. unfold loc in REL0 at 1. rewrite wf_init_lab in REL0; auto.
    congruence. }
  right. apply FIN. split; auto. 
Qed. 

Lemma fin_exec_full_fair G (WF: Wf G) (FIN: fin_exec_full G):
  mem_fair G.
Proof using.
  apply fin_exec_fair; auto. apply fin_exec_full_equiv in FIN. by desc. 
Qed. 