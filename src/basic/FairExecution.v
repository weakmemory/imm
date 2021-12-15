Require Import Lia.
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.

Definition mem_fair (G: execution) := fsupp (co G) /\ fsupp (fr G). 

Section FairExecution.
  Variable G: execution.
  Hypothesis FAIR: mem_fair G.
  Hypothesis WF: Wf G. 

  Lemma co_imm:
    co G ≡ (immediate (co G))⁺.
  Proof. apply fsupp_imm_t; apply WF || apply FAIR. Qed. 

  Lemma nS_imm_co_in_sb
        (S : actid -> Prop) w wnext
        (WW : is_w (lab G) w)
        (NSW : ~ S w)
        (NCOIMM : immediate ((co G) ⨾ ⦗S⦘) w wnext)
        (FOR_SPLIT : ⦗set_compl S⦘ ⨾ immediate (co G) ⊆ sb G) :
    sb G w wnext.
  Proof.
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
        { apply clos_trans_immediate1; auto.
          eapply (co_trans WF). }
        ins. eapply NCOIMM; [|by apply R2].
        apply seq_eqv_r in R1; destruct R1 as [R1 R3].
        apply seq_eqv_r; split; auto.
        eapply (co_trans WF); [|by apply R1].
        apply clos_trans_immediate1; auto.
        eapply (co_trans WF). }
      clear IMM.
      induction IMMS.
      { apply rt_step. apply seq_eqv_l; split; auto. }
      assert (co G y wnext) as YNEXT.
      { apply clos_trans_immediate1; auto.
        eapply (co_trans WF).
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
        apply clos_trans_immediate1; auto.
        eapply (co_trans WF). }
      eapply rt_trans.
      { by apply IHIMMS1. }
      apply IHIMMS2; auto.
      { apply (wf_coD WF) in YNEXT.
        apply seq_eqv_l in YNEXT; desf. }
      intros NISS. eapply NCOIMM; apply seq_eqv_r; split; auto.
      2: by apply NISS.
      2: done.
      apply clos_trans_immediate1; auto.
        by apply (co_trans WF). }
    intros HH. apply rtE in IMMS; destruct IMMS as [IMSS|IMMS].
    { red in IMSS; desf. }
    eapply NCOIMM; apply seq_eqv_r; split; auto.
    2: by apply HH.
    all: apply clos_trans_immediate1; auto.
    all: apply (co_trans WF).
  Qed.
  

End FairExecution.   

