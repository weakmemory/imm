(*****************************************************************************)
(** The FSC memory model splits memory into non-atomic and atomic locations. *)
(** Every location can be accessed only with corresponding mode.             *)
(** FSC's memory access instructions are compiled into IMM as follows:       *)
(** +----------------+-----------------------+----------+                    *)
(** |FSC             |IMM                    |Hypotheses|                    *)
(** +----------------+-----------------------+----------+                    *)
(** |r := [x]^{na};  | r := [x]^{rlx};       |  -       |                    *)
(** |                |                       |          |                    *)
(** +----------------+-----------------------+----------+                    *)
(** |[x]^{na} := v;  | fence(acqrel);        | WNAF     |                    *)
(** |                | [x]^{rlx} := v;       |          |                    *)
(** +----------------+-----------------------+----------+                    *)
(** |r := [x]^{at};  | fence(sc);            | RATF1,   |                    *)
(** |                | r := [x]^{rlx};       | RATF2    |                    *)
(** |                | fence(sc);            |          |                    *)
(** +----------------+-----------------------+----------+                    *)
(** |[x]^{at} := v;  | fence(sc);            | WATF1,   |                    *)
(** |                | [x]^{rlx} := v;       | WATF2    |                    *)
(** |                | fence(sc);            |          |                    *)
(** +----------------+-----------------------+----------+                    *)
(*****************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import IfThen.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_ppo.
Require Import imm_hb.
Require Import imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section LDRF_Fsc.


Variable G : execution.
Hypothesis WF: Wf G.
Hypothesis IC : imm.imm_consistent G. 
           
Notation "'E'" := (acts_set G).
Notation "'Init'" := (is_init).
Notation "'NInit'" := (set_compl Init).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).

Notation "'detour'" := (detour G).

Notation "'rs'" := (rs G).
Notation "'release'" := (release G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (imm_hb.hb G).

Notation "'ar_int'" := (ar_int G).
Notation "'ppo'" := (ppo G).
Notation "'bob'" := (bob G).

Notation "'ar'" := (ar G).


Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'ORlx'" := (fun a => is_true (is_only_rlx lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Variable NA AT: actid -> Prop. 
Hypothesis LOCMODE: forall l, <<LM: Loc_ l ⊆₁ NA>> \/ <<LM: Loc_ l ⊆₁ AT>>.
Hypothesis DIFMODE: AT ∩₁ NA ≡₁ ∅.
Hypothesis RWMODE: AT ∪₁ NA ≡₁ RW.

Hypothesis WNAF : W ∩₁ NA ⊆₁ codom_rel (⦗F∩₁Acqrel⦘ ⨾ immediate sb) ∪₁ Init.
Hypothesis RATF1 : R ∩₁ AT ⊆₁ codom_rel (⦗F ∩₁ Sc⦘ ⨾ immediate sb).
Hypothesis RATF2 : R ∩₁ AT ⊆₁ dom_rel (immediate sb ⨾ ⦗F ∩₁ Sc⦘).
Hypothesis WATF1: W ∩₁ AT ⊆₁ codom_rel (⦗F ∩₁ Sc⦘ ⨾ immediate sb) ∪₁ Init.
Hypothesis WATF2: W ∩₁ AT ⊆₁ dom_rel (immediate sb ⨾ ⦗F ∩₁ Sc⦘) ∪₁ Init.


Lemma mode_split (S: actid -> Prop) (HASLOC: forall x, S x -> exists l, loc x = Some l):
  S ≡₁ (S ∩₁ NA) ∪₁ (S ∩₁ AT).
Proof using.
  red. split; [| basic_solver].
  rewrite <- set_inter_union_r.
  apply set_subset_inter_r. split; [basic_solver| ]. 
  red. intros x Sx. red.
  specialize (HASLOC x). apply HASLOC in Sx. 
  destruct Sx as [l Lx]. specialize (LOCMODE l).
  destruct LOCMODE; specialize (H x); auto. 
Qed.

    
Lemma sb_f_helper T M (TF: T ⊆₁ codom_rel (⦗F ∩₁ M⦘ ⨾ immediate sb)):
  ⦗RW⦘ ⨾ sb ⨾ ⦗T⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F ∩₁ M⦘ ⨾ sb ⨾ ⦗T⦘.
Proof using.
  unfolder. intros e a H. destruct H as [RWe [SBew Ta]]. split; auto.
  red in TF. specialize (@TF a).
  pose proof (TF Ta) as [f HH].
  apply seq_eqv_l in HH. destruct HH as [[Ff Mf] [SBfw IMMfw]].
  exists f.
  assert (NIf: NInit f).
  { specialize (read_or_fence_is_not_init WF). intros RFNI.
    specialize (RFNI f). basic_solver 10. }
  assert (NEQef: e <> f).
  { destruct RWe; red; intros; type_solver. }
  assert (SBef: sb e f).    
  { pose (sb_semi_total_r WF NIf NEQef SBew SBfw) as SB2. 
    destruct SB2; auto. exfalso. specialize (IMMfw e). auto. }
  basic_solver.  
Qed. 


Lemma sb_f_w:
  ⦗RW⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ⦗W ∩₁ AT⦘ ∪ ⦗RW⦘ ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W ∩₁ NA⦘.
Proof using.
  assert (FENCE: forall MW MF (COMP: W ∩₁ MW
          ⊆₁ codom_rel (⦗F ∩₁ MF⦘ ⨾ immediate sb) ∪₁ Init),
             ⦗RW⦘ ⨾ sb ⨾ ⦗W ∩₁ MW⦘ ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗F ∩₁ MF⦘ ⨾ sb ⨾ ⦗W ∩₁ MW⦘). 
  { ins.
    rewrite (no_sb_to_init G) at 3. rewrite seqA, <- id_inter. 
    assert (TMP: NInit ∩₁ (W ∩₁ MW) ⊆₁ codom_rel (⦗F ∩₁ MF⦘ ⨾ immediate sb)).
    { rewrite COMP. rewrite set_inter_union_r.
      apply set_subset_union_l. split; [basic_solver 10 | basic_solver]. }
    rewrite (no_sb_to_init G) at 1. rewrite seqA, <- id_inter. 
    apply (sb_f_helper TMP). }
    
  rewrite (mode_split W) at 2; [| apply is_w_loc].  
  rewrite (id_union (W ∩₁ NA) _). do 2 rewrite seq_union_r.
  unionL; [unionR right;apply (FENCE NA Acqrel WNAF)
          | unionR left; apply (FENCE AT Sc WATF1)]. 
Qed. 
  
Lemma sb_rf_acyclic: acyclic (sb ⨾ rfe).
Proof using.
  rewrite ((wf_rfeD WF)). arewrite (R ⊆₁ RW).
  rewrite <- !seqA, acyclic_rotl, !seqA.
  sin_rewrite sb_f_w.
  cdes IC. cdes Cext.
  arewrite (F ∩₁ Sc ⊆₁ F ∩₁ Acq/Rel) by mode_solver.
  arewrite (F ∩₁ Acqrel ⊆₁ F ∩₁ Acq/Rel) by mode_solver.
  assert (FBOB: sb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ⊆ bob ⨾ bob).
  { seq_rewrite <- seq_eqvK. rewrite seqA.
    sin_rewrite sb_to_f_in_bob. sin_rewrite sb_from_f_in_bob. basic_solver. }
  do 2 sin_rewrite FBOB.
  rewrite !inclusion_seq_eqv_r, !inclusion_seq_eqv_l.
  arewrite (rfe ⊆ ar). arewrite (bob ⊆ ar).
  rewrite unionK, seqA.
  red.
  red in Cext0.
  arewrite (ar ⨾ ar ⨾ ar ⊆ ar^+).
  { do 2 rewrite <- ct_unit. rewrite seqA. basic_solver 10. }
  rewrite ct_of_ct. auto.
Qed.


Lemma sb_rfe_crt_hb: (⦗RW⦘ ⨾ sb ⨾ rfe)^* ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ hb.
Proof using.
  rewrite (dom_l (wf_rfeD WF)).
  sin_rewrite sb_f_w.  
  arewrite (F ∩₁ Sc ⊆₁ F ∩₁ Acqrel) by mode_solver.
  do 2 rewrite inclusion_seq_eqv_r. rewrite unionK.
  rewrite inclusion_seq_eqv_l. 
  rewrite !seqA.
  rewrite rtE, seq_union_l. unionL.
  { rewrite sb_in_hb. basic_solver. }
  arewrite ((sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rfe)⁺ ⊆ sb ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rfe ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘)^* ⨾ ⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rfe).
  { rewrite <- seq_eqvK at 1. rewrite seqA.
    rewrite <- seqA with (r2:=⦗F ∩₁ Acqrel⦘). rewrite ct_rotl.
    basic_solver. }
  arewrite ((⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ rfe ⨾ sb ⨾ ⦗F ∩₁ Acqrel⦘) ⊆ hb).
  { seq_rewrite (dom_l (wf_rfeD WF)). rewrite seqA. 
    arewrite (⦗F ∩₁ Acqrel⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ imm_hb.release G).
    { unfold imm_hb.release. 
      arewrite (⦗W⦘ ⊆ imm_hb.rs G).
      { unfold imm_hb.rs. rewrite seq_union_r. unionR right.
        basic_solver. }
      hahn_frame_r. 
      mode_solver 10. }
    rewrite <- sw_in_hb. unfold imm_hb.sw.
    rewrite id_inter. arewrite (Acqrel ⊆₁ Acq) by mode_solver.
    arewrite ((sb ⨾ ⦗F⦘) ⊆ (sb ⨾ ⦗F⦘)^?). hahn_frame.
    unionR right. basic_solver. }
  rewrite sb_in_hb. 
  rewrite inclusion_seq_eqv_l. 
  seq_rewrite <- ct_begin. sin_rewrite ct_unit.
  rewrite (ct_of_trans (@hb_trans G)).
  basic_solver. 
Qed. 

Lemma sl_mode r (SL: r ⊆ same_loc):
  ⦗RW⦘ ⨾ r ⨾ ⦗RW⦘ ⊆ restr_rel NA r ∪ restr_rel AT r.
Proof using.
  unfolder. ins. destruct H as [RWx [RELxy RWy]].
  assert (exists l, Loc_ l x) as [l Lx].
  { unfold Events.loc. unfold is_f in *.
    destruct (lab x) eqn:AA; simpls.
    all: eauto.
    type_solver. }
  specialize (LOCMODE l).
  red in SL.
  pose proof (SL x y RELxy) as SLxy. red in SLxy.
  rewrite Lx in SLxy. 
  destruct LOCMODE; splits; auto.
Qed.

Lemma sb_f_at: RW ∩₁ AT ∩₁ NInit ⊆₁ codom_rel (⦗F ∩₁ Sc⦘ ⨾ immediate sb).
Proof using.
  do 2 rewrite set_inter_union_l.
  apply set_subset_union_l.
  split.
  { arewrite (R ∩₁ AT ∩₁ NInit ⊆₁ R ∩₁ AT) by basic_solver. } 
  rewrite WATF1. rewrite set_inter_union_l. apply set_subset_union_l.
  split; [basic_solver 10 | basic_solver]. 
Qed.

  
Lemma f_sb_at: RW ∩₁ AT ∩₁ NInit  ⊆₁ dom_rel (immediate sb ⨾ ⦗F ∩₁ Sc⦘).
Proof using.   
  do 2 rewrite set_inter_union_l.
  apply set_subset_union_l.
  split.
  { arewrite (R ∩₁ AT ∩₁ NInit ⊆₁ R ∩₁ AT) by basic_solver. } 
  rewrite WATF2. rewrite set_inter_union_l. apply set_subset_union_l.
  split; [basic_solver 10 | basic_solver]. 
Qed.


Lemma ct_dom_start: forall (A: Type) (r: relation A) (dom: A -> Prop), 
    ⦗dom⦘ ⨾ (r ⨾ ⦗dom⦘)^+ ≡ (⦗dom⦘ ⨾ r ⨾ ⦗dom⦘)^+.
Proof using.
  intros A r dom. 
  rewrite ct_rotl.
  rewrite <- (seqA ⦗dom⦘ r ⦗dom⦘). rewrite ct_rotl.
  rewrite !seqA.
  seq_rewrite seq_eqvK.
  basic_solver. 
Qed.

Lemma acyclic_empty: forall (A: Type), @acyclic A ∅₂.
Proof using.
  intros A. red.
  rewrite ct_of_trans; [| basic_solver]. 
  basic_solver.
Qed. 

Lemma sb_eco_sb_psc: ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ psc G.
Proof using. unfold psc. rewrite sb_in_hb. basic_solver 10. Qed. 

Lemma RFE1: rfe^+ ≡ rfe.
Proof using.  apply ct_no_step. rewrite (wf_rfeD WF). type_solver. Qed. 

Lemma no_eco_to_init: eco ≡ eco ⨾ ⦗NInit⦘. 
Proof using.
  split; [| basic_solver].
  arewrite (eco ≡ eco ⨾ ⦗codom_rel eco⦘) at 1 by basic_solver.
  apply seq_mori; [basic_solver|]. 
  rewrite (eco_alt3 WF).
  cdes IC. 
  rewrite (no_rf_to_init WF), (no_co_to_init WF (coherence_sc_per_loc Cint)).
  rewrite (no_fr_to_init WF (coherence_sc_per_loc Cint)). 
  do 2 rewrite <- seq_union_l.
  rewrite inclusion_ct_seq_eqv_r. rewrite codom_seq.
  basic_solver.
Qed. 

Lemma acyclic_sb_rf_eco: acyclic (sb ∪ restr_rel NA rf ∪ restr_rel AT eco). 
Proof using.
  rewrite rfi_union_rfe, <- union_restr, <- unionA.
  arewrite (restr_rel NA rfi ⊆ sb). rewrite unionK. 
  assert (na_at_rels_empty: restr_rel NA rfe ⨾ restr_rel AT eco ≡ ∅₂).
  { generalize DIFMODE. basic_solver. }
  rewrite unionA. apply acyclic_union1; [apply Execution.sb_acyclic | |].
  { cdes IC. cdes Cint. 
    apply acyclic_union1.    
    { rewrite inclusion_restr. 
      rewrite (wf_rfeD WF). apply acyclic_disj. type_solver. }
    { rewrite inclusion_restr. 
      red. rewrite (ct_of_trans (eco_trans WF)).
      apply (eco_irr WF). }
    rewrite ct_end, ct_begin, seqA.
    seq_rewrite na_at_rels_empty.
    rewrite seq_false_l, seq_false_r. apply acyclic_empty. }
  rewrite (ct_of_trans (@sb_trans G)).
  arewrite ((restr_rel NA rfe ∪ restr_rel AT eco)⁺ ⊆ (restr_rel NA rfe)⁺ ∪ (restr_rel AT eco)⁺).
  { rewrite path_union. apply union_mori; [basic_solver| ]. 
    rewrite rtE. rewrite seq_union_l.
    rewrite (ct_end (restr_rel NA rfe)) at 1. rewrite seqA.
    rewrite na_at_rels_empty. 
    rewrite !seq_false_r, union_false_r. rewrite seq_id_l at 1. 
    rewrite seq_union_r. unionL; [basic_solver| ].
    rewrite ct_end, ct_begin, seqA at 1.
    assert (restr_rel AT eco ⨾ restr_rel NA rfe ≡ ∅₂).
    { do 2 rewrite restr_relE, seqA.
      seq_rewrite <- id_inter. rewrite DIFMODE. basic_solver. } 
    seq_rewrite H. basic_solver. }
  rewrite seq_union_r.
  
  apply acyclic_union1.
  { rewrite inclusion_restr. 
    rewrite RFE1. apply sb_rf_acyclic. }
  { rewrite restr_relE. 
    rewrite inclusion_ct_seq_eqv_l, inclusion_seq_eqv_r. 
    rewrite (ct_of_trans (eco_trans WF)). 
    rewrite (wf_ecoD WF). seq_rewrite <- id_inter. 
    rewrite <- seqA with (r3:=⦗RW⦘), <- seqA. rewrite acyclic_rotl.
    rewrite set_interC. 
    rewrite no_sb_to_init, seqA. seq_rewrite <- id_inter. rewrite set_interC. 
    sin_rewrite (sb_f_helper sb_f_at).
    rewrite inclusion_seq_eqv_r,  inclusion_seq_eqv_l. 
    rewrite !seqA.
    rewrite <- (seq_eqvK (F ∩₁ Sc)), seqA.
    rewrite <- seqA with (r2:=⦗F ∩₁ Sc⦘). 
    apply acyclic_rotl. rewrite !seqA.
    rewrite sb_eco_sb_psc. arewrite (psc G ⊆ ar). 
    cdes IC. cdes Cext. auto. }
  rewrite inclusion_restr, RFE1. 
  rewrite restr_relE, inclusion_seq_eqv_r. 
  rewrite acyclic_rotl.
  rewrite inclusion_ct_seq_eqv_l. 
  rewrite (ct_of_trans (eco_trans WF)).
  rewrite (dom_r (wf_rfeD WF)) at 1. arewrite (R ⊆₁ RW) at 1.
  rewrite <- seqA with (r3:=⦗RW⦘). 
  rewrite (@inclusion_ct_seq_eqv_r _ RW _). 
  rewrite <- seqA, acyclic_rotl.
  arewrite (⦗RW⦘ ⨾ (sb ⨾ ⦗AT⦘ ⨾ eco)⁺ ⊆ (⦗RW⦘ ⨾ sb ⨾ ⦗RW ∩₁ AT⦘ ⨾ eco)⁺).
  { rewrite (wf_ecoD WF) at 1. 
    rewrite <- !seqA.
    rewrite ct_dom_start, !seqA.
    apply clos_trans_mori.
    hahn_frame. basic_solver. }
  rewrite no_sb_to_init, seqA. seq_rewrite <- id_inter. rewrite set_interC. 
  sin_rewrite (sb_f_helper sb_f_at).
  do 2 rewrite inclusion_seq_eqv_r. 
  rewrite <- (seq_eqvK (F ∩₁ Sc)), !seqA.
  rewrite <- seqA with (r2:=⦗F ∩₁ Sc⦘). rewrite <- seqA with (r1:=⦗RW⦘).
  rewrite inclusion_seq_eqv_l. 
  rewrite ct_rotl, !seqA. 
  rewrite sb_eco_sb_psc.

  rewrite <- seqA. rewrite acyclic_rotl. 
  rewrite !seqA.
  
  arewrite (eco ⨾ (sb ⨾ rfe)⁺ ⊆ eco ⨾ (⦗RW⦘ ⨾ sb ⨾ rfe)⁺).
  { rewrite (dom_r (wf_ecoD WF)) at 1. rewrite !seqA. hahn_frame_l.
    rewrite (dom_r (wf_rfeD WF)) at 1. 
    arewrite (R ⊆₁ RW) at 2. rewrite <- seqA. 
    rewrite ct_dom_start.
    rewrite inclusion_seq_eqv_r. basic_solver. }

  rewrite <- (seq_eqvK (F ∩₁ Sc)) at 2.
  rewrite inclusion_t_rt. sin_rewrite sb_rfe_crt_hb.
  arewrite ((⦗F ∩₁ Sc⦘ ⨾ sb ⨾ eco ⨾ hb ⨾ ⦗F ∩₁ Sc⦘) ⊆ psc G). 
  rewrite <- ct_end. arewrite (psc G ⊆ ar). 
  red. rewrite ct_of_ct. 
  cdes IC. cdes Cext. auto. 
Qed.   
  
Lemma imm_to_ocaml_causal:
  acyclic (sb ∪ rfe ∪ restr_rel AT (coe ∪ fre G)).
Proof using.
  arewrite (rfe ⊆ rf). 
  arewrite (rf ⊆ restr_rel NA rf ∪ restr_rel AT rf).
  { rewrite (wf_rfD WF) at 1. arewrite (R ⊆₁ RW). arewrite (W ⊆₁ RW) at 1.  
    rewrite sl_mode; [basic_solver | apply (wf_rfl WF)]. }

  do 2 rewrite unionA.
  rewrite union_restr. 
  arewrite ((rf ∪ (coe ∪ fre G)) ⊆ eco).
  { unfold Execution_eco.eco, Execution.rf, Execution.coe, Execution.fre. basic_solver 10. }
  rewrite <- unionA. apply acyclic_sb_rf_eco. 
Qed.


Lemma f_sb_helper T M (TF: T ⊆₁ dom_rel (immediate sb ⨾ ⦗F ∩₁ M⦘))
  (NIT: T ∩₁ is_init ≡₁ ∅):
  ⦗T⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ ⦗T⦘ ⨾ sb ⨾ ⦗F ∩₁ M⦘ ⨾ sb ⨾ ⦗RW⦘.
Proof using.
  unfolder. intros a e [Ta [SBae RWe]]. split; auto. 
  red in TF. specialize (@TF a).
  pose proof (TF Ta) as [f HH].
  apply seq_eqv_r in HH. destruct HH as [[SBaf IMMfw] [Ff Mf]].
  exists f.
  assert (NIa: ~is_init a).
  { red in NIT. destruct NIT as [NIT _]. red in NIT.
    specialize (NIT a).
    red. intros contra.
    destruct NIT. red. split; auto. }
  assert (NEQef: e <> f).
  { destruct RWe; red; intros; type_solver. }
  assert (SBfe: sb f e).    
  { pose (sb_semi_total_l WF NIa NEQef SBae SBaf) as SB2. 
    destruct SB2; auto. exfalso. specialize (IMMfw e). auto. }
  basic_solver.  
Qed.
  
Lemma ac_irr: forall A (r: relation A), acyclic r <-> irreflexive r^+.
Proof using. intros A r. basic_solver. Qed. 

Definition ae := (⦗AT⦘ ⨾ (rfe ∪ co) ⨾ ⦗AT⦘).


Lemma imm_to_ocaml_coherent: irreflexive ((sb ∪ ae)^+ ⨾ (co ∪ fr)).
Proof using.
  arewrite (co ∪ fr ⊆ eco) by unfold Execution_eco.eco; basic_solver 10. 
  rewrite ct_unionE.
  assert (ae_in_eco: ae ⊆ eco).
  { unfold Execution_eco.eco, ae.
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
    unfold Execution.rfe. 
    basic_solver 10. }
  rewrite seq_union_l. apply irreflexive_union. split.
  { rewrite ae_in_eco. 
    rewrite ct_unit.
    rewrite (ct_of_trans (eco_trans WF)). 
    apply (eco_irr WF). }
  rewrite seqA.
  rewrite irreflexive_seqC, seqA.
  arewrite (eco ⨾ ae＊ ⊆ eco).
  { rewrite ae_in_eco. rewrite <- ct_begin.
    apply (ct_of_trans (eco_trans WF)). }
  rewrite rtE, seq_union_r, seq_id_r.
  rewrite unionC, path_absorb2.
  2: { sin_rewrite (rewrite_trans (@sb_trans G)). basic_solver. }
  do 2 rewrite seq_union_l. rewrite unionA. apply irreflexive_union. split.
  { arewrite (ae ⊆ ⦗AT⦘ ⨾ eco ⨾ ⦗AT⦘).
    { unfold ae, Execution_eco.eco, Execution.rfe. basic_solver 10. }
    rewrite <- restr_relE.     
    rewrite (ct_of_trans (transitive_restr (eco_trans WF))).
    assert (eco_sl: eco ⊆ same_loc).
    { rewrite (eco_alt3 WF).
      rewrite (wf_rfl WF), (wf_col WF), (wf_frl WF).
      do 2 rewrite unionK. apply (ct_of_trans (@same_loc_trans _ lab)). }
    rewrite (wf_ecoD WF) at 2. 
    rewrite (sl_mode eco_sl). 
    rewrite seq_union_r.
    apply irreflexive_union. split. 
    { rewrite ct_end, seqA, seqA.
      arewrite (restr_rel AT eco ⨾ restr_rel NA eco ⊆ ∅₂).
      { do 2 rewrite restr_relE. generalize DIFMODE. basic_solver. }
      rewrite !seq_false_r. basic_solver. }
    rewrite ct_rotl, !seqA.
    rewrite (rewrite_trans (transitive_restr (eco_trans WF))).
    rewrite <- ct_rotl. 
    rewrite <- ac_irr. apply acyclic_seq_from_union. 
    arewrite (sb ∪ restr_rel AT eco ⊆ sb ∪ restr_rel NA rf ∪ restr_rel AT eco) by basic_solver 10.
    apply acyclic_sb_rf_eco. }
      
  rewrite (ct_of_trans (@sb_trans G)).
  apply irreflexive_union. split.
  { rewrite sb_in_hb.
    cdes IC. cdes Cint. auto. }
  rewrite (dom_r (wf_ecoD WF)), <- seqA.
  rewrite irreflexive_seqC, seqA. 
  arewrite (⦗RW⦘ ⨾ (sb ⨾ ae⁺)⁺ ⊆  sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ (psc G)^* ⨾ ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ae⁺).
  { 
    arewrite (ae⁺ ⊆ ⦗RW ∩₁ AT⦘ ⨾ ae⁺ ⨾ ⦗RW⦘) at 1. 
    { rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
      apply clos_trans_mori. 
      unfold ae. rewrite !seqA.
      rewrite id_inter, seqA. seq_rewrite seq_eqvK.
      seq_rewrite (seq_eqvC (RW) (AT)). rewrite seqA. 
      rewrite (seq_eqvC (AT) (RW)).
      hahn_frame.
      rewrite ((wf_rfeD WF)), ((wf_coD WF)) at 1.
      basic_solver. }
    do 2 rewrite <- seqA. rewrite ct_dom_start, seqA, seqA.     
    rewrite no_sb_to_init at 1. rewrite seqA.
    seq_rewrite <- id_inter. rewrite set_interC. 
    sin_rewrite (sb_f_helper sb_f_at). do 2 rewrite inclusion_seq_eqv_r. 
    rewrite !seqA.
    rewrite inclusion_seq_eqv_l.
    rewrite <- seq_eqvK at 1. rewrite seqA.
    rewrite <- seqA with (r2:=⦗F ∩₁ Sc⦘). rewrite ct_rotl, seqA.
    hahn_frame. repeat hahn_frame_r. 
    apply clos_refl_trans_mori.
    rewrite ae_in_eco. rewrite (ct_of_trans (eco_trans WF)).
    rewrite sb_in_hb. 
    unfold psc. basic_solver 10. }
  arewrite (ae⁺ ⊆ eco ⨾ ⦗RW ∩₁ AT⦘).
  { unfold ae. rewrite <- seqA, inclusion_ct_seq_eqv_r.
    rewrite id_inter. hahn_frame.
    rewrite inclusion_seq_eqv_l.
    arewrite (rfe ∪ co ⊆ eco) by unfold Execution_eco.eco, Execution.rfe; basic_solver 10.
    rewrite (ct_of_trans (eco_trans WF)).
    apply (dom_r (wf_ecoD WF)). }
  
  rewrite (dom_l (wf_ecoD WF)) at 2.  
  rewrite no_eco_to_init. rewrite seqA.
  seq_rewrite <- id_inter. rewrite (set_interC _ (RW ∩₁ AT)). 
  assert (NINIT: RW ∩₁ AT ∩₁ NInit ∩₁ Init ≡₁ ∅) by basic_solver. 
  sin_rewrite (f_sb_helper f_sb_at NINIT). 
  rewrite !seqA. 
  sin_rewrite (@inclusion_seq_eqv_r _ eco _).
  rewrite <- seq_eqvK at 3. rewrite seqA.
  arewrite (⦗RW ∩₁ AT ∩₁ NInit⦘ ⨾ sb ⊆ sb). 
  sin_rewrite sb_eco_sb_psc. 
  rewrite <- seqA with (r2:=psc G). rewrite <- seqA with (r1:=sb).
  rewrite irreflexive_seqC, !seqA.
  sin_rewrite (@inclusion_seq_eqv_l _ eco _). 
  sin_rewrite sb_eco_sb_psc. 
  seq_rewrite <- ct_end. rewrite ct_unit. 
  arewrite (psc G ⊆ ar). 
  cdes IC. cdes Cext. auto.
Qed.

Theorem ldrf_condition_ext:
  acyclic(sb ∪ rf ∪ ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗F ∩₁ Sc⦘). 
Proof using.
  apply acyclic_union1.
  { rewrite (wf_rfD WF). arewrite (W ⊆₁ RW). arewrite (R ⊆₁ RW) at 2 .
    rewrite (sl_mode); [| apply (wf_rfl WF)].
    rewrite rf_in_eco at 2. rewrite <- unionA.
    apply acyclic_sb_rf_eco. }
  { sin_rewrite sb_eco_sb_psc. arewrite (psc G ⊆ ar). 
    cdes IC. cdes Cext. auto. }
  rewrite rfi_union_rfe, (rfi_in_sbloc' WF), inclusion_inter_l1. 
  rewrite <- unionA, unionK. 
  rewrite <- seq_eqvK. rewrite !seqA.
  sin_rewrite sb_eco_sb_psc.
  rewrite unionC. rewrite path_ut2; [| apply (@sb_trans G)].
  rewrite RFE1. arewrite (rfe^* ≡ rfe^?).
  { rewrite rtE, RFE1. basic_solver. }
  rewrite <- seqA with (r3:=⦗F ∩₁ Sc⦘). rewrite inclusion_ct_seq_eqv_r.
  rewrite <- seqA. rewrite acyclic_rotl.
  seq_rewrite seq_union_r.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ rfe ≡ ∅₂) by rewrite (wf_rfeD WF); type_solver. 
  rewrite union_false_l. 
  arewrite (⦗F ∩₁ Sc⦘ ⨾ rfe^? ≡ ⦗F ∩₁ Sc⦘) by rewrite (wf_rfeD WF); type_solver. 
  rewrite inclusion_ct_seq_eqv_l.
  arewrite (rfe^? ⨾ ⦗F ∩₁ Sc⦘ ≡ ⦗F ∩₁ Sc⦘) by rewrite (wf_rfeD WF); type_solver. 
  rewrite rtE. repeat case_union _ _.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗fun _ : actid => True⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar).
  { arewrite (sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ bob).
    { unfold imm_bob.bob, imm_bob.fwbob.
      arewrite (Sc ⊆₁ Acq/Rel) by mode_solver. 
      basic_solver 10. }
    unfold imm.ar, imm_ppo.ar_int. basic_solver 10. }
  rewrite ct_begin with (r:=(sb ⨾ rfe)).
  rewrite !seqA.
  rewrite (dom_r (wf_rfeD WF)), seqA.
  arewrite (⦗R⦘ ⨾ (sb ⨾ rfe ⨾ ⦗R⦘)＊ ⊆ (⦗RW⦘ ⨾ sb ⨾ rfe)＊).
  { rewrite rtE, seq_union_r. unionL; [basic_solver| ].
    arewrite (⦗R⦘ ⊆ ⦗RW⦘). rewrite <- seqA, ct_dom_start.
    rewrite inclusion_seq_eqv_r. basic_solver. }
  sin_rewrite sb_rfe_crt_hb.
  arewrite (rfe ⊆ eco) by unfold Execution_eco.eco, Execution.rfe; basic_solver.
  arewrite ((psc G)⁺ ⊆ ⦗F ∩₁ Sc⦘ ⨾ (psc G)⁺).
  { unfold psc. rewrite <- seq_eqvK at 1. rewrite seqA.
    rewrite inclusion_ct_seq_eqv_l at 1. basic_solver. }
  arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⨾ eco ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ psc G).
  arewrite (psc G ⊆ ar).
  rewrite inclusion_seq_eqv_l, unionK. 
  rewrite acyclic_rotl, ct_unit. 
  red. rewrite ct_of_ct.
  cdes IC. cdes Cext. auto.   
Qed.

Theorem ldrf_condition: acyclic(sb ∪ rf ∪ ⦗AT⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗AT⦘).
Proof using. 
  arewrite (sb ∪ rf ∪ ⦗AT⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗AT⦘ ⊆ (sb ∪ rf ∪ ⦗AT⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗AT⦘) ⨾ ⦗NInit⦘).
  { rewrite (no_sb_to_init G) at 1. rewrite (no_sb_to_init G) at 3.
    rewrite (no_rf_to_init WF) at 1. 
    rewrite seqA. rewrite seq_eqvC. 
    rewrite <- !seqA. do 2 rewrite <- seq_union_l.
    hahn_frame. basic_solver. }

  rewrite acyclic_rotl, seq_union_r.
  arewrite (AT ⊆₁ RW ∩₁ AT).
  { apply set_subset_inter_r. split; auto. generalize RWMODE. basic_solver. }
  arewrite (⦗NInit⦘ ⨾ ⦗RW ∩₁ AT⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗RW ∩₁ AT⦘ ⊆ ⦗RW ∩₁ AT⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ eco ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⨾ sb). 
  { seq_rewrite <- id_inter. rewrite set_interC.
    rewrite (wf_ecoD WF), !seqA.
    rewrite no_sb_to_init at 2. rewrite seqA, <- id_inter. rewrite (set_interC NInit _).  
    rewrite (sb_f_helper sb_f_at). rewrite inclusion_seq_eqv_r. 
    do 5 hahn_frame_r. 
    assert (ninit': (RW ∩₁ AT ∩₁ NInit) ∩₁ is_init ≡₁ ∅) by basic_solver.
    sin_rewrite (f_sb_helper f_sb_at ninit').
    hahn_frame. basic_solver. }
  do 2 rewrite inclusion_seq_eqv_l. 
  red.
  assert (ct_spec: forall (x y z: relation actid), (x ∪ y ∪ x ⨾ z ⨾ x)⁺ ⊆ (x ∪ y ∪ z)⁺).
  { intros x y z.
    assert (inclusion_ext: x ∪ y ∪ x ⨾ z ⨾ x ⊆ (x ∪ y ∪ z)⁺). 
    { apply inclusion_union_l.
      { rewrite <- ct_step. basic_solver. }
      do 2 rewrite <- ct_unit. 
      rewrite <- seqA.
      apply seq_mori; [| basic_solver]. apply seq_mori; [| basic_solver].
      rewrite <- ct_step. basic_solver. }
    apply inclusion_t_ind_right; [apply inclusion_ext| ]. 
    rewrite <- ct_ct with (r:=(x ∪ y ∪ z)) at 2.
    apply seq_mori; [basic_solver | apply inclusion_ext]. }
  do 4 rewrite <- seqA with (r3:=sb). 
  rewrite ct_spec.
  apply -> ac_irr. apply ldrf_condition_ext. 
Qed. 
  
End LDRF_Fsc.
