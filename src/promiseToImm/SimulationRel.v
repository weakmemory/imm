Require Import Classical Peano_dec.
From hahn Require Import Hahn.
From promising Require Import Basic DenseOrder
     TView View Time Event Cell Thread Language Memory Configuration.

Require Import Events Execution.
Require Import imm_s_hb imm_s.

Require Import PArith.
Require Import CombRelations.
Require Import AuxRel.
Require Import TraversalConfig.
Require Import Setoid.
Require Import MaxValue ViewRel.
Require Import Event_imm_promise.
Require Import Promise ProgToExecution.
Require Import ProgToExecutionProperties.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section SimRel.
  Variable G : execution.
  Variable WF : Wf G.
  Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'coi'" := G.(coi).
Notation "'sw'" := G.(sw).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1). (* , format "'Loc_'  l"). *)
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
  
  Definition tmin := xH.
  Definition f_to_coherent (I : actid -> Prop) (f_to f_from : actid -> Time.t) :=
    (* ⟪ NW  : forall a, ~ is_w lab a -> f_to a = tmin ⟫ /\ *)
    ⟪ TINITTO : forall x, (is_init ∩₁ E) x -> f_to x = tmin ⟫ /\
    ⟪ TINITFROM : forall x, (is_init ∩₁ E) x -> f_from x = tmin ⟫ /\
    ⟪ TTOFROM : forall x,
         I x -> ~ is_init x -> Time.lt (f_from x) (f_to x) ⟫ /\
    ⟪ TCO : forall x y,
        I x -> I y ->
        co x y -> Time.le (f_to x) (f_from y) ⟫ /\
    ⟪ TRMW : forall x y,
        I x -> I y -> (rf ⨾ rmw) x y -> f_to x = f_from y ⟫
  .

Lemma init_co_w (IMMCON : imm_consistent G sc)
      e e' (INIT : is_init e) (NINIT : ~ is_init e')
      (EE : E e') (WW : W e') (SL : same_loc lab e e') :
  co e e'.
Proof.
  destruct (is_w_loc lab e' WW) as [l LOC].
  red in SL. rewrite LOC in SL.
  unfold is_init in INIT. unfold loc in SL.
  destruct e; [|done].
  rewrite WF.(wf_init_lab) in SL. inv SL.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists. eauto. }
  edestruct WF.(wf_co_total) as [CO|CO]; eauto; desf.
  { split; [split|]; auto. by apply init_w.
    unfold loc at 1. by rewrite WF.(wf_init_lab). }
  { intros H. subst. desf. }
  exfalso. cdes IMMCON.
  eapply Cint. eexists. split.
  { apply sb_in_hb. by apply init_ninit_sb with (y:=e'); eauto. }
  apply r_step. apply Execution_eco.co_in_eco; eauto.
Qed.

Lemma f_to_co_mon (IMMCON : imm_consistent G sc)
      I f_to f_from (FCOH : f_to_coherent I f_to f_from)
      e e' (CO : co e e') (ISS : I e) (ISS' : I e') :
  Time.lt (f_to e) (f_to e').
Proof.
  eapply TimeFacts.le_lt_lt.
  2: eapply FCOH; auto.
  { by apply FCOH. }
  apply Execution_eco.no_co_to_init in CO; auto.
  { apply seq_eqv_r in CO. desf. }
  apply coherence_sc_per_loc.
  apply IMMCON.
Qed.

Lemma f_from_co_mon I f_to f_from (FCOH : f_to_coherent I f_to f_from)
      e e' (NINIT : ~ is_init e) (CO : co e e') (ISS : I e) (ISS' : I e') :
  Time.lt (f_from e) (f_from e').
Proof.
  eapply TimeFacts.lt_le_lt.
  { eapply FCOH; eauto. }
    by apply FCOH.
Qed.

Lemma f_to_coherent_strict (IMMCON : imm_consistent G sc)
      f_to f_from T
      (TCCOH : tc_coherent G sc T)
      (FCOH: f_to_coherent (issued T) f_to f_from)
      x y z (ISSX : issued T x) (ISSY : issued T y) (ISSZ : issued T z)
      (COXY: co x y) (COYZ: co y z) :
  Time.lt (f_to x) (f_from z).
Proof.
  eapply TimeFacts.le_lt_lt.
  { apply FCOH.
    3: by apply COXY.
    all: eauto. }
  eapply f_from_co_mon; eauto.
  apply Execution_eco.no_co_to_init in COXY; auto.
  { apply seq_eqv_r in COXY. desf. }
  apply coherence_sc_per_loc.
  apply IMMCON.
Qed.

Lemma lt_init_ts T f_to f_from
      (CON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (FCOH : f_to_coherent (issued T) f_to f_from) e (EE : E e)
      (WW : W e) (ISS : issued T e) (NINIT : ~ is_init e) :
  Time.lt tmin (f_to e).
Proof.
  unfold is_w in *.
  destruct e; desf.
  cdes FCOH.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists.
    split; eauto. unfold loc. desf. }
  assert ((is_init ∩₁ E) (InitEvent l)) as LL.
  { by split; eauto. }
  erewrite <- TINITTO; eauto.
  eapply f_to_co_mon; eauto.
  2: { eapply w_covered_issued; eauto.
       split; eauto; [by apply init_w|]. 
         by apply TCCOH. }
  apply init_co_w; auto.
  { unfold is_w. desf. }
  red. unfold loc. rewrite WF.(wf_init_lab).
  desf.
Qed.

Lemma le_init_ts T f_to f_from
      (CON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (FCOH : f_to_coherent (issued T) f_to f_from) e (EE : E e)
      (WW : W e) (ISS : issued T e) :
  Time.le tmin (f_to e).
Proof.
  unfold is_w in *.
  destruct e; desf.
  { apply Time.le_lteq. right.
    symmetry. cdes FCOH. apply TINITTO.
    split; auto. }
  apply Time.le_lteq. left.
  eapply lt_init_ts; eauto.
  unfold is_w. desf.
Qed.

Lemma le_init_ts_from T f_to f_from
      (CON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (FCOH : f_to_coherent (issued T) f_to f_from) e (EE : E e)
      (WW : W e) (ISS : issued T e) (NINIT : ~ is_init e) :
  Time.le tmin (f_from e).
Proof.
  unfold is_w in *.
  destruct e; desf.
  cdes FCOH.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists.
    split; eauto. unfold loc. desf. }
  assert ((is_init ∩₁ E) (InitEvent l)) as LL.
  { by split; eauto. }
  erewrite <- TINITTO; eauto.
  apply FCOH; eauto.
  { eapply w_covered_issued; eauto.
    split; eauto; [by apply init_w|]. 
      by apply TCCOH. }
  apply init_co_w; auto.
  { unfold is_w. desf. }
  red. unfold loc. rewrite WF.(wf_init_lab).
  desf.
Qed.

Lemma f_to_eq (IMMCON : imm_consistent G sc) T (TCCOH : tc_coherent G sc T)
      f_to f_from (FCOH : f_to_coherent (issued T) f_to f_from)
      e e' (SAME_LOC : same_loc lab e e') (ISS : issued T e) (ISS' : issued T e')
      (FEQ : f_to e = f_to e') :
  e = e'.
Proof.
  assert (E e /\ E e') as [EE EE']. 
  { by split; apply TCCOH. }
  assert (W e /\ W e') as [WE WE']. 
  { by split; apply TCCOH. }
  destruct (classic (e = e')) as [|NEQ]; auto.
  exfalso.
  edestruct (wf_co_total WF); eauto.
  1,2: split; [split|]; eauto.
  { assert (Time.lt (f_to e) (f_to e')) as HH.
    { eapply f_to_co_mon; eauto. }
    rewrite FEQ in *.
      by apply DenseOrder.lt_strorder in HH. }
  assert (Time.lt (f_to e') (f_to e)) as HH.
  { eapply f_to_co_mon; eauto. }
  rewrite FEQ in *.
    by apply DenseOrder.lt_strorder in HH.
Qed.

Lemma f_from_eq (IMMCON : imm_consistent G sc) T (TCCOH : tc_coherent G sc T)
      f_to f_from (FCOH : f_to_coherent (issued T) f_to f_from)
      e e' (SAME_LOC : same_loc lab e e') (ISS : issued T e) (ISS' : issued T e')
      (NINIT : ~ is_init e) (NINIT' : ~ is_init e')
      (FEQ : f_from e = f_from e') :
  e = e'.
Proof.
  assert (E e /\ E e') as [EE EE']. 
  { by split; apply TCCOH. }
  assert (W e /\ W e') as [WE WE']. 
  { by split; apply TCCOH. }
  destruct (classic (e = e')) as [|NEQ]; auto.
  exfalso.
  edestruct (wf_co_total WF); eauto.
  1,2: split; [split|]; eauto.
  { assert (Time.lt (f_from e) (f_from e')) as HH.
    { eapply f_from_co_mon; eauto. }
    rewrite FEQ in *.
      by apply DenseOrder.lt_strorder in HH. }
  assert (Time.lt (f_from e') (f_from e)) as HH.
  { eapply f_from_co_mon; eauto. }
  rewrite FEQ in *.
    by apply DenseOrder.lt_strorder in HH.
Qed.
 
  Definition nth {A} (r : relation A) n :=
    codom_rel r ^^ (n + 1) \₁ codom_rel r ^^ n.
  
Definition sim_prom
           (thread : thread_id)
           (T : trav_config)
           (f_to f_from : actid -> Time.t)
           promises :=
  forall l to from v rel
         (PROM  : Memory.get l to promises =
                  Some (from, Message.mk v rel)),
  exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ TID  : tid b = thread ⟫ /\
    ⟪ ISS  : issued T b ⟫ /\
    ⟪ NCOV : ~ covered T b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫ /\
    ⟪ HELPER : sim_mem_helper G sc f_to b from v rel.(View.unwrap) ⟫.

Definition message_to_event (f_to f_from : actid -> Time.t) I (memory : Memory.t) :=
  forall l to from v rel
         (MSG : Memory.get l to memory = Some (from, Message.mk v rel)),
    (to = Time.bot /\ from = Time.bot) \/
    exists b,
    ⟪ ACTS : E b ⟫ /\
    ⟪ ISS  : I b ⟫ /\
    ⟪ LOC  : Loc_ l b ⟫ /\
    ⟪ FROM : f_from b = from ⟫ /\
    ⟪ TO   : f_to b = to ⟫.

(* Definition intervals_for_issue f_to f_from I mem := *)
  (* ⟪ INTERVAL : *)
    (* forall l x y *)
    (*        (LOCX : loc lab x = Some l) *)
    (*        (NIMM : immediate (⦗ I ⦘ ⨾ co ⨾ ⦗ I ⦘) x y) *)
    (*        (INTERVAL_NEEDED : exists z, *)
    (*            ⟪ NISS : ~ I z ⟫ /\ ⟪ COXZ : co x z ⟫ /\ ⟪ COZY : co z y ⟫), *)
    (* forall to from msg (INMEM : Memory.get l to mem = Some (from, msg)), *)
    (*   Interval.disjoint (from, to) (f_to x, f_from y) ⟫ /\ *)
  (* ⟪ MEM : *)
  (* message_to_event f_to f_from I mem. *)
  (* ⟫. *)

  (* forall w l (WNISS : ~ I w) (LOC : loc lab w = Some l), *)
  (*   exists to from, *)
  (*     let f_to'   := upd f_to   w to   in *)
  (*     let f_from' := upd f_from w from in *)
  (*     ⟪ FCOH' : f_to_coherent (I ∪₁ eq w) f_to' f_from' ⟫ /\ *)
  (*     ⟪ LT : Time.lt from to ⟫ /\ *)
  (*     ⟪ DISJOINT : *)
  (*       forall m_to m_from msg (INMEM : Memory.get l to mem = Some (from, msg)), *)
  (*         Interval.disjoint (from, to) (m_from, m_to)  *)
  (*     ⟫. *)

Definition sim_mem
           (T : trav_config)
           (f_to f_from : actid -> Time.t)
           (thread : thread_id)
           (local : Local.t)
           mem :=
    forall l b (EB: E b) (ISSB: issued T b) (LOC: Loc_ l b)
                   v (VAL: val lab b = Some v) ,
    exists rel_opt,
      let rel := rel_opt.(View.unwrap) in
      ⟪ INMEM : Memory.get l (f_to b) mem =
                 Some (f_from b, Message.mk v rel_opt) ⟫ /\

      ⟪ HELPER : sim_mem_helper G sc f_to b (f_from b) v rel ⟫ /\
      ⟪ REL_PLN_RLX : TimeMap.eq (View.pln rel) (View.rlx rel) ⟫ /\
      ⟪ MEM_CLOS : Memory.closed_timemap (View.rlx rel) mem ⟫ /\

      (⟪ TID  : tid b = thread ⟫ ->
       ⟪ NCOV : ~ covered T b ⟫ ->
       ⟪ PROM: Memory.get l (f_to b) local.(Local.promises) =
          Some (f_from b, Message.mk v rel_opt) ⟫ /\
       ⟪ REL_REPR :
         exists p_rel,
           ⟪ REL : rel_opt =
                    Some (View.join (View.join (TView.rel (Local.tview local) l)
                                               p_rel.(View.unwrap))
                                    (View.singleton_ur l (f_to b))) ⟫ /\
           ((⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) b ⟫ /\
             ⟪ PREL : p_rel = None ⟫) \/
            (exists p,
                ⟪ ISSP  : issued T p ⟫ /\
                ⟪ INRMW : (rf ⨾ rmw) p b ⟫ /\
             exists p_v,
                ⟪ P_VAL : val lab p = Some p_v ⟫ /\
                ⟪ P_INMEM : Memory.get l (f_to p) mem =
                            Some (f_from p, Message.mk p_v p_rel) ⟫))
       ⟫).

  Inductive sim_mode := sim_normal | sim_certification.
  
  Definition sim_state_helper smode thread
             (state state' : Language.state (thread_lts thread)) : Prop :=
      ⟪ STEPS : (step thread)＊ state state' ⟫ /\
      ⟪ TERMINAL : smode = sim_normal -> is_terminal state' ⟫ /\
      ⟪ TEH  : thread_restricted_execution G thread state'.(ProgToExecution.G) ⟫.

  Definition sim_state smode (C : actid -> Prop) thread
             (state : Language.state (thread_lts thread)) : Prop :=
    ⟪ PCOV : forall index , C (ThreadEvent thread index) <-> index < state.(eindex)⟫ /\
    exists state', sim_state_helper smode state state'.
  
Definition pln_rlx_eq tview :=
  ⟪ EQ_CUR : TimeMap.eq (View.pln (TView.cur tview)) (View.rlx (TView.cur tview)) ⟫ /\
  ⟪ EQ_ACQ : TimeMap.eq (View.pln (TView.acq tview)) (View.rlx (TView.acq tview)) ⟫ /\
  ⟪ EQ_REL :
    forall l, TimeMap.eq (View.pln (TView.rel tview l)) (View.rlx (TView.rel tview l)) ⟫.

Definition reserved_time f_to f_from I memory smode :=
  match smode with
  | sim_normal =>
    (* During normal simulation: for adding *)
    (⟪ MEM : message_to_event f_to f_from I memory ⟫ /\
     ⟪ TFRMW : forall x y, I x -> I y -> ~ is_init y -> co x y ->
                           f_to x = f_from y -> (rf ⨾ rmw) x y ⟫)
  | sim_certification => 
    (* During certification: for splitting *)
    (⟪ FOR_SPLIT  : ⦗ set_compl I ⦘ ⨾ (immediate co) ⊆ sb ⟫ /\
     ⟪ RMW_ISSUED : codom_rel rmw ⊆₁ I ⟫)
  end.

Definition memory_close tview memory :=
  ⟪ CLOSED_CUR :
    Memory.closed_timemap (View.rlx (TView.cur tview)) memory ⟫ /\
  ⟪ CLOSED_ACQ :
    Memory.closed_timemap (View.rlx (TView.acq tview)) memory ⟫ /\
  ⟪ CLOSED_REL :
    forall loc,
      Memory.closed_timemap (View.rlx (TView.rel tview loc)) memory ⟫.

Definition simrel_common
           (PC : Configuration.t)
           (T : trav_config)
           (f_to f_from : actid -> Time.t)
           (smode : sim_mode) :=
  let memory := PC.(Configuration.memory) in
  let threads := PC.(Configuration.threads) in
  let sc_view := PC.(Configuration.sc) in
  ⟪ ACQEX : W_ex ⊆₁ W_ex_acq ⟫ /\
  ⟪ ALLRLX: E \₁ is_init ⊆₁ Rlx ⟫ /\
  ⟪ TCCOH : tc_coherent G sc T ⟫ /\
  ⟪ RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T ⟫ /\
  ⟪ RMWCOV : forall r w (RMW : rmw r w), covered T r <-> covered T w ⟫ /\

  ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
    exists langst, IdentMap.find (tid e) threads = Some langst ⟫ /\

  ⟪ PROM_IN_MEM :
     forall thread' langst local
            (TID : IdentMap.find thread' threads = Some (langst, local)),
           Memory.le local.(Local.promises) memory ⟫ /\

  ⟪ FCOH: f_to_coherent (issued T) f_to f_from ⟫ /\

  ⟪ SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T ⟫ /\ 
  ⟪ SC_REQ : smode = sim_normal -> 
         forall (l : Loc.t),
         max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\

  ⟪ RESERVED_TIME: reserved_time f_to f_from (issued T) memory smode ⟫ /\
                    
  ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory ⟫ /\
  ⟪ FUTURE : Memory.future Memory.init memory ⟫.

Definition simrel_thread_local
           (PC : Configuration.t)
           (thread : thread_id)
           (T : trav_config)
           (f_to f_from : actid -> Time.t)
           (smode : sim_mode) :=
  let memory := PC.(Configuration.memory) in
  let threads := PC.(Configuration.threads) in
  exists state local,
    ⟪ TNNULL : thread <> BinNums.xH ⟫ /\
    ⟪ GPC : wf_thread_state thread state ⟫ /\
    ⟪ XACQIN : rmw_is_xacq_instrs state.(instrs) ⟫ /\
    ⟪ LLH : IdentMap.find thread threads =
             Some (existT _ (thread_lts thread) state, local) ⟫ /\
    ⟪ PROM_DISJOINT :
        forall thread' langst' local'
               (TNEQ : thread <> thread')
               (TID' : IdentMap.find thread' threads = Some (langst', local')),
        forall loc to,
          Memory.get loc to local .(Local.promises) = None \/
          Memory.get loc to local'.(Local.promises) = None ⟫ /\

    ⟪ SIM_PROM : sim_prom thread T f_to f_from local.(Local.promises) ⟫ /\
    ⟪ SIM_MEM : sim_mem T f_to f_from thread local memory ⟫ /\
    ⟪ SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread ⟫ /\
    ⟪ PLN_RLX_EQ : pln_rlx_eq local.(Local.tview) ⟫ /\
    ⟪ MEM_CLOSE : memory_close local.(Local.tview) memory ⟫ /\
    ⟪ STATE : @sim_state smode (covered T) thread state ⟫.

Definition simrel_thread
           (PC : Configuration.t)
           (thread : thread_id)
           (T : trav_config)
           (f_to f_from : actid -> Time.t)
           (smode : sim_mode) :=
  ⟪ COMMON : simrel_common PC T f_to f_from smode ⟫ /\
  ⟪ LOCAL  : simrel_thread_local PC thread T f_to f_from smode ⟫.

Definition simrel
           (PC : Configuration.t) (T : trav_config) (f_to f_from : actid -> Time.t) :=
  ⟪ COMMON : simrel_common PC T f_to f_from sim_normal ⟫ /\
  ⟪ THREADS : forall thread (TP : IdentMap.In thread PC.(Configuration.threads)),
      simrel_thread_local PC thread T f_to f_from sim_normal ⟫.

  Lemma prev_next e e' (SB : sb e e')
        (T : trav_config)
        (NEXT : next G (covered T) e')
        (NCOV : forall e'', sb e e'' -> tid e'' = tid e' -> ~ covered T e'') :
    immediate sb e e'.
  Proof.
    red; splits; eauto.
    red in NEXT; unfold dom_cond in *; unfolder in *; desf.
    ins; eapply NCOV; eauto 10.
    hahn_rewrite sb_tid_init' in R2.
    hahn_rewrite no_sb_to_init in R1.
    unfold same_tid in *; unfolder in *; desf.
  Qed.

  Lemma rel_le_cur PC thread T f_to l langst local
        (SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) thread)
        (TID : IdentMap.find thread PC.(Configuration.threads) = Some (langst, local)) :
    TimeMap.le (View.rlx (TView.rel (Local.tview local) l))
               (View.rlx (TView.cur (Local.tview local))).
  Proof.
    cdes SIM_TVIEW.
    intros l'.
    specialize (CUR l').
    specialize (REL l l').
    unfold LocFun.find in *.
    set (srel := t_rel G sc thread l' l (covered T)).
    set (scur := t_cur G sc thread l' (covered T)).
    assert (srel ⊆₁ scur) as SS.
    { unfold scur, srel.
      intros x H.
      unfold t_rel in H; unfold t_cur.
      eapply dom_rel_mori; [|apply H].
      unfold c_rel, c_cur.
      rewrite inclusion_seq_eqv_l.
        by rewrite inclusion_seq_eqv_l. }
    cdes REL.
    destruct MAX as [[MAX MAX'] | MAX].
    { rewrite MAX'. apply Time.bot_spec. }
    desc.
    etransitivity; [apply LB'|].
    cdes CUR.
    apply UB0.
    destruct INam as [|INam]; [by apply SS|].
    destruct (classic (l' = l)) as [LL|NLL]; subst.
    2: by rewrite Loc.eq_dec_neq in INam; desf.
    rewrite Loc.eq_dec_eq in INam.
    destruct INam as [[[X Y] Z] U].
    red. exists a_max.
    red. hahn_rewrite <- seqA.
    apply seq_eqv_r. split; auto.
    apply seq_eqv_r. split; [|by left].
      by apply urr_refl.
  Qed.
End SimRel.