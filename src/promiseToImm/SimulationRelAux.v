From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import TView View Time Event Cell Thread Memory Configuration.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_bob imm_s_ppo.

Require Import PArith.
Require Import CombRelations.
Require Import TraversalConfig.
Require Import Traversal.
Require Import Setoid.
Require Import MaxValue ViewRel.
Require Import Event_imm_promise.
Require Import SimulationRel.
Require Import SimState.
Require Import ViewRelHelpers.
Require Import MemoryAux.

Set Implicit Arguments.

Section Aux.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.

Notation "'acts'" := G.(acts).
Notation "'co'" := G.(co).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'rmw'" := G.(rmw).
Notation "'lab'" := G.(lab).
Notation "'msg_rel'" := (msg_rel G sc).
Notation "'urr'" := (urr G sc).
Notation "'release'" := G.(release).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_'" := (fun l => W ∩₁ Loc_ l).
(* Notation "'RW'" := (fun x => R x \/ W x). *)
Notation "'FR'" := (fun x => F x \/ R x).
Notation "'FW'" := (fun x => F x \/ W x).

Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Lemma interval_disjoint_imm_le a b c d (LE : Time.le b c):
  Interval.disjoint (a, b) (c, d).
Proof using.
  red; ins.
  destruct LHS as [LFROM LTO].
  destruct RHS as [RFROM RTO]; simpls.
  eapply Time.lt_strorder.
  eapply TimeFacts.le_lt_lt.
  2: by apply RFROM.
  etransitivity; [by apply LTO|].
  done.
Qed.

Definition closedness_preserved memory memory' :=
  forall view,
    Memory.closed_timemap view memory ->
    Memory.closed_timemap view memory'.

Lemma closedness_preserved_id memory :
  closedness_preserved memory memory.
Proof using. by intros view. Qed.

Lemma closedness_preserved_add memory memory'
      loc from to val rel
      (ADD : Memory.add memory loc from to val rel memory'):
  closedness_preserved memory memory'.
Proof using.
  intros view CP. red.
  intros loc'.
  erewrite Memory.add_o; eauto.
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to)) as [[A B]|NEQ]; simpls.
  subst; eexists; eexists; eexists; eauto.
Qed.

Lemma closedness_preserved_split memory memory'
      loc from to to' val val' rel rel'
      (SPLIT : Memory.split memory loc from to to' val val' rel rel' memory'):
  closedness_preserved memory memory'.
Proof using.
  intros view CP. red.
  intros loc'.
  erewrite Memory.split_o; eauto.
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to)) as [[A B]|NEQ]; simpls.
  { eexists; eexists; eexists; eauto. }
  destruct (loc_ts_eq_dec (loc', view loc') (loc, to')) as [[A B]|NEQ']; simpls.
  eexists; eexists; eexists; eauto.
Qed.

Lemma tview_closedness_preserved_add tview memory memory'
      loc from to val rel
      (ADD : Memory.add memory loc from to val rel memory')
      (MEM_CLOSE : memory_close tview memory) :
  memory_close tview memory'.
Proof using.
  red; splits; ins.
  all: eapply closedness_preserved_add; eauto.
  all: by apply MEM_CLOSE.
Qed.

Lemma tview_closedness_preserved_split tview memory memory'
      loc from to to' val val' rel rel'
      (SPLIT : Memory.split memory loc from to to' val val' rel rel' memory')
      (MEM_CLOSE : memory_close tview memory) :
  memory_close tview memory'.
Proof using.
  red; splits; ins.
  all: eapply closedness_preserved_split; eauto.
  all: by apply MEM_CLOSE.
Qed.

Lemma sim_msg_f_issued f_to f_to' T rel b 
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISS : issued T b)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (SIMMEM : sim_msg G sc f_to b rel) :
  sim_msg G sc f_to' b rel.
Proof using WF.
  red; red in SIMMEM.
  intros l; specialize (SIMMEM l).
  eapply max_value_new_f; eauto.
  intros x [H|H].
  2: by desf; apply (ISSEQ_TO  b ISS).
  assert (issued T x) as ISSX.
  2: by apply (ISSEQ_TO  x ISSX).
  eapply (msg_rel_issued WF IMMCON TCCOH); eauto;
      eexists; apply seq_eqv_r; split; eauto.
Qed.

Lemma sim_mem_helper_f_issued f_to f_to' T rel b from v
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISS : issued T b)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (HELPER : sim_mem_helper G sc f_to b from v rel) :
  sim_mem_helper G sc f_to' b from v rel.
Proof using WF.
  red; red in HELPER; desc.
  rewrite (ISSEQ_TO b ISS).
  splits; auto.
  eapply sim_msg_f_issued; eauto.
Qed.

Lemma sim_mem_covered_mori T T' f_to f_from threads thread memory
      (TCCOH : tc_coherent G sc T)
      (ISSEQ : issued T ≡₁ issued T')
      (COVIN : covered T ⊆₁ covered T')
      (SIMMEM : sim_mem G sc T f_to f_from threads thread memory) :
  sim_mem G sc T' f_to f_from threads thread memory.
Proof using.
  red in SIMMEM.
  red; splits.
  edestruct SIMMEM as [rel]; eauto; desc.
  { by apply ISSEQ. }
  exists rel. splits; auto. 
  intros TIDB NCOV.
  destruct H1; auto; split; auto.
  destruct H0 as [p_rel]; desc.
  exists p_rel; splits; auto.
  desf; [left; split; auto|right].
  { intros HH; apply NINRMW. generalize HH.
    generalize ISSEQ. basic_solver 10. }
  exists p; splits; auto.
  { by apply ISSEQ. }
  eexists; split; eauto.
Qed.

Lemma sim_mem_f_issued f_to f_from f_to' f_from' T threads thread memory
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMMEM : sim_mem G sc T f_to f_from threads thread memory) :
  sim_mem G sc T f_to' f_from' threads thread memory.
Proof using WF.
  red in SIMMEM.
  red; splits.
  edestruct SIMMEM as [rel]; eauto; desc.
  exists rel.
  rewrite (ISSEQ_TO   b ISSB); rewrite (ISSEQ_FROM b ISSB).
  splits; auto. 
  { eapply sim_mem_helper_f_issued; eauto. }
  ins. destruct H1; auto; split; auto.
  destruct H2 as [p_rel]; desc.
  exists p_rel; splits; auto.
  desf; [by left|right].
  exists p; splits; auto.
  eexists; split; eauto.
  rewrite (ISSEQ_TO p); eauto.
  rewrite (ISSEQ_FROM p); eauto.
Qed.

Lemma rintervals_f_issued f_to f_from f_to' f_from' T memory smode
      (TCCOH : tc_coherent G sc T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (RINTERVALS : reserved_time G f_to f_from (issued T) memory smode):
  reserved_time G f_to' f_from' (issued T) memory smode.
Proof using.
  red. red in RINTERVALS.
  desf. desc.
  unnw; split.
  (* TODO: make a separate lemma. *)
  { red; ins.
    specialize (MEM l to from v rel MSG).
    destruct MEM as [MEM|MEM]; [by left; apply MEM|right].
    destruct MEM as [b H]; desc.
    exists b; splits; auto.
      by rewrite (ISSEQ_FROM b ISS).
        by rewrite (ISSEQ_TO b ISS). }
  intros x y ISSX ISSY NINIT COXY H.
  apply TFRMW; auto.
  rewrite <- (ISSEQ_FROM y ISSY).
  rewrite <- (ISSEQ_TO x ISSX).
  done.
Qed.

Lemma sim_prom_f_issued f_to f_from f_to' f_from' T thread promises 
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMPROM : sim_prom G sc thread T f_to f_from promises) :
  sim_prom G sc thread T f_to' f_from' promises.
Proof using WF.
  red; ins. edestruct SIMPROM as [b]; eauto; desc.
  exists b; splits; auto.
  { by rewrite (ISSEQ_FROM b ISS). }
  { by rewrite (ISSEQ_TO b ISS). }
  eapply sim_mem_helper_f_issued; eauto.
Qed.

Lemma f_to_coherent_f_issued f_to f_from f_to' f_from' T
      (TCCOH : tc_coherent G sc T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (FCOH: f_to_coherent G (issued T) f_to f_from):
  f_to_coherent G (issued T) f_to' f_from'.
Proof using WF.
  cdes TCCOH.
  cdes FCOH. red; splits; ins.
  all: try (rewrite (ISSEQ_TO x));
    try (rewrite (ISSEQ_FROM x)); try (rewrite (ISSEQ_FROM y)); auto.
  all: eapply w_covered_issued; eauto; split.
  2,4: by apply TCCOH.
  all: apply WF.(init_w).
  all: by destruct H.
Qed.

Lemma sc_view_f_issued f_to f_to' T sc_view
      (IMMCON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (SC_REQ : forall l,
          max_value f_to (S_tm G l (covered T)) (LocFun.find l sc_view)):
  forall l,
    max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view).
Proof using WF.
  intros l; specialize (SC_REQ l).
  eapply max_value_new_f; eauto.
  intros x H; apply ISSEQ_TO.
  red in H.
  eapply S_tm_covered; eauto.
Qed.

Lemma simrel_common_f_issued T f_to f_from f_to' f_from' PC smode
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMREL: simrel_common G sc PC T f_to f_from smode):
  simrel_common G sc PC T f_to' f_from' smode.
Proof using WF.
  cdes SIMREL.
  red; splits; auto.
  { by eapply f_to_coherent_f_issued; eauto. }
  { by ins; eapply sc_view_f_issued; eauto. }
    by eapply rintervals_f_issued; eauto.
Qed.

Lemma simrel_thread_local_f_issued thread T f_to f_from f_to' f_from' PC smode
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMREL: simrel_thread_local G sc PC thread T f_to f_from smode):
  simrel_thread_local G sc PC thread T f_to' f_from' smode.
Proof using WF.
  cdes SIMREL.
  red; splits; auto.
  eexists; eexists; eexists; splits; eauto.
  { by eapply sim_prom_f_issued; eauto. }
  { by eapply sim_mem_f_issued; eauto. }
  eapply sim_tview_f_issued; eauto.
Qed.

Lemma simrel_thread_f_issued thread T f_to f_from f_to' f_from' PC smode
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMREL: simrel_thread G sc PC thread T f_to f_from smode):
  simrel_thread G sc PC thread T f_to' f_from' smode.
Proof using WF.
  cdes SIMREL. cdes COMMON. cdes LOCAL.
  red; splits; auto.
  { eapply simrel_common_f_issued; eauto. }
  eapply simrel_thread_local_f_issued; eauto.
Qed.

Lemma simrel_f_issued T f_to f_from f_to' f_from' PC
      (TCCOH : tc_coherent G sc T)
      (IMMCON : imm_consistent G sc)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e)
      (ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e)
      (SIMREL: simrel G sc PC T f_to f_from):
  simrel G sc PC T f_to' f_from'.
Proof using WF.
  cdes SIMREL. red; splits.
  { eapply simrel_common_f_issued; eauto. }
  ins. eapply simrel_thread_local_f_issued; eauto.
Qed.

Lemma max_value_le_issued locw w wprev s ts T f_to f_from
      (IMMCOH : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (FCOH : f_to_coherent G (issued T) f_to f_from)
      (LOC : loc lab w = Some locw)
      (NISS : ~ issued T w)
      (COIMM : immediate (⦗ issued T ⦘ ⨾ co) wprev w)
      (MAXVAL : max_value f_to s ts)
      (LOCS : s ⊆₁ Loc_ locw)
      (ISSS : s ⊆₁ issued T)
      (NOCO : ⦗ eq w ⦘ ⨾ co ⨾ ⦗ s ⦘ ≡ ∅₂) :
  Time.le ts (f_to wprev).
Proof using WF.
  red in MAXVAL. desc.
  destruct MAX as [[Y1 Y2]|[a_max Y1]].
  { rewrite Y2. apply Time.bot_spec. }
  desc.
  destruct (classic (a_max = wprev)) as [|NEQ]; [by subst|].
  etransitivity; eauto.
  apply Time.le_lteq. left.
  assert (issued T wprev) as ISSWP.
  { destruct COIMM as [CO _].
    apply seq_eqv_l in CO. desf. }
  assert (co wprev w) as COWP.
  { destruct COIMM as [CO _].
    apply seq_eqv_l in CO. desf. }
  assert (E w) as EW.
  { apply (dom_r WF.(wf_coE)) in COWP. 
    apply seq_eqv_r in COWP. desf. }
  assert (W w) as WW.
  { apply (dom_r WF.(wf_coD)) in COWP. 
    apply seq_eqv_r in COWP. desf. }
  assert (E wprev) as EWP.
  { eapply issuedE; eauto. }
  assert (W wprev) as WWP.
  { apply TCCOH in ISSWP. apply ISSWP. }
  assert (loc lab wprev = Some locw) as LOCWP.
  { rewrite <- LOC. by apply WF.(wf_col). }
  assert (issued T a_max) as ISSA.
  { by apply ISSS. }
  assert (E a_max) as EA.
  { eapply issuedE; eauto. }
  assert (is_w lab a_max) as WA.
  { apply ISSS in INam. apply TCCOH in INam. apply INam. }
  eapply f_to_co_mon; eauto.
  edestruct WF.(wf_co_total) as [CO|CO].
  3: by apply NEQ.
  3: done.
  1,2: split; [split|]; auto.
  exfalso.
  assert (w <> a_max) as WANEQ.
  { intros H. desf. }
  assert (co w a_max) as COWA.
  { edestruct WF.(wf_co_total) as [CO'|CO'].
    3: by apply WANEQ.
    3: done.
    1,2: split; [split|]; auto.
    { rewrite LOC. by apply LOCS. }
    exfalso.
    eapply COIMM.
    all: apply seq_eqv_l; split; eauto. }
  eapply NOCO. apply seq_eqv_l. split; eauto.
  apply seq_eqv_r. split; eauto.
Qed.

Lemma exists_time_interval f_to f_from T PC w locw valw langst local smode
      (IMMCON : imm_consistent G sc)
      (ACQEX : W_ex ⊆₁ W_ex_acq)
      (TCCOH : tc_coherent G sc T)
      (WNISS : ~ issued T w)
      (WISSUABLE : issuable G sc T w)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (FCOH : f_to_coherent G (issued T) f_to f_from)
      (RESERVED_TIME:
         reserved_time G f_to f_from (issued T) PC.(Configuration.memory) smode)
      (FUTURE : Memory.future Memory.init (Configuration.memory PC))
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) (tid w))
      (PLN_RLX_EQ : pln_rlx_eq local.(Local.tview))
      (MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let memory := PC.(Configuration.memory) in
  exists p_rel,
    (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
     ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap)) memory ⟫) /\
     ⟪ P_REL_CH :
         (⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
          ⟪ PREL : p_rel = None ⟫) \/
         (exists p,
             ⟪ EP  : E p ⟫ /\
             ⟪ ISSP  : issued T p ⟫ /\
             ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
             ⟪ P_LOC : loc lab p = Some locw ⟫ /\
             ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
           exists p_v,
             ⟪ P_VAL : val lab p = Some p_v ⟫ /\
             ⟪ P_INMEM : Memory.get locw (f_to p) memory =
                         Some (f_from p, Message.mk p_v p_rel) ⟫)⟫ /\
  (⟪ FOR_ISSUE :
     exists f_to' f_from' promises' memory',
     let rel'' :=
         if is_rel lab w
         then (TView.cur (Local.tview local))
         else (TView.rel (Local.tview local) locw)
     in
     let rel' := (View.join (View.join rel'' p_rel.(View.unwrap))
                            (View.singleton_ur locw (f_to' w))) in
     ⟪ PADD :
         Memory.add local.(Local.promises) locw (f_from' w) (f_to' w) valw
                                           (Some rel') promises' ⟫ /\
     ⟪ MADD :
         Memory.add memory locw (f_from' w) (f_to' w) valw
                    (Some rel') memory' ⟫ /\
    
     ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\
     ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to' w) ⟫ /\

     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e ⟫ /\
     ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\
     ⟪ FCOH : f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\
     ⟪ RESERVED_TIME :
         reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' smode ⟫ /\

     ⟪ HELPER :
         sim_mem_helper
           G sc f_to' w (f_from' w) valw
           (View.join (View.join (if is_rel lab w
                                  then (TView.cur (Local.tview local))
                                  else (TView.rel (Local.tview local) locw))
                                 p_rel.(View.unwrap))
                      (View.singleton_ur locw (f_to' w))) ⟫
   ⟫ \/
   ⟪ FOR_SPLIT :
     ⟪ NREL : ~ Rel w ⟫ /\
     ⟪ SMODE : smode = sim_certification ⟫ /\

     exists ws valws relws f_to' f_from' promises' memory',
     let rel' := (View.join (View.join (TView.rel (Local.tview local) locw)
                                       p_rel.(View.unwrap))
                            (View.singleton_ur locw (f_to' w))) in
      
     ⟪ WSISS  : issued T ws ⟫ /\
     ⟪ WSNCOV : ~ covered T ws ⟫ /\
     ⟪ WSVAL : val lab ws = Some valws ⟫ /\

     ⟪ SBWW : sb w ws ⟫ /\
     ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
     ⟪ COWW : co w ws ⟫ /\

     ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
     ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

     ⟪ WSPROM : Memory.get locw (f_to ws) (Local.promises local) =
                Some (f_from ws, Message.mk valws relws)⟫ /\
     ⟪ WSMEM : Memory.get locw (f_to ws) memory =
               Some (f_from ws, Message.mk valws relws)⟫ /\

     ⟪ PADD :
        Memory.split (Local.promises local)
                     locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     (Some rel') relws promises' ⟫ /\
     ⟪ MADD :
        Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     (Some rel') relws memory' ⟫ /\

     ⟪ REL_VIEW_LT : Time.lt (View.rlx (TView.rel (Local.tview local) locw)
                                       locw) (f_to' w) ⟫ /\
     ⟪ REL_VIEW_LE : Time.le (View.rlx rel' locw) (f_to' w) ⟫ /\

     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
     ⟪ ISSEQ_FROM :
        forall e (ISS: (issued T \₁ eq ws) e), f_from' e = f_from e ⟫ /\
     ⟪ FCOH : f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\
     ⟪ RESERVED_TIME :
            reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' sim_certification ⟫ /\

     ⟪ HELPER :
         sim_mem_helper
           G sc f_to' w (f_from' w) valw
           (View.join (View.join (TView.rel (Local.tview local) locw)
                                 p_rel.(View.unwrap))
                      (View.singleton_ur locw (f_to' w))) ⟫
   ⟫).
Proof using WF.
  assert (Memory.inhabited PC.(Configuration.memory)) as INHAB.
  { by apply inhabited_future_init. }

  assert (W w) as WW.
  { apply WISSUABLE. }

  assert (E w) as EW.
  { apply WISSUABLE. }
  
  assert (~ covered T w) as WNCOV.
  { intros COV. apply WNISS.
      by eapply w_covered_issued; eauto; split. }

  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV.
    apply TCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  (* cdes SIMREL_THREAD. *)
  (* rewrite LLH in TID. inv TID. *)

  destruct langst as [lang state].

  assert
    (exists p_rel,
        (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
         ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap))
                                              PC.(Configuration.memory) ⟫) /\
        ((⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
          ⟪ PREL : p_rel = None ⟫) \/
         (exists p,
             ⟪ EP  : E p ⟫ /\
             ⟪ ISSP  : issued T p ⟫ /\
             ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
             ⟪ P_LOC : loc lab p = Some locw ⟫ /\
             ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
          exists p_v,
            ⟪ P_VAL : val lab p = Some p_v ⟫ /\
            ⟪ P_INMEM : Memory.get locw (f_to p) PC.(Configuration.memory) =
                        Some (f_from p, Message.mk p_v p_rel) ⟫)))
    as [p_rel PREL].
  { destruct (classic (codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w)) as [[p CD]|].
    2: { eexists; split; [|by left; splits; eauto].
         simpls. split; auto. by apply Memory.closed_timemap_bot. }
    apply seq_eqv_l in CD; destruct CD as [PISS CD].
    assert (E p) as EP.
    { apply TCCOH in PISS; apply PISS. }
    assert (W p) as WP.
    { apply (dom_l WF.(wf_rfrmwD)) in CD.
      apply seq_eqv_l in CD. desf. }
    assert (loc lab p = Some locw) as PLOC.
    { rewrite <- LOC. by apply wf_rfrmwl. }
    assert (exists p_v, val lab p = Some p_v) as [p_v PVAL].
    { unfold val. type_solver. }
    edestruct SIM_MEM as [p_rel REL]; simpls; desc.
    all: eauto.
    exists p_rel; split; [auto|right; exists p; splits; eauto].
    apply HELPER. }
  exists p_rel; split; [by apply PREL|split; [by apply PREL|]]. desc.

  assert (forall f_to' f_from'
                 (ISSEQ_TO : forall e (ISS: issued T e), f_to' e = f_to e)
                 (FCOH : f_to_coherent G (issued T ∪₁ eq w) f_to' f_from'),
             sim_mem_helper
               G sc f_to' w (f_from' w) valw
               (View.join (View.join (if is_rel lab w
                                      then (TView.cur (Local.tview local))
                                      else (TView.rel (Local.tview local) locw))
                                     p_rel.(View.unwrap))
                          (View.singleton_ur locw (f_to' w)))) as SIM_HELPER.
  { ins. red; splits; auto.
    { left. apply FCOH0; auto. by right. }
    red; ins.
    eapply sim_tview_f_issued in SIM_TVIEW; eauto.
    cdes SIM_TVIEW. red in REL.
    unfold LocFun.find, TimeMap.join in *.
    eapply (@max_value_le_join _
              _ _
              (if Loc.eq_dec l locw
               then W ∩₁ (fun x => loc lab x = Some locw) ∩₁ Tid_ (tid w) ∩₁ covered T
               else ∅)).
    { intros x XX; destruct (Loc.eq_dec l locw); [subst|by desf].
      destruct XX as [[[WX LOCX] TIDX] COVX].
      eapply TimeFacts.lt_le_lt; [|apply Time.join_r].
      unfold TimeMap.singleton, LocFun.add; rewrite Loc.eq_dec_eq.
      eapply f_to_co_mon; eauto.
      3: by right.
      2: by left; apply (w_covered_issued TCCOH); split.
      apply coi_union_coe; left.
      apply w_sb_loc_w_in_coi; auto.
      { apply coherence_sc_per_loc. apply IMMCON. }
      apply seq_eqv_l; split; [done|].
      apply seq_eqv_r; split; [|done].
      split; [|by red; rewrite LOCX].
      edestruct same_thread as [[EQ|SB]|SB].
      { apply EW. }
      { apply TCCOH in COVX. apply COVX. }
      all: auto.
      { desf. }
      exfalso. apply TCCOH in COVX. destruct COVX as [[_ C] _].
      apply WNCOV. apply C. eexists; apply seq_eqv_r; eauto. }
    eapply max_value_same_set.
    2: { arewrite ((fun a : actid => msg_rel l a w \/ loc lab w = Some l /\ a = w) ≡₁
                   dom_rel (msg_rel l ⨾ ⦗ eq w ⦘) ∪₁
                   (fun x => loc lab x = Some l) ∩₁ eq w).
         { rewrite <- dom_rel_fun_alt. basic_solver. }
         rewrite set_unionA.
         rewrite (set_unionC ((fun x => loc lab x = Some l) ∩₁ eq w)).
         rewrite <- set_unionA.
         reflexivity. }
    cdes IMMCON.
    eapply max_value_same_set.
    2: by rewrite (msg_rel_alt2 WF TCCOH); eauto.
    eapply max_value_same_set.
    2: { arewrite ((if Rel w
                    then t_cur G sc (tid w) l (covered T)
                    else t_rel G sc (tid w) l locw (covered T)) ∪₁
                   dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ∪₁
                   Rel ∩₁ Loc_ l ∩₁ eq w ∪₁
                   (if Loc.eq_dec l locw
                    then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                    else ∅) ∪₁
                   Loc_ l ∩₁ eq w ≡₁
                   (if Rel w
                    then t_cur G sc (tid w) l (covered T)
                    else t_rel G sc (tid w) l locw (covered T)) ∪₁
                   dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ∪₁
                   (if Loc.eq_dec l locw
                    then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                    else ∅) ∪₁
                   Loc_ l ∩₁ eq w).
         2: reflexivity.
         basic_solver 40. }
    assert (max_value
              f_to' ((if Rel w
                      then t_cur G sc (tid w) l (covered T)
                      else t_rel G sc (tid w) l locw (covered T)) ∪₁
                     (if Loc.eq_dec l locw
                      then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T
                      else ∅))
              (View.rlx (if Rel w
                         then TView.cur (Local.tview local)
                         else TView.rel (Local.tview local) locw) l)) as JJ.
    { destruct (Rel w); simpls.
      eapply max_value_same_set; eauto.
      apply set_union_absorb_r.
      destruct (Loc.eq_dec l locw); simpls.
      unfold t_cur, c_cur.
      generalize (@urr_refl G sc locw).
      basic_solver 40. }
    assert (max_value f_to' (Loc_ l ∩₁ eq w) (TimeMap.singleton locw (f_to' w) l)) as KK.
    { unfold TimeMap.singleton, LocFun.add, LocFun.find.
      destruct (Loc.eq_dec l locw) as [|NEQ]; [subst|].
      { eapply max_value_same_set.
        { apply max_value_singleton; eauto. }
        basic_solver. }
      eapply max_value_same_set.
      { apply max_value_empty.
        intros x H. apply H. }
      basic_solver. }

    destruct PREL0 as [PP|PP]; desc; subst. 
    { eapply max_value_join; [ | by apply KK | reflexivity].
      assert ((⦗ W_ex ⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗eq w⦘ ≡ ∅₂) as TT.
      { split; [|done].
        rewrite ACQEX.
        intros x y H. hahn_rewrite <- seqA in H.
        apply seq_eqv_r in H; destruct H as [H]; subst.
        apply NINRMW. exists x. apply seq_eqv_l; split.
        { eapply wex_rfi_rfe_rmw_issuable_is_issued; eauto.
          exists y. hahn_rewrite <- seqA. apply seq_eqv_r; split; auto. }
        generalize H; unfold Execution.rfi, Execution.rfe.
        basic_solver. }
      assert ((if Rel w
               then t_cur G sc (tid w) l (covered T)
               else t_rel G sc (tid w) l locw (covered T)) ∪₁
              dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
              (if Rel w
               then t_cur G sc (tid w) l (covered T)
               else t_rel G sc (tid w) l locw (covered T))) as SS.
      { destruct (Rel w); simpls.
        rewrite t_cur_msg_rel_rfrmw; eauto.
        rewrite TT; basic_solver.
        rewrite t_rel_msg_rel_rfrmw; auto.
        arewrite (msg_rel l ⨾ (⦗W_ex⦘ ⨾ rfi ∪ rfe) ⨾ rmw ⨾ ⦗eq w⦘ ≡ ∅₂)
          by rewrite TT; basic_solver.
        basic_solver. }
      eapply max_value_same_set.
      2: { rewrite !seqA in SS. by rewrite SS. }
      simpls. unfold TimeMap.bot.
      rewrite time_join_bot_r.
      apply JJ. }
    edestruct SIM_MEM as [p_rel' H]; simpls; desc.
    { apply EP. }
    all: eauto.
    assert (dom_rel (msg_rel l ⨾ (rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁
                    dom_rel (msg_rel l ⨾ ⦗eq p⦘)) as YY.
    { rewrite <- dom_rel_eqv_dom_rel.
      arewrite (dom_rel ((rf ⨾ rmw) ⨾ ⦗eq w⦘) ≡₁ eq p); [|done].
      split.
      2: { generalize INRMW. basic_solver 30. }
      intros x [y H]. apply seq_eqv_r in H.
      eapply wf_rfrmwf; eauto; desf. }
    eapply max_value_same_set.
    2: { rewrite seqA in YY; by rewrite YY. }
    apply (@max_value_le_join _ _ _ (Loc_ l ∩₁ (eq p))).
    { intros x [XL]; subst. apply time_lt_join_r.
      unfold TimeMap.singleton, LocFun.add.
      assert (l = locw); subst.
      { erewrite wf_rfrmwl in XL; eauto.
        rewrite LOC in XL. inv XL. }
      rewrite Loc.eq_dec_eq. eapply f_to_co_mon; eauto.
      { eapply rfrmw_in_im_co; eauto. }
        by left.
        by right. }
    assert
    ((if Rel w then
      t_cur G sc (tid w) l (covered T)
      else t_rel G sc (tid w) l locw (covered T)) ∪₁
     dom_rel (msg_rel l ⨾ ⦗eq p⦘) ∪₁
     (if Loc.eq_dec l locw then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T else ∅) ∪₁
     Loc_ l ∩₁ eq w ∪₁ Loc_ l ∩₁ eq p ≡₁
     (if Rel w then
      t_cur G sc (tid w) l (covered T)
      else t_rel G sc (tid w) l locw (covered T)) ∪₁
     (if Loc.eq_dec l locw then W ∩₁ Loc_ locw ∩₁ Tid_ (tid w) ∩₁ covered T else ∅) ∪₁
     (dom_rel (msg_rel l ⨾ ⦗eq p⦘) ∪₁ Loc_ l ∩₁ eq p) ∪₁
     Loc_ l ∩₁ eq w) as YYY.
    { basic_solver 40. }
    eapply max_value_same_set; [| by apply YYY].
    eapply max_value_join; [ | by apply KK | reflexivity].
    eapply max_value_join; [by apply JJ | | reflexivity].
    rewrite INMEM in P_INMEM; inv P_INMEM.
    eapply sim_mem_helper_f_issued in HELPER; eauto.
    cdes HELPER. red in SIMMSG. unfold LocFun.find in SIMMSG.
    eapply max_value_same_set; [by apply SIMMSG|].
    basic_solver 10. }

  assert (forall f_to',
             View.wf (View.join (View.join (TView.rel (Local.tview local) locw)
                                       p_rel.(View.unwrap))
                                (View.singleton_ur locw (f_to' w)))) as REL_WF_2.
  { ins. constructor.
    unfold View.join; simpls.
    rewrite REL_PLN_RLX.
    cdes PLN_RLX_EQ. rewrite EQ_REL. 
    reflexivity. }

  assert (forall f_to',
             View.wf (View.join
                        (View.join
                           (if is_rel lab w
                            then (TView.cur (Local.tview local))
                            else (TView.rel (Local.tview local) locw))
                           p_rel.(View.unwrap))
                        (View.singleton_ur locw (f_to' w)))) as REL_WF_1.
  { ins.
    destruct (Rel w).
    2: by apply REL_WF_2.
    constructor.
    unfold View.join; simpls.
    rewrite REL_PLN_RLX.
    cdes PLN_RLX_EQ. rewrite EQ_CUR. 
    reflexivity. }
  
  destruct (classic (exists wnext, (co ⨾ ⦗ issued T ⦘) w wnext)) as [WNEXT|WNONEXT].
  { assert (exists wnext, immediate (co ⨾ ⦗ issued T ⦘) w wnext) as [wnext NIMMCO].
    { desc; eapply clos_trans_immediate2 in WNEXT.
      apply ct_begin in WNEXT; unfold seq in *; desc; eauto.
      generalize (co_trans WF); unfold transitive; basic_solver 21.
      generalize (co_irr WF); basic_solver 21.
      unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL.
      unfolder in REL; desc; eauto. }
    clear WNEXT.
    assert (issued T wnext /\ co w wnext) as [ISSNEXT CONEXT].
    { destruct NIMMCO as [H _]. apply seq_eqv_r in H; desf. }
    assert (E wnext /\ W wnext) as [ENEXT WNEXT].
    { by apply TCCOH. }
    assert (Loc_ locw wnext) as LOCNEXT.
    { apply WF.(wf_col) in CONEXT. by rewrite <- CONEXT. }
    assert (exists vnext, val lab wnext = Some vnext) as [vnext VNEXT].
    { unfold val, is_w in *. desf.
      all: eexists; eauto. }

    assert (exists wprev, immediate (⦗ issued T ⦘ ⨾ co) wprev w) as [wprev PIMMCO].
    { assert ((⦗ issued T ⦘ ⨾ co) (InitEvent locw) w) as WPREV.
      { assert (W (InitEvent locw)) as WI.
        { by apply init_w. }
        assert (E (InitEvent locw)) as EI.
        { apply wf_init; auto.
            by exists w; split. }
        assert (InitEvent locw <> w) as NEQ.
        { intros H; subst. desf. }
        assert (loc lab (InitEvent locw) = Some locw) as LI.
        { unfold loc. by rewrite WF.(wf_init_lab). }
        apply seq_eqv_l; split.
        { eapply w_covered_issued; eauto.
          split; [done |by apply TCCOH]. }
        edestruct WF.(wf_co_total).
        3: by apply NEQ.
        1,2: split; [split|]; auto.
        { by rewrite LOC. }
        { done. }
        exfalso. cdes IMMCON. eapply Cint.
        eexists; split.
        2: { apply r_step. by apply Execution_eco.co_in_eco; apply H. }
        apply sb_in_hb. apply init_ninit_sb; auto. }
      desc; eapply clos_trans_immediate2 in WPREV.
      apply ct_end in WPREV; unfold seq in *; desc; eauto.
      generalize (co_trans WF); unfold transitive; basic_solver 21.
      generalize (co_irr WF); basic_solver 21.
      unfolder; ins; desc; hahn_rewrite (dom_r (wf_coE WF)) in REL0.
      unfolder in REL0; desc; eauto. }

    assert (issued T wprev /\ co wprev w) as [ISSPREV COPREV].
    { destruct PIMMCO as [H _]. apply seq_eqv_l in H; desf. }
    assert (E wprev /\ W wprev) as [EPREV WPREV].
    { by apply TCCOH. }

    assert (wnext <> w) as NEQNEXT.
    { intros H; subst. by apply WF.(co_irr) in CONEXT. }
    assert (wprev <> w) as NEQPREV.
    { intros H; subst. by apply WF.(co_irr) in COPREV. }

    assert (loc lab wprev = Some locw) as PLOC.
    { rewrite <- LOC. by apply WF.(wf_col). }
    
    assert (forall y (RFRMW : (rf ⨾ rmw ⨾ ⦗ issued T ⦘) w y), y = wnext) as NRFRMW.
    { ins. apply seqA in RFRMW.
      apply seq_eqv_r in RFRMW; destruct RFRMW as [RFRMW ISSY].
      eapply rfrmw_in_im_co in RFRMW; eauto. destruct RFRMW as [CO IMM].
      destruct (classic (y = wnext)) as [|NEQ]; auto.
      exfalso.
      edestruct WF.(wf_co_total).
      3: by apply NEQ.
      1,2: split; [split|]; eauto.
      { apply WF.(wf_coE) in CO. apply seqA in CO.
        apply seq_eqv_r in CO; desf. }
      { apply WF.(wf_coD) in CO. apply seqA in CO.
        apply seq_eqv_r in CO; desf. }
      { erewrite <- (WF.(wf_col) w y); [|by apply CO].
          by rewrite LOC. }
      2: by apply (IMM wnext).
      eapply NIMMCO.
      all: apply seq_eqv_r; split; eauto. }

    assert (forall z (RFRMW : (⦗ issued T ⦘ ⨾ rf ⨾ rmw) z w), z = wprev) as PRFRMW.
    { ins. apply seq_eqv_l in RFRMW; destruct RFRMW as [ISSZ RFRMW].
      eapply rfrmw_in_im_co in RFRMW; eauto. destruct RFRMW as [CO IMM].
      destruct (classic (z = wprev)) as [|NEQ]; auto.
      exfalso.
      edestruct WF.(wf_co_total).
      3: by apply NEQ.
      1,2: split; [split|]; eauto.
      1,2: by apply TCCOH in ISSZ; apply ISSZ.
      { erewrite (WF.(wf_col) z w); [|by apply CO].
          by rewrite LOC. }
      { by apply (IMM wprev). }
      eapply PIMMCO. all: apply seq_eqv_l; eauto. }
    red in RESERVED_TIME.
    destruct smode; desc.
    { left. (* ISSUING *)
      set (A := (rf ⨾ rmw) w wnext).
      assert (exists n_to,
                 ⟪ NTO : (n_to = f_from wnext /\ A) \/
                          (n_to = Time.middle (f_to wprev) (f_from wnext) /\ ~A) ⟫)
        as [n_to NTO].
      { by destruct (classic A) as [H|H]; eexists; [left|right]. }
      set (f_to' := upd f_to w n_to).
      exists f_to'.

      set (B := (rf ⨾ rmw) wprev w).
      assert (exists n_from,
                 ⟪ NFROM : (n_from = f_to wprev /\ B) \/
                            (n_from = Time.middle (f_to wprev) n_to /\ ~B) ⟫)
        as [n_from NFROM].
      { by destruct (classic B) as [H|H]; eexists; [left|right]. }
      set (f_from' := upd f_from w n_from).
      exists f_from'.

      assert (co wprev wnext) as COPN.
      { eapply WF.(co_trans); eauto. }

      assert (~ is_init wnext) as NINITWNEXT.
      { apply no_co_to_init in CONEXT; auto.
        2: { apply coherence_sc_per_loc. apply IMMCON. }
        apply seq_eqv_r in CONEXT. desf. }

      assert (Time.lt (f_to wprev) (f_from wnext)) as NPLT.
      { assert (Time.le (f_to wprev) (f_from wnext)) as H.
        { apply FCOH; auto. }
        apply Time.le_lteq in H. destruct H as [|H]; [done|exfalso].
        apply TFRMW in H; auto.
        eapply rfrmw_in_im_co in H; eauto.
          by eapply H; [apply COPREV|]. }

      assert (Time.lt (f_to wprev) n_to) as PREVNLT.
      { destruct NTO as [[N1 N2]|[N1 N2]]; subst; [done|].
          by apply Time.middle_spec. }

      assert (Time.le (f_to wprev) n_from) as PREVFROMLE.
      { destruct NFROM as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
        apply Time.le_lteq; left. by apply Time.middle_spec. }

      assert (Time.le n_to (f_from wnext)) as TONEXTLE.
      { destruct NTO as [[N1 N2]|[N1 N2]]; subst; [reflexivity|].
        apply Time.le_lteq; left. by apply Time.middle_spec. }

      assert (Time.lt (f_from' w) (f_to' w)) as NLT.
      { unfold f_to', f_from'; rewrite !upds.
        destruct NTO as [[NTO1 NTO2]|[NTO1 NTO2]];
          destruct NFROM as [[NFROM1 NFROM2]|[NFROM1 NFROM2]]; subst; auto.
        all: by apply Time.middle_spec. }

      assert (forall to from msg,
                 Memory.get locw to (Configuration.memory PC) =
                 Some (from, msg) ->
                 Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
      { unfold f_to', f_from'; rewrite !upds.
        ins; red; ins. destruct LHS. destruct RHS. simpls.
        destruct msg as [hval hrel].
        apply MEM in H.
        destruct H as [[H1 H2]|H]; subst.
        { apply Time.le_lteq in TO0. destruct TO0 as [TT|]; subst.
          { by apply time_lt_bot in TT. }
            by apply Time.lt_strorder in FROM0. }
        destruct H as [h H]; desc.
        rewrite <- FROM1 in *. rewrite <- TO1 in *.
        assert (W h) as WH.
        { by apply TCCOH. }
        assert (co^? h wprev \/ co^? wnext h) as CO.
        { destruct (classic (h = wprev)) as [|PNEQ]; subst.
          { by left; left. }
          destruct (classic (h = wnext)) as [|NNEQ]; subst.
          { by right; left. }
          edestruct WF.(wf_co_total) as [|LIMM].
          3: by apply PNEQ.
          1,2: split; [split|]; eauto.
          { by left; right. }
          right; right.
          edestruct WF.(wf_co_total) as [LHN|].
          3: by apply NNEQ.
          1,2: split; [split|]; eauto.
          2: done.
          exfalso.
          destruct (classic (h = w)) as [|WNEQ]; [by desf|].
          edestruct WF.(wf_co_total) as [LHW|LWH].
          3: by apply WNEQ.
          1,2: split; [split|]; eauto.
          2: eapply NIMMCO; apply seq_eqv_r; split.
          eapply PIMMCO; apply seq_eqv_l; split.
          all: eauto. }
        destruct CO as [CO|CO].
        { assert (Time.le (f_to h) (f_to wprev)) as HH.
          { destruct CO as [|CO]; [subst; reflexivity|].
            apply Time.le_lteq; left.
            eapply f_to_co_mon; eauto. }
          assert (Time.le (f_to h) n_from) as HNLE.
          { by etransitivity; [by apply HH|]. }
          eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; [by apply FROM|].
            by etransitivity; [by apply TO0|]. }
        assert (Time.le (f_from wnext) (f_from h)) as HH.
        { destruct CO as [|CO]; [subst; reflexivity|].
          apply Time.le_lteq; left.
          eapply f_from_co_mon; eauto. }
        assert (Time.le n_to (f_from h)) as HNLE.
        { by etransitivity; [|by apply HH]. }
        eapply Time.lt_strorder.
        eapply TimeFacts.le_lt_lt; [by apply TO|].
          by eapply TimeFacts.le_lt_lt; [by apply HNLE|]. }

      edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) valw)
        as [promises' PADD].
      3: by apply View.opt_wf_some; apply REL_WF_1.
      { ins. eapply DISJOINT.
        eapply PROM_IN_MEM; eauto. }
      { done. }

      edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) valw)
        as [memory' MADD].
      3: by apply View.opt_wf_some; apply REL_WF_1.
      { apply DISJOINT. }
      { done. }
      
      assert (f_to_coherent G (issued T ∪₁ eq w) f_to' f_from') as FCOH_NEW.
      { unfold f_to', f_from'; red; splits.
        { ins; rewrite updo; [by apply FCOH|].
          intros Y; subst. destruct H. desf. }
        { ins; rewrite updo; [by apply FCOH|].
          intros Y; subst. destruct H. desf. }
        { intros x [ISS|]; subst.
          { rewrite !updo; [by apply FCOH | |].
            all: by intros Y; subst. }
          unfold f_to', f_from' in *.
            by rewrite !upds in *. }
        { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
          all: try rewrite !upds.
          all: try rewrite !updo.
          all: try by intros H; subst.
          { by apply FCOH. }
          { (* TODO: generalize to lemma! *)
            apply (wf_coD WF) in CO.
            apply seq_eqv_l in CO; destruct CO as [WX CO].
            apply seq_eqv_r in CO; destruct CO as [CO WY].
            unfold is_w in WX; destruct (lab x) eqn:LAB; desc; try by desf.
            edestruct SIM_MEM.
            3,4: by unfold loc, val; rewrite LAB; eauto.
            { apply (wf_coE WF) in CO.
              apply seq_eqv_l in CO; desf. }
            all: eauto.
            assert (co^? x wprev) as COXP.
            { destruct (classic (wprev=x)); ins; [basic_solver|].
              right; eapply tot_ex.
              by eapply WF.
              by basic_solver 12.
              unfolder; splits.
              hahn_rewrite (dom_l (wf_coE WF)) in CO; unfolder in CO; basic_solver 12.
              type_solver 21.
              hahn_rewrite (wf_col WF) in CO; unfold same_loc in CO; congruence.
              by unfold immediate in PIMMCO; desc; intro; eapply PIMMCO0; basic_solver 21.
              done. }
            assert (Time.le (f_to x) (f_to wprev)) as LL.
            { destruct COXP as [|COXP]; subst; vauto.
              apply Time.le_lteq; left.
              eapply f_to_co_mon; eauto. }
            etransitivity; [apply LL|].
            destruct NFROM as [[NFROM1 NFROM2]|[NFROM1 NFROM2]]; subst; vauto. }
          2: by apply WF.(co_irr) in CO. 
          apply (wf_coD WF) in CO.
          apply seq_eqv_l in CO; destruct CO as [WX CO].
          apply seq_eqv_r in CO; destruct CO as [CO WY].
          unfold is_w in WY; destruct (lab y) eqn:LAB; desc; try by desf.
          edestruct SIM_MEM.
          3,4: by unfold loc, val; rewrite LAB; eauto.
          { apply (wf_coE WF) in CO.
            apply seqA in CO.
            apply seq_eqv_r in CO; desf. }
          all: eauto.
          assert (co^? wnext y) as COXP.
          { destruct (classic (y=wnext)); ins; [basic_solver|].
            right; eapply tot_ex.
            by eapply WF.
            unfolder; splits.
            hahn_rewrite (dom_r (wf_coE WF)) in CO; unfolder in CO; basic_solver 12.
            type_solver 21.
            edone.
            unfolder; splits; auto.
            by hahn_rewrite (wf_col WF) in CO; hahn_rewrite (wf_col WF) in COPREV;
            hahn_rewrite (wf_col WF) in COPN; unfold same_loc in *; congruence.
            by unfold immediate in NIMMCO; desc; intro; eapply NIMMCO0; basic_solver 21.
            done. }
          assert (Time.le (f_from wnext) (f_from y) ) as LL.
          { destruct COXP as [|COXP]; subst; vauto.
            apply Time.le_lteq; left.
            eapply f_from_co_mon; eauto. }
          etransitivity; [|apply LL].
          destruct NTO as [[NTO1 NTO2]|[NTO1 NTO2]]; subst; vauto. }
        intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
        all: try rewrite !upds.
        all: try rewrite !updo.
        all: try by intros H; subst.
        { by apply FCOH. }
        { assert (x = wprev); subst.
          2: by destruct NFROM as [[NN1 NN2]|[NN1 NN2]]; desf.
         eapply WF.(rfrmw_in_im_co) in RFRMW; [|edone].
         destruct (classic (x=wprev)); auto.
         exfalso.
         unfold immediate in *; desc.
         apply (PIMMCO0 x).
         2: basic_solver.
         eexists; splits; [basic_solver|].
         eapply tot_ex.
         eapply WF.
         unfolder; splits.
         hahn_rewrite (dom_l (wf_coE WF)) in RFRMW; unfolder in RFRMW; basic_solver 12.
         hahn_rewrite (dom_l (wf_coD WF)) in RFRMW; unfolder in RFRMW; basic_solver 12.
         edone.
         unfolder; splits; eauto.
         hahn_rewrite (wf_col WF) in RFRMW; unfold same_loc in *; congruence.
         intro; eapply RFRMW0; eauto.
         done. }
        { assert (y = wnext); subst.
          2: by destruct NTO as [[NN1 NN2]|[NN1 NN2]]; desf.
          apply NRFRMW.
          revert RFRMW; basic_solver 12. }
        exfalso. eapply WF.(co_irr).
        eapply rfrmw_in_im_co in RFRMW; eauto.
        apply RFRMW. }

      assert (DenseOrder.lt Time.bot n_to) as NTOBOT.
      { destruct NTO as [[U1 U2]|[U1 U2]]; subst.
        all: eapply TimeFacts.le_lt_lt; eauto.
        all: apply Time.bot_spec. }

      set (rel'' :=
             if Rel w
             then TView.cur (Local.tview local)
             else TView.rel (Local.tview local) locw).

      assert (Time.le (View.rlx rel'' locw)
                      (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
      { unfold rel''. destruct (Rel w).
        { reflexivity. }
        eapply rel_le_cur; eauto. }

      assert (Time.lt (View.rlx rel'' locw) n_to) as REL_VIEW_LT.
      { eapply TimeFacts.le_lt_lt; eauto.
        eapply TimeFacts.le_lt_lt.
        2: by apply PREVNLT.
        cdes SIM_TVIEW. cdes CUR.
        eapply max_value_le_issued with (w:=w); eauto.
        { unfold t_cur, c_cur, CombRelations.urr.
          rewrite !seqA. rewrite dom_eqv1.
            by intros x [[_ YY]]. }
        { apply t_cur_covered; eauto. }
        split; [|basic_solver].
        intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
        apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR].
        red in TCUR. destruct TCUR as [z CCUR]. red in CCUR.
        hahn_rewrite <- seqA in CCUR.
        apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ].
        apply seq_eqv_r in URR. destruct URR as [URR II].
        eapply eco_urr_irr with (sc:=sc); eauto.
        1-3: by apply IMMCON.
        exists y. split.
        { apply co_in_eco. apply COXY. }
        apply urr_hb. exists z. split; eauto.
        right. apply sb_in_hb.
        assert (E z) as EZ.
        { apply TCCOH in COVZ. apply COVZ. }
        destruct II as [TIDZ|INITZ].
        2: by apply init_ninit_sb; auto.
        destruct (@same_thread G x z) as [[|SB]|SB]; auto.
        { desf. }
        exfalso. apply WNCOV. apply TCCOH in COVZ.
        apply COVZ. eexists. apply seq_eqv_r; eauto. }

      exists promises'; exists memory'; splits; eauto; unfold f_to', f_from'.
      3,4: by ins; rewrite updo; auto; intros H; subst.
      { by rewrite upds. }
      { rewrite upds. cdes SIM_TVIEW.
        specialize (CUR locw).
        unfold LocFun.find in *.
        unfold rel', rel''0. apply Time.join_spec.
        { apply Time.join_spec.
          { apply Time.le_lteq. left. apply REL_VIEW_LT. }
          destruct PREL0; desc.
          { subst. simpls. apply Time.bot_spec. }
          apply Time.le_lteq. left.
          eapply TimeFacts.le_lt_lt; [|by apply PREVNLT].
          eapply max_value_le_issued with (w:=w); eauto.
          { intros x [HH|HH].
            2: by desf.
            unfold CombRelations.msg_rel, CombRelations.urr in HH.
            hahn_rewrite seqA in HH. apply seq_eqv_l in HH. apply HH. }
          { intros x [HH|HH].
            2: by desf.
            eapply msg_rel_issued; eauto.
            exists p. apply seq_eqv_r. split; eauto. }
          split; [|basic_solver].
          intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
          apply seq_eqv_r in QQ. destruct QQ as [COXY [MSG|[MSG EQ]]].
          2: { subst. eapply WF.(co_irr). eapply WF.(co_trans).
               { apply COXY. }
               eapply rfrmw_in_im_co in INRMW; eauto. apply INRMW. }
          assert (msg_rel locw ⨾ (rf ⨾ rmw) ⊆ msg_rel locw) as YY.
          { unfold CombRelations.msg_rel, imm_s_hb.release, rs. 
            rewrite !seqA. by rewrite rt_unit. }
          assert (msg_rel locw y x) as MSGYX.
          { apply YY. eexists. eauto. }
          unfold CombRelations.msg_rel in MSGYX.
          destruct MSGYX as [z [URR RELES]].
          eapply release_co_urr_irr; eauto.
          1-4: by apply IMMCON.
          eexists; split; [|eexists; split]; eauto. }
        unfold f_to'. rewrite upds. simpls.
        unfold TimeMap.singleton, LocFun.add. rewrite Loc.eq_dec_eq.
        apply DenseOrder_le_PreOrder. }
      { red. splits.
        { red; ins. erewrite Memory.add_o in MSG; eauto.
          destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ].
          { simpls; subst.
            rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG.
            inv MSG. clear MSG. right.
            exists w; splits; auto.
              by right. }
          rewrite loc_ts_eq_dec_neq in MSG; simpls; auto.
          apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right].
          destruct MSG as [b H]; desc.
          assert (b <> w) as BNEQ.
          { by intros H; subst. }
          exists b; splits; auto.
          { by left. }
          all: by rewrite updo. }
        intros x y [ISSX|HX]; subst.
        { assert (x <> w) as XNEQ.
          { intros H; desf. }
          rewrite updo; auto.
          intros [ISSY|HY] JJ CO II; subst.
          { assert (y <> w) as YNEQ.
            { intros H; desf. }
            rewrite updo in II; auto. }
          rewrite upds in II.
          assert (loc lab x = Some locw) as XLOC.
          { rewrite <- LOC. by apply WF.(wf_col). }
          destruct NFROM as [[NFROM BB]|[NFROM BB]].
          { desc; subst.
            eapply f_to_eq in II; eauto.
            { subst. apply BB. }
            red. by rewrite XLOC. }
          exfalso.
          edestruct WF.(wf_co_total) with (a:=x) (b:=wprev) as [COWX|COWX].
          1-2: split; [split|]; eauto.
          1-2: by apply TCCOH in ISSX; apply ISSX.
          { intros H; subst. 
            edestruct Time.middle_spec as [AA _].
            { apply PREVNLT. }
            rewrite <- II in AA.
              by apply Time.lt_strorder in AA. }
          { subst.
            edestruct Time.middle_spec as [AA CC].
            { apply PREVNLT. }
            assert (Time.lt (f_to x) (f_to wprev)) as DD.
            { eapply f_to_co_mon; eauto. }
            rewrite II in DD.
            eapply Time.lt_strorder.
              by etransitivity; [by apply DD|]. }
          eapply PIMMCO.
          all: apply seq_eqv_l; split; eauto. }
        intros [ISSY|HY] JJ CO II; subst.
        2: by apply WF.(co_irr) in CO.
        assert (y <> x) as YNEQ.
        { intros H. desf. }
        rewrite upds in *; auto. rewrite updo in II; auto.
        assert (loc lab y = Some locw) as XLOC.
        { rewrite <- LOC. symmetry. by apply WF.(wf_col). }
        destruct NTO as [[NTO BB]|[NTO BB]].
        { desc; subst.
          eapply f_from_eq in II; eauto.
          { subst. apply BB. }
          red. by rewrite XLOC. }
        exfalso.
        edestruct WF.(wf_co_total) with (a:=y) (b:=wnext) as [COWX|COWX].
        1-2: split; [split|]; eauto.
        1-2: by apply TCCOH in ISSY; apply ISSY.
        { intros H; subst. 
          edestruct Time.middle_spec as [AA CC].
          { apply NPLT. }
          rewrite II in CC.
            by apply Time.lt_strorder in CC. }
        { eapply NIMMCO.
          all: apply seq_eqv_r; split; eauto. }
        subst.
        edestruct Time.middle_spec as [AA CC].
        { apply NPLT. }
        assert (Time.lt (f_from wnext) (f_from y)) as DD.
        { eapply f_from_co_mon; eauto. }
        rewrite <- II in DD.
        eapply Time.lt_strorder.
          by etransitivity; [by apply DD|]. }
      apply SIM_HELPER; auto. by ins; rewrite updo; auto; intros H; subst. }

    right. (* SPLITTING *)
    destruct (is_w_val lab wnext WNEXT) as [valwnext VALWNEXT].
    assert (sb w wnext) as SBNEXT.
    { clear -WF WW WNISS FOR_SPLIT RMW_ISSUED NIMMCO ISSNEXT CONEXT. desc.
      apply clos_trans_of_transitiveD; [apply sb_trans|].
      apply (inclusion_t_t FOR_SPLIT).
      eapply ct_imm1 in CONEXT.
      2: by apply WF.(co_irr).
      2: by apply WF.(co_trans).
      2: by intros x [y H']; apply WF.(wf_coE) in H'; apply seq_eqv_l in H'; desf; eauto.
      apply t_rt_step in CONEXT. destruct CONEXT as [z [IMMS IMM]].
      apply t_rt_step. exists z; split; [|apply seq_eqv_l; split; [|done]].
      { apply rtE in IMMS. destruct IMMS as [IMMS|IMMS].
        { red in IMMS; desf. apply rt_refl. }
        assert (immediate (co ⨾ ⦗issued T⦘) z wnext) as IMM'.
        { red; split; [apply seq_eqv_r; split; auto|].
          { apply clos_trans_immediate1; auto.
            eapply WF.(co_trans). }
          ins. eapply NIMMCO; [|by apply R2].
          apply seq_eqv_r in R1; destruct R1 as [R1 R3].
          apply seq_eqv_r; split; auto.
          eapply WF.(co_trans); [|by apply R1].
          apply clos_trans_immediate1; auto.
          eapply WF.(co_trans). }
        clear IMM.
        induction IMMS.
        { apply rt_step. apply seq_eqv_l; split; auto. }
        assert (co y wnext) as YNEXT.
        { apply clos_trans_immediate1; auto.
          eapply WF.(co_trans).
          eapply transitive_ct; [by apply IMMS2|].
          eapply clos_trans_immediate2.
          { apply WF.(co_trans). }
          { apply WF.(co_irr). }
          { red; ins. apply WF.(wf_coE) in REL.
            apply seq_eqv_l in REL; destruct REL as [_ REL].
            apply seq_eqv_r in REL. apply REL. }
          destruct IMM' as [II _].
          apply seq_eqv_r in II; apply II. }
        assert (immediate (co ⨾ ⦗issued T⦘) y wnext) as YNEXTIMM.
        { red; split; [by apply seq_eqv_r; split|].
          ins. eapply NIMMCO; [|by apply R2].
          apply seq_eqv_r in R1; destruct R1 as [R1 R3].
          apply seq_eqv_r; split; auto.
          eapply WF.(co_trans); [|by apply R1].
          apply clos_trans_immediate1; auto.
          eapply WF.(co_trans). }
        eapply rt_trans. 
        { by apply IHIMMS1. }
        apply IHIMMS2; auto.
        { intros NISS. eapply NIMMCO; apply seq_eqv_r; split; auto. 
          2: by apply NISS.
          2: done.
          apply clos_trans_immediate1; auto.
            by apply WF.(co_trans). }
        apply WF.(wf_coD) in YNEXT.
        apply seq_eqv_l in YNEXT; desf. }
      intros HH. apply rtE in IMMS; destruct IMMS as [IMSS|IMMS].
      { red in IMSS; desf. }
      eapply NIMMCO; apply seq_eqv_r; split; auto.
      2: by apply HH.
      all: apply clos_trans_immediate1; auto.
      all: apply WF.(co_trans). }
    assert (tid wnext = tid w) as TIDNEXT.
    { apply sb_tid_init in SBNEXT. destruct SBNEXT as [H|H]; desf. }
    assert (~ covered T wnext) as NCOVNEXT.
    { intros H; apply TCCOH in H.
      apply WNCOV. apply H.
      eexists. apply seq_eqv_r; split; eauto. }
    edestruct (SIM_MEM locw wnext) as [nextrel]; eauto.
    simpls; desc.
    specialize (H1 TIDNEXT NCOVNEXT). desc.

    set (n_to := Time.middle (f_from wnext) (f_to wnext)).

    assert (~ is_init wnext) as NINITWNEXT.
    { apply no_co_to_init in CONEXT; auto.
      2: { apply coherence_sc_per_loc. apply IMMCON. }
      apply seq_eqv_r in CONEXT. desf. }

    assert (Time.lt (f_from wnext) (f_to wnext)) as LLWNEXT.
    { by apply FCOH. }
    assert (Time.lt (f_from wnext) n_to) as LLFROMN.
    { unfold n_to. by apply DenseOrder.middle_spec. }
    assert (Time.lt n_to (f_to wnext)) as LLTON.
    { unfold n_to. by apply DenseOrder.middle_spec. }

    set (rel' := View.join
                   (View.join (TView.rel (Local.tview local) locw)
                              p_rel.(View.unwrap))
                   (View.singleton_ur locw n_to)).
    assert (View.opt_wf (Some rel')) as RELWF.
    { apply View.opt_wf_some.
      apply View.join_wf.
      2: by apply View.singleton_ur_wf.
      constructor.
      unfold View.join; simpls. rewrite REL_PLN_RLX.
      cdes PLN_RLX_EQ. rewrite EQ_REL.
      reflexivity. }
    assert (f_to_coherent G (issued T ∪₁ eq w) (upd f_to w n_to)
                          (upd (upd f_from wnext n_to) w (f_from wnext))) as N_FCOH.
    { red; splits; ins.
      { rewrite updo.
        { by apply FCOH. }
        intros HH; subst. by destruct H. }
      { rewrite updo.
        rewrite updo.
        { by apply FCOH. }
        all: intros HH; subst.
        { apply NCOVNEXT. by apply TCCOH. }
        destruct H; desf. } 
      { destruct H as [H|]; subst.
        2: by rewrite !upds.
        rewrite updo.
        2: by intros HH; subst.
        destruct (classic (wnext = x)) as [|NEQ]; subst;
          [rewrite upds | rewrite updo; auto];
          rewrite updo; auto.
          by apply FCOH.
            by intros HH; subst. }
      { assert (x <> y) as HXY.
        { by intros HH; subst; apply WF.(co_irr) in H1. }
        destruct H as [H|]; destruct H0 as [H0|]; subst.
        all: try (rewrite !upds).
        { rewrite updo; [|by intros HH; subst].
          rewrite updo; [|by intros HH; subst].
          destruct (classic (wnext = y)) as [|NEQ]; subst;
            [rewrite upds | rewrite updo; auto].
          { etransitivity; eauto.
            2: by apply Time.le_lteq; left; eauto.
              by apply FCOH. }
            by apply FCOH. }
        { rewrite updo; auto.
          apply FCOH; auto.
          eapply WF.(co_trans); eauto. }
        { rewrite updo; auto.
          destruct (classic (wnext = y)) as [|NEQ]; subst;
            [by rewrite upds; apply DenseOrder_le_PreOrder | rewrite updo; auto].
          etransitivity.
          { apply Time.le_lteq; left. apply LLTON. }
          apply FCOH; auto.
          eapply tot_ex.
          by eapply WF.
          unfolder; splits; eauto.
          hahn_rewrite (dom_r (wf_coE WF)) in H1; unfolder in H1; basic_solver 12.
          hahn_rewrite (dom_r (wf_coD WF)) in H1; unfolder in H1; basic_solver 12.
          unfolder; splits; eauto.
          hahn_rewrite (wf_col WF) in H1; unfold same_loc in *; congruence.
          by unfold immediate in NIMMCO; desc; intro; eapply NIMMCO0; basic_solver 21.
          by intro; subst. }
        by apply WF.(co_irr) in H1. }
      destruct H as [H|]; subst.
      { assert (x <> w) as NXW.
        { intros YY. desf. }
        rewrite updo; auto.
        destruct H0 as [H0|]; subst.
        { assert (y <> w) as NXY.
          { intros YY. desf. }
          rewrite updo; auto.
          assert (y <> wnext) as NYN.
          2: { rewrite updo; auto. by apply FCOH. }
          intros UU; subst.
          assert (loc lab x = Some locw) as XLOC.
          { rewrite <- LOCNEXT. by apply WF.(wf_rfrmwl). }
          edestruct WF.(wf_co_total) with (a:=w) (b:=x) as [CO|CO]; auto.
          1,2: split; [split|]; auto.
          1,2: by apply TCCOH in H; apply H.
          { by rewrite XLOC. }
          { eapply NIMMCO.
            all: apply seq_eqv_r; split; eauto.
            eapply rfrmw_in_im_co; eauto. }
          eapply rfrmw_in_im_co in H1; eauto. eapply H1; eauto. }
        rewrite upds.
        assert (x = wprev); subst.
        { apply PRFRMW. apply seq_eqv_l. by split. }
        exfalso. apply WNISS. apply TCCOH in ISSNEXT.
        apply ISSNEXT. eexists. apply seq_eqv_r; split; eauto.
        apply seq_eqv_l; split; auto.
        destruct H1 as [z [RF RMW]].
        apply ct_step. apply w_ex_acq_sb_w_in_ar.
        apply seq_eqv_l. split.
        { apply ACQEX. eexists; eauto. }
        apply seq_eqv_r. split; auto. }
      destruct H0 as [H0|]; subst.
      { rewrite upds. 
        assert (y = wnext); subst.
        { apply NRFRMW. apply seqA. apply seq_eqv_r. by split. }
        rewrite updo.
        { by rewrite upds. }
        intros UU. desf. }
      eapply rfrmw_in_im_co in H1; eauto.
      destruct H1 as [HH _]. by apply WF.(co_irr) in HH. }
    
    edestruct (@Memory.split_exists (Local.promises local) locw
                                    (f_from wnext) n_to (f_to wnext)
                                    valw valwnext
                                    (Some rel') nextrel) as [promises' PSPLIT]; eauto.

    edestruct (@Memory.split_exists PC.(Configuration.memory) locw
                                    (f_from wnext) n_to (f_to wnext)
                                    valw valwnext
                                    (Some rel') nextrel) as [memory' MSPLIT]; eauto.

    assert (issued T wnext) as NEXTISS.
    { destruct NIMMCO as [HH _]. apply seq_eqv_r in HH; desf. }
    assert (~ Rel w) as NREL.
    { intros WREL. apply WNISS.
      eapply w_covered_issued; eauto. split; auto.
      apply TCCOH in NEXTISS. destruct NEXTISS as [[_ NN] _].
      apply NN. exists wnext. apply seq_eqv_r; split; auto.
      red. left; left; right. apply seq_eqv_l; split; [by split|].
      apply seq_eqv_r; split; auto. split; auto.
      red. by rewrite LOC. }

    assert (vnext = valwnext); subst.
    { rewrite VALWNEXT in VNEXT. inv VNEXT. }

    splits; auto.
    exists wnext; exists valwnext;
      exists (Some
                (View.join
                   (View.join (TView.rel (Local.tview local) locw)
                              (View.unwrap p_rel0))
                   (View.singleton_ur locw (f_to wnext)))).
    exists (upd f_to w n_to).
    exists (upd (upd f_from wnext n_to) w (f_from wnext)).

    assert (co wprev wnext) as COPN.
    { eapply WF.(co_trans); eauto. }

    assert (Time.le (f_to wprev) (f_from wnext)) as LEWPWTO.
    { destruct (classic (is_init wprev)) as [WPINIT|WPNINIT].
      2: by apply FCOH; eauto.
      assert (f_to wprev = tid_init) as HH.
      { apply FCOH. by split. }
      rewrite HH. apply Time.bot_spec. }

    assert (Time.lt (f_to wprev) n_to) as LEWPNTO.
    { eapply TimeFacts.le_lt_lt; [by apply LEWPWTO|].
      unfold n_to.
      apply Time.middle_spec. by apply FCOH. }

    assert (DenseOrder.lt tid_init n_to) as NTOBOT.
    { unfold n_to.
      eapply TimeFacts.le_lt_lt; eauto.
      apply Time.bot_spec. }

    assert (Time.lt (View.rlx (TView.rel (Local.tview local) locw) locw) n_to)
      as LTNTO.
    { eapply TimeFacts.le_lt_lt.
      2: by apply LEWPNTO.
      assert (Time.le (View.rlx (TView.rel (Local.tview local) locw) locw)
                      (View.rlx (TView.cur (Local.tview local)) locw)) as VV.
      { eapply rel_le_cur; eauto. }
      etransitivity; [by apply VV|].
      cdes SIM_TVIEW. cdes CUR.
      eapply max_value_le_issued with (w:=w); eauto.
      { unfold t_cur, c_cur, CombRelations.urr.
        rewrite !seqA. rewrite dom_eqv1.
          by intros x [[_ YY]]. }
      { apply t_cur_covered; eauto. }
      split; [|basic_solver].
      intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
      apply seq_eqv_r in QQ. destruct QQ as [COXY TCUR].
      red in TCUR. destruct TCUR as [z CCUR]. red in CCUR.
      hahn_rewrite <- seqA in CCUR.
      apply seq_eqv_r in CCUR. destruct CCUR as [URR COVZ].
      apply seq_eqv_r in URR. destruct URR as [URR II].
      eapply eco_urr_irr with (sc:=sc); eauto.
      1-3: by apply IMMCON.
      exists y. split.
      { apply co_in_eco. apply COXY. }
      apply urr_hb. exists z. split; eauto.
      right. apply sb_in_hb.
      assert (E z) as EZ.
      { apply TCCOH in COVZ. apply COVZ. }
      destruct II as [TIDZ|INITZ].
      2: by apply init_ninit_sb; auto.
      destruct (@same_thread G x z) as [[|SB]|SB]; auto.
      { desf. }
      exfalso. apply WNCOV. apply TCCOH in COVZ.
      apply COVZ. eexists. apply seq_eqv_r; eauto. }

    exists promises'; exists memory'.
    unfold rel' in *.
    splits; auto.
    1-5: rewrite upds; (try rewrite (fun x y => updo x y NEQNEXT));
      (try rewrite upds); auto.
    { rewrite upds. cdes SIM_TVIEW. clear ACQ REL.
      apply Time.join_spec.
      2: { unfold TimeMap.singleton, LocFun.add.
           rewrite Loc.eq_dec_eq. apply DenseOrder_le_PreOrder. }
      apply Time.le_lteq. left.
      apply TimeFacts.join_spec_lt; auto.
      eapply TimeFacts.le_lt_lt.
      2: by apply LEWPNTO.
      destruct PREL0; desc.
      { subst. simpls. apply Time.bot_spec. }
      eapply max_value_le_issued with (w:=w); eauto.
      { intros x [HH|HH].
        2: by desf.
        unfold CombRelations.msg_rel, CombRelations.urr in HH.
        hahn_rewrite seqA in HH. apply seq_eqv_l in HH. apply HH. }
      { intros x [HH|HH].
        2: by desf.
        eapply msg_rel_issued; eauto.
        exists p. apply seq_eqv_r. split; eauto. }
      split; [|basic_solver].
      intros x y QQ. apply seq_eqv_l in QQ. destruct QQ as [QQ' QQ]; subst.
      apply seq_eqv_r in QQ. destruct QQ as [COXY [MSG|[MSG EQ]]].
      2: { subst. eapply WF.(co_irr). eapply WF.(co_trans).
           { apply COXY. }
           eapply rfrmw_in_im_co in INRMW; eauto. apply INRMW. }
      assert (msg_rel locw ⨾ (rf ⨾ rmw) ⊆ msg_rel locw) as YY.
      { unfold CombRelations.msg_rel, imm_s_hb.release, rs. 
        rewrite !seqA. by rewrite rt_unit. }
      assert (msg_rel locw y x) as MSGYX.
      { apply YY. eexists. eauto. }
      unfold CombRelations.msg_rel in MSGYX.
      destruct MSGYX as [z [URR RELES]].
      eapply release_co_urr_irr; eauto.
      1-4: by apply IMMCON.
      eexists; split; [|eexists; split]; eauto. }
    { ins. rewrite updo; auto. by intros HH; subst. }
    { ins. destruct ISS as [ISS NEQ].
      rewrite updo.
      2: by intros HH; subst.
      rewrite updo; auto. }
    { etransitivity; eauto.
      arewrite (set_compl (issued T ∪₁ eq w) ⊆₁ set_compl (issued T)); [|done].
      basic_solver. }
    { etransitivity; eauto.
      basic_solver. }
    destruct (Rel w); simpls.
    apply SIM_HELPER; auto. by ins; rewrite updo; auto; intros H; subst. }
  left. (* ISSUING *)
  set (ts := Memory.max_ts locw (Configuration.memory PC)).
  set (f_to' := upd f_to w (Time.incr (Time.incr ts))).
  exists f_to'.
 
  set (A :=
         exists wprev, ⟪ WPISS : issued T wprev ⟫ /\
                       ⟪ RFRMW : (rf ⨾ rmw) wprev w ⟫).
  assert (exists n_from,
             ⟪ NFROM_SPEC : ((n_from = ts) /\ A) \/ ((n_from = Time.incr ts) /\ ~ A) ⟫ )
    as [n_from NFROM].
  { destruct (classic A) as [H|H].
    { by exists ts; left. }
    by exists (Time.incr ts); right. }
  assert (Time.le ts n_from) as LENFROM_R.
  { destruct NFROM as [[N _]|[N _]]; subst; [reflexivity|].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  assert (Time.le n_from (Time.incr ts)) as LENFROM_L.
  { destruct NFROM as [[N _]|[N _]]; subst; [|reflexivity].
    apply Time.le_lteq; left. apply DenseOrder.incr_spec. }

  set (f_from' := upd f_from w n_from).
  exists f_from'.

  assert (Time.lt (f_from' w) (f_to' w)) as NLT.
  { unfold f_to', f_from', ts; rewrite !upds.
    eapply TimeFacts.le_lt_lt.
    { apply LENFROM_L. }
    apply DenseOrder.incr_spec. }

  assert (Time.lt (View.rlx (TView.rel (Local.tview local) locw) locw)
                  (f_to' w))
      as REL_VIEW_LT.
  { unfold f_to', ts. rewrite upds.
    etransitivity.
    2: by apply DenseOrder.incr_spec.
    eapply TimeFacts.le_lt_lt.
    2: by apply DenseOrder.incr_spec.
    apply Memory.max_ts_spec2.
    apply MEM_CLOSE. }
  assert (Time.le (View.rlx (TView.rel (Local.tview local) locw) locw)
                  (f_to' w))
      as REL_VIEW_LE.
  { by apply Time.le_lteq; left. }

  assert (forall to from msg,
             Memory.get locw to (Configuration.memory PC) =
             Some (from, msg) ->
             Interval.disjoint (f_from' w, f_to' w) (from, to)) as DISJOINT.
  { unfold f_to', f_from', ts; rewrite !upds.
    ins; red; ins. destruct LHS. destruct RHS.
    simpls.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    2: by apply FROM.
    etransitivity.
    2: by apply LENFROM_R.
    etransitivity.
    { apply TO0. }
    unfold ts.
    apply Memory.max_ts_spec in H. desf. }

  edestruct (@Memory.add_exists (Local.promises local) locw (f_from' w) (f_to' w) valw)
    as [promises' PADD].
  3: by apply View.opt_wf_some; apply REL_WF_1.
  { ins. eapply DISJOINT.
    eapply PROM_IN_MEM; eauto. }
  { done. }

  edestruct (@Memory.add_exists PC.(Configuration.memory) locw (f_from' w) (f_to' w) valw)
    as [memory' MADD].
  3: by apply View.opt_wf_some; apply REL_WF_1.
  { apply DISJOINT. }
  { done. }

  assert
  (f_to_coherent G (issued T ∪₁ eq w)
    (upd f_to w (Time.incr (Time.incr (Memory.max_ts locw (Configuration.memory PC)))))
    (upd f_from w n_from)) as N_FCOH.
  { red; splits.
    { ins; rewrite updo; [by apply FCOH|].
      intros Y; subst. by destruct H. }
    { ins; rewrite updo; [by apply FCOH|].
      intros Y; subst. by destruct H. }
    { intros x [ISS|]; subst.
      { rewrite !updo; [by apply FCOH | |].
        all: by intros Y; subst. }
      unfold f_to', f_from', ts in *.
        by rewrite !upds in *. }
    { intros x y [ISSX|EQX] [ISSY|EQY] CO; subst.
      all: try rewrite !upds.
      all: try rewrite !updo.
      all: try by intros H; subst.
      { by apply FCOH. }
      { (* TODO: generalize to lemma! *)
        apply (wf_coD WF) in CO.
        apply seq_eqv_l in CO; destruct CO as [WX CO].
        apply seq_eqv_r in CO; destruct CO as [CO WY].
        unfold is_w in WX; destruct (lab x) eqn:LAB; desc; try by desf.
        edestruct SIM_MEM.
        3,4: by unfold loc, val; rewrite LAB; eauto.
        { apply (wf_coE WF) in CO.
          apply seq_eqv_l in CO; desf. }
        all: eauto.
        desc.
        apply (wf_col WF) in CO; red in CO; unfold loc in *; desf.
        all: etransitivity; [by eapply Memory.max_ts_spec; eauto|].
        all: by apply LENFROM_R. }
      { exfalso. eapply WNONEXT. eexists; apply seq_eqv_r; eauto. }
      exfalso. by apply co_irr in CO. }
    intros x y [ISSX|EQX] [ISSY|EQY] RFRMW; subst.
    all: try rewrite !upds.
    all: try rewrite !updo.
    all: try by intros H; subst.
    { by apply FCOH. }
    { destruct NFROM as [[EQ [wprev HH]]|[EQ NWPREV]]; subst.
      2: by exfalso; apply NWPREV; eexists; split; eauto.
      red in RESERVED_TIME. destruct smode; desc.
      2: { exfalso. apply WNISS. apply RMW_ISSUED.
           destruct RFRMW as [z [RF RMW]].
             by exists z. }
      assert (wprev = x); [|subst].
      eapply wf_rfrmwf; eauto.
      destruct (classic (f_to x = ts)) as [|NEQ]; [done|exfalso].
      unfold ts in *.
      assert (E x) as EX.
      { hahn_rewrite (dom_l (wf_rfE WF)) in RFRMW; revert RFRMW; basic_solver. }
      assert (co x y) as COXY.
      { apply rf_rmw_in_co; cdes IMMCON; eauto using coherence_sc_per_loc. }
      assert (Loc_ locw x) as LOCX.
      { hahn_rewrite (wf_col WF) in COXY; unfold same_loc in COXY; congruence. }
      assert (exists valx, val lab x = Some valx) as [valx VALX].
      { apply is_w_val. hahn_rewrite (dom_l (wf_coD WF)) in COXY; revert COXY; basic_solver. }
      edestruct SIM_MEM as [xrel].
      2: by apply ISSX.
      by eauto.
      by apply LOCX.
      by eauto.
      destruct H as [INMEM H'']; desc.
      edestruct Memory.max_ts_spec as [[from [val [rel HMEM]]] TS].
      { apply INMEM. }
      red in TS. apply Time.le_lteq in TS; destruct TS as [TS|]; [clear NEQ|by subst].
      apply MEM in HMEM. destruct HMEM as [[H1 H2]|HMEM].
      { rewrite H1 in TS. by apply time_lt_bot in TS. }
      destruct HMEM as [wmax H]; desc. rewrite <- TO in TS.
      assert (wmax <> y) as WWNEQ.
      { intros H; desf. }
      assert ((E ∩₁ W ∩₁ (fun x0 => loc lab x0 = Some locw)) wmax) as WWM.
      { split; [split|]; eauto. by apply TCCOH. }
      assert ((E ∩₁ W ∩₁ (fun x0 => loc lab x0 = Some locw)) x) as WXX.
      { split; [split|]; eauto. by apply TCCOH. }
      assert (co wmax y) as COWY.
      { edestruct WF.(wf_co_total).
        3: by apply WWNEQ.
        1-3: by eauto.
        exfalso. apply WNONEXT; eexists; apply seq_eqv_r; eauto. }
      assert (wmax <> x) as WXNEQ.
      { intros H; subst. eapply Time.lt_strorder; eauto. }
      assert (co x wmax) as COXW.
      { edestruct WF.(wf_co_total).
        3: by apply WXNEQ.
        1-2,4: by eauto.
        exfalso. eapply Time.lt_strorder; etransitivity. apply TS.
        eapply f_to_co_mon; eauto. }
      eapply rfrmw_in_im_co; eauto. }
    all: exfalso; eapply rfrmw_in_im_co in RFRMW; eauto.
    { eapply WNONEXT. eexists; apply seq_eqv_r; split; eauto.
      apply RFRMW. }
    eapply WF.(co_irr). apply RFRMW. }

  assert (forall z (ISSZ : issued T z) (LOCZ : loc lab z = Some locw),
             Time.le (f_to z) ts) as YY.
  { ins.
    red in SIM_MEM.
    assert (E z) as EZ.
    { apply TCCOH in ISSZ. apply ISSZ. }
    assert (W z) as WZ.
    { apply TCCOH in ISSZ. apply ISSZ. }
    destruct (is_w_val lab z WZ) as [vz VALZ].
    edestruct SIM_MEM with (b:=z) as [p_rel']; eauto.
    desc.
    apply Memory.max_ts_spec in INMEM.
    destruct INMEM as [_ LE].
    apply LE. }

  assert (forall z (ISSZ : issued T z) (LOCZ : loc lab z = Some locw),
             ~ Time.lt ts (f_to z) ) as XX.
  { ins. intros LL.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt; [|apply LL].
      by apply YY. }

  set (rel'' := if Rel w
                then TView.cur (Local.tview local)
                else TView.rel (Local.tview local) locw).

  assert (Time.le (View.rlx rel'' locw)
                  (View.rlx (TView.cur (Local.tview local)) locw)) as GG.
  { unfold rel''. destruct (Rel w).
    { reflexivity. }
    eapply rel_le_cur; eauto. }

  assert (Time.lt (View.rlx rel'' locw)
                  (Time.incr (Time.incr (Memory.max_ts locw (Configuration.memory PC)))))
    as INCRLT.
  { eapply TimeFacts.le_lt_lt; [by apply GG|].
    cdes SIM_TVIEW. specialize (CUR locw). cdes CUR.
    destruct MAX as [[Y1 Y2]|[a_max Y1]].
    { unfold LocFun.find in *.
      rewrite Y2. eapply TimeFacts.le_lt_lt.
      { apply Time.bot_spec. }
      apply Time.incr_spec. }
    desc.
    destruct INam as [z INam].
    red in INam. hahn_rewrite seq_eqvC in INam.
    hahn_rewrite <- seqA in INam.
    apply seq_eqv_r in INam. destruct INam as [INam TINIT].
    assert (ISSA := INam). apply urr_covered in ISSA; auto.
    apply seq_eqv_l in ISSA. destruct ISSA as [ISSA _].
    apply seq_eqv_r in INam. destruct INam as [INam COVA].
    eapply TimeFacts.le_lt_lt; eauto.
    eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt.
    2: by apply Time.incr_spec.
    apply wf_urrD in INam.
    apply seq_eqv_l in INam. destruct INam as [[WA LOCA] URR].
    assert (exists aval, val lab a_max = Some aval) as [aval AVAL].
    { unfold val. type_solver. }
    edestruct SIM_MEM with (b:=a_max) as [rel]; eauto.
    eapply issuedE; eauto. }

  exists promises'; exists memory'; splits; eauto; unfold f_to', f_from', ts.
  3,4: by ins; rewrite updo; auto; intros H; subst.
  { rewrite upds; auto. }
  { rewrite upds; auto.
    cdes SIM_TVIEW. clear ACQ REL.
    specialize (CUR locw).
    unfold LocFun.find in *.
    unfold rel'. apply Time.join_spec.
    2: { simpls. unfold TimeMap.singleton, LocFun.add.
         rewrite Loc.eq_dec_eq. unfold f_to', ts.
         rewrite upds. apply DenseOrder_le_PreOrder. }
    apply Time.join_spec.
    { apply Time.le_lteq. by left. }
    destruct PREL0 as [PP|PP]; desc.
    { rewrite PREL. apply Time.bot_spec. }
    specialize (P_MSG locw).
    cdes P_MSG.
    destruct MAX as [[Y1 Y2]|[a_max Y1]].
    { unfold LocFun.find in *. rewrite Y2.
      apply Time.bot_spec. }
    desc.
    destruct INam as [MSG|[U1 U2]].
    2: { subst. etransitivity; eauto.
         etransitivity; [by apply YY|].
         apply Time.le_lteq. left.
         etransitivity; apply Time.incr_spec. }
    etransitivity; eauto.
    etransitivity.
    2: { apply Time.le_lteq. left.
         etransitivity; apply Time.incr_spec. }
    apply YY.
    { eapply msg_rel_issued; eauto.
      exists p. apply seq_eqv_r. split; eauto. }
    destruct MSG as [z [URR _]].
    red in URR. apply seq_eqv_l in URR.
    apply URR. }
  { red. red in RESERVED_TIME. destruct smode; desc; [|splits]; auto.
    2-3: etransitivity; eauto; basic_solver.
    splits.
    { red; ins. erewrite Memory.add_o in MSG; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[EQ1 EQ2]|NEQ]; simpls; subst.
      { rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in MSG. inv MSG. clear MSG.
        right. exists w; splits; auto.
          by right. }
      rewrite (loc_ts_eq_dec_neq NEQ) in MSG.
      apply MEM in MSG. destruct MSG as [MSG|MSG]; [by left|right].
      destruct MSG as [b MSG]; desc.
      exists b. assert (b <> w) as BWNEQ; [by intros SS; desf|].
      unnw. rewrite !updo; auto.
      splits; auto.
        by left. }
    intros x y [ISSX|EQX] [ISSY|EQY] NINIT CO; subst.
    all: try rewrite !upds.
    all: try rewrite !updo; auto.
    all: try by intros H; subst.
    3: by apply WF.(co_irr) in CO.
    { intros KK. 
      destruct NFROM as [[NN1 NN2]|[NN1 NN2]].
      { subst. red in NN2. desc.
        destruct (classic (wprev = x)) as [|NEQ]; [by subst|].
        exfalso.
        assert (E x) as EX.
        { apply TCCOH in ISSX. apply ISSX. }
        assert (W x) as WX.
        { apply TCCOH in ISSX. apply ISSX. }
        assert (loc lab x = Some locw) as LOCX.
        { rewrite <- LOC. by apply WF.(wf_col). }
        assert (loc lab wprev = Some locw) as LOCWP.
        { rewrite <- LOC. apply WF.(wf_col). eapply rfrmw_in_im_co; eauto. }
        edestruct WF.(wf_co_total) with (a:=wprev) (b:=x) as [COWX|COWX]; auto.
        1,2: split; [split|]; eauto.
        1,2: by apply TCCOH in WPISS; apply WPISS.
        { eapply rfrmw_in_im_co; eauto. }
        assert (Time.lt (f_to x) (f_to wprev)) as LL.
        { eapply f_to_co_mon; eauto. }
        rewrite KK in LL.
        eapply XX.
        3: by apply LL.
        all: eauto. }
      exfalso. eapply XX.
      { apply ISSX. }
      { rewrite <- LOC. by apply WF.(wf_col). }
      rewrite KK. rewrite NN1. apply Time.incr_spec. }
    intros HH. exfalso.
    assert (Time.lt (f_from y) (f_to y)) as FF by (apply FCOH; auto).
    eapply XX.
    3: { etransitivity; [|by apply FF].
         rewrite <- HH. etransitivity; apply Time.incr_spec. }
    { done. }
    rewrite <- LOC. symmetry. by apply WF.(wf_col). }
  eapply SIM_HELPER; auto. by ins; rewrite updo; auto; intros H; subst.
Qed.

Lemma write_promise_step_helper f_to f_from T PC w locw valw ordw langst local smode
      (IMMCON : imm_consistent G sc)
      (TCCOH : tc_coherent G sc T)
      (ACQEX : W_ex ⊆₁ W_ex_acq)
      (WNISS : ~ issued T w)
      (WISSUABLE : issuable G sc T w)
      (LOC : loc lab w = Some locw)
      (VAL : val lab w = Some valw)
      (ORD : mod lab w = ordw)
      (RELCOV : W ∩₁ Rel ∩₁ issued T ⊆₁ covered T)
      (THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
          exists langst, IdentMap.find (tid e) PC.(Configuration.threads) = Some langst)
      (PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' PC.(Configuration.threads) =
                       Some (langst, local)),
           Memory.le local.(Local.promises) PC.(Configuration.memory))
      (FCOH : f_to_coherent G (issued T) f_to f_from)
      (SC_COV : smode = sim_certification -> E∩₁F∩₁Sc ⊆₁ covered T)
      (SC_REQ : smode = sim_normal -> 
                forall (l : Loc.t),
                  max_value f_to (S_tm G l (covered T)) (LocFun.find l PC.(Configuration.sc)))
      (SIM_PROM : sim_prom G sc (tid w) T f_to f_from local.(Local.promises))
      (RESERVED_TIME: reserved_time G f_to f_from (issued T) PC.(Configuration.memory) smode)
      (CLOSED_SC : Memory.closed_timemap PC.(Configuration.sc) PC.(Configuration.memory))
      (FUTURE : Memory.future Memory.init (Configuration.memory PC))
      (PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' PC.(Configuration.threads) =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to local .(Local.promises) = None \/
           Memory.get loc to local'.(Local.promises) = None)
      (SIM_MEM : sim_mem G sc T f_to f_from
                         (tid w) local PC.(Configuration.memory))
      (SIM_TVIEW : sim_tview G sc (covered T) f_to local.(Local.tview) (tid w))
      (PLN_RLX_EQ : pln_rlx_eq local.(Local.tview))
      (MEM_CLOSE : memory_close local.(Local.tview) PC.(Configuration.memory))
      (TID : IdentMap.find (tid w) PC.(Configuration.threads) = Some (langst, local)) :
  let memory := PC.(Configuration.memory) in
  let sc_view := PC.(Configuration.sc) in
  exists p_rel,
    (⟪ REL_PLN_RLX : View.pln p_rel.(View.unwrap) = View.rlx p_rel.(View.unwrap) ⟫ /\
     ⟪ P_MEM_CLOS : Memory.closed_timemap (View.rlx p_rel.(View.unwrap)) memory ⟫) /\
     ⟪ P_REL_CH :
         (⟪ NINRMW : ~ codom_rel (⦗ issued T ⦘ ⨾ rf ⨾ rmw) w ⟫ /\
          ⟪ PREL : p_rel = None ⟫) \/
         (exists p,
             ⟪ EP  : E p ⟫ /\
             ⟪ ISSP  : issued T p ⟫ /\
             ⟪ INRMW : (rf ⨾ rmw) p w ⟫ /\
             ⟪ P_LOC : loc lab p = Some locw ⟫ /\
             ⟪ P_MSG : sim_msg G sc f_to p p_rel.(View.unwrap) ⟫  /\
           exists p_v,
             ⟪ P_VAL : val lab p = Some p_v ⟫ /\
             ⟪ P_INMEM : Memory.get locw (f_to p) memory =
                         Some (f_from p, Message.mk p_v p_rel) ⟫)⟫ /\
  (⟪ FOR_ISSUE :
     exists f_to' f_from' promises' memory' promises'',
     let rel'' :=
         if is_rel lab w
         then (TView.cur (Local.tview local))
         else (TView.rel (Local.tview local) locw)
     in
     let rel := (View.join (View.join rel'' p_rel.(View.unwrap))
                           (View.singleton_ur locw (f_to' w))) in

     let tview' := if is_rel lab w
                   then TView.write_tview local.(Local.tview) sc_view locw
                                          (f_to' w) (Event_imm_promise.wmod ordw)
                   else local.(Local.tview) in
     let local' := Local.mk tview' promises'' in
     let threads' :=
         IdentMap.add (tid w)
                      (langst, local')
                      (Configuration.threads PC) in

     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to'   e = f_to   e ⟫ /\
     ⟪ ISSEQ_FROM : forall e (ISS: issued T e), f_from' e = f_from e ⟫ /\

     ⟪ REL_VIEW_LT : Time.lt (View.rlx rel'' locw) (f_to' w) ⟫ /\

     ⟪ PEQ :
         if Rel w
         then Memory.remove promises' locw (f_from' w) (f_to' w) valw
                            (Some rel) promises''
         else promises'' = promises' ⟫ /\

     ⟪ PADD :
       Memory.add local.(Local.promises) locw (f_from' w) (f_to' w) valw
                                         (Some rel) promises' ⟫ /\

     ⟪ MADD :
        Memory.add memory locw (f_from' w) (f_to' w) valw
                   (Some rel) memory' ⟫ /\
     ⟪ MFUTURE :
        Memory.future Memory.init memory' ⟫ /\

     ⟪ HELPER :
         sim_mem_helper
           G sc f_to' w (f_from' w) valw
           (View.join (View.join (if is_rel lab w
                                  then (TView.cur (Local.tview local))
                                  else (TView.rel (Local.tview local) locw))
                                 p_rel.(View.unwrap))
                      (View.singleton_ur locw (f_to' w))) ⟫ /\

     ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
         exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\
     ⟪ PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' threads' = Some (langst, local)),
           Memory.le local.(Local.promises) memory' ⟫ /\

     ⟪ FCOH: f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\
     ⟪ SC_REQ : smode = sim_normal -> 
                forall (l : Loc.t),
                  max_value f_to' (S_tm G l (covered T)) (LocFun.find l sc_view) ⟫ /\
     ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

     let covered' := if Rel w then covered T ∪₁ eq w else covered T in
     ⟪ SIM_PROM : sim_prom G sc (tid w)
                           (mkTC covered' (issued T ∪₁ eq w))
                           f_to' f_from' promises''  ⟫ /\
     ⟪ RESERVED_TIME :
         reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' smode ⟫ /\

     ⟪ PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' threads' =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to promises'' = None \/
           Memory.get loc to local'.(Local.promises) = None ⟫ /\

     ⟪ SIM_MEM : sim_mem G sc (mkTC covered' (issued T ∪₁ eq w))
                         f_to' f_from' (tid w) local' memory' ⟫ /\

     ⟪ MEM_PROMISE :
         Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                        valw (Some rel) promises' memory' Memory.op_kind_add ⟫ /\

     ⟪ REL_CLOSE : Memory.closed_opt_view (Some rel) memory' ⟫ /\
     ⟪ NEW_CLOSE : Memory.closed_timemap (TimeMap.singleton locw (f_to' w)) memory' ⟫ /\
     ⟪ VIEW_CLOSE : memory_close tview' memory' ⟫ /\

     ⟪ NOWLOC : Rel w -> Memory.nonsynch_loc locw (Local.promises local) ⟫
   ⟫ \/
   ⟪ FOR_SPLIT :
     ⟪ NREL : ~ Rel w ⟫ /\
     ⟪ SMODE : smode = sim_certification ⟫ /\

     exists ws valws relws rel f_to' f_from' promises' memory',
     let local' := Local.mk (Local.tview local) promises' in
     let threads' :=
         IdentMap.add (tid w)
                      (langst, local')
                      (Configuration.threads PC) in
     ⟪ ISSEQ_TO   : forall e (ISS: issued T e), f_to' e = f_to e ⟫ /\
     ⟪ ISSEQ_FROM :
        forall e (ISS: (issued T \₁ eq ws) e), f_from' e = f_from e ⟫ /\

     ⟪ PADD :
        Memory.split (Local.promises local)
                     locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     rel relws promises' ⟫ /\
     ⟪ MADD :
        Memory.split memory locw (f_from' w) (f_to' w) (f_to' ws) valw valws
                     rel relws memory' ⟫ /\
     ⟪ MFUTURE :
        Memory.future Memory.init memory' ⟫ /\
      
     ⟪ WSISS  : issued T ws ⟫ /\
     ⟪ WSNCOV : ~ covered T ws ⟫ /\
     ⟪ WSVAL : val lab ws = Some valws ⟫ /\

     ⟪ SBWW : sb w ws ⟫ /\
     ⟪ SAME_LOC : Loc_ locw ws ⟫ /\
     ⟪ COWW : co w ws ⟫ /\

     ⟪ FEQ1 : f_to' w = f_from' ws ⟫ /\
     ⟪ FEQ2 : f_from' w = f_from ws ⟫ /\

     ⟪ THREAD : forall e (ACT : E e) (NINIT : ~ is_init e),
         exists langst, IdentMap.find (tid e) threads' = Some langst ⟫ /\
     ⟪ PROM_IN_MEM :
         forall thread' langst local
                (TID : IdentMap.find thread' threads' = Some (langst, local)),
           Memory.le local.(Local.promises) memory' ⟫ /\

     ⟪ FCOH : f_to_coherent G (issued T ∪₁ eq w) f_to' f_from' ⟫ /\

     ⟪ CLOSED_SC : Memory.closed_timemap sc_view memory' ⟫ /\

     ⟪ SIM_PROM : sim_prom G sc (tid w)
                           (mkTC (covered T) (issued T ∪₁ eq w))
                           f_to' f_from' promises' ⟫ /\
     ⟪ RESERVED_TIME :
            reserved_time G f_to' f_from' (issued T ∪₁ eq w) memory' sim_certification ⟫ /\

     ⟪ PROM_DISJOINT :
         forall thread' langst' local'
                (TNEQ : tid w <> thread')
                (TID' : IdentMap.find thread' threads' =
                        Some (langst', local')),
         forall loc to,
           Memory.get loc to promises' = None \/
           Memory.get loc to local'.(Local.promises) = None ⟫ /\
     ⟪ SIM_MEM : sim_mem G sc (mkTC (covered T) (issued T ∪₁ eq w))
                         f_to' f_from' (tid w) local' memory' ⟫ /\
     ⟪ MEM_PROMISE :
         Memory.promise (Local.promises local) memory locw (f_from' w) (f_to' w)
                        valw rel promises' memory'
                        (Memory.op_kind_split (f_to' ws) valws relws) ⟫ /\
     ⟪ REL_CLOSE : Memory.closed_opt_view rel memory' ⟫
   ⟫).
Proof using WF.
  assert (Memory.inhabited PC.(Configuration.memory)) as INHAB.
  { by apply inhabited_future_init. }

  assert (W w) as WW.
  { apply WISSUABLE. }

  assert (E w) as EW.
  { apply WISSUABLE. }
  
  assert (~ covered T w) as WNCOV.
  { intros COV. apply WNISS.
      by eapply w_covered_issued; eauto; split. }

  assert (~ is_init w) as WNINIT.
  { intros H. apply WNCOV. apply TCCOH. by split. }

  assert ((E ∩₁ W ∩₁ Loc_ locw) w) as WEW.
  { split; [split|]; auto. }

  assert (tc_coherent G sc (mkTC (covered T) (issued T ∪₁ eq w))) as TCCOH'.
  { eapply trav_step_coherence; eauto. exists w; right. by splits. }

  edestruct exists_time_interval as [p_rel].
  3: by apply TCCOH.
  all: eauto.
  desc.
  exists p_rel; split; auto.
  split; auto.
  destruct H1; desc.
  { red in H; desc. simpls. left.
    assert (Memory.closed_timemap
              (TimeMap.singleton locw (f_to' w)) memory') as NEW_CLOSE.
    { unfold TimeMap.singleton, LocFun.add.
      red. intros loc. erewrite Memory.add_o; eauto.
      destruct (Loc.eq_dec loc locw) as [|NEQ]; subst.
      { eexists; eexists; eexists. 
        rewrite loc_ts_eq_dec_eq. eauto. }
      rewrite loc_ts_eq_dec_neq.
      2: by left.
      unfold LocFun.find, LocFun.init.
      rewrite INHAB. destruct Message.elt.
      eauto. }

    assert (exists promises'', 
               if Rel w
               then Memory.remove promises' locw (f_from' w) (f_to' w) valw
                                  (Some
                                     (View.join
                                        (View.join
                                           (if Rel w
                                            then TView.cur (Local.tview local)
                                            else TView.rel (Local.tview local) locw) 
                                           (View.unwrap p_rel))
                                        (View.singleton_ur locw (f_to' w)))) promises''
               else promises'' = promises')
      as [promises'' PEQ].
    { destruct (is_rel lab w); eauto.
      apply Memory.remove_exists.
      erewrite Memory.add_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }

    assert (Memory.closed_timemap
              (TimeMap.join
                 (TimeMap.join
                    (View.rlx
                       (if Rel w
                        then TView.cur (Local.tview local)
                        else TView.rel (Local.tview local) locw))
                    (View.rlx (View.unwrap p_rel)))
                 (TimeMap.singleton locw (f_to' w))) memory') as YY.
    { apply Memory.join_closed_timemap.
      { eapply closedness_preserved_add; eauto.
        destruct (is_rel lab w); simpls.
        all: apply Memory.join_closed_timemap; auto.
        all: apply MEM_CLOSE. }
      eapply Memory.singleton_closed_timemap.
      2: by eapply Memory.add_inhabited; eauto.
      erewrite Memory.add_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }

    eexists; eexists; exists promises'; exists memory'; exists promises''; splits; eauto.
    { etransitivity; eauto.
      apply clos_rt1n_step.
      econstructor.
      { apply Memory.op_add. eauto. }
      { constructor. constructor; simpls.
        rewrite REL_PLN_RLX.
        cdes PLN_RLX_EQ.
        destruct (Rel w).
        { by rewrite EQ_CUR. }
          by rewrite EQ_REL. }
      eauto. }
    { ins.
      destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
      { rewrite EQ. rewrite IdentMap.gss.
        eexists. eauto. }
      rewrite IdentMap.gso; auto. }
    { ins.
      assert (Memory.le PC.(Configuration.memory) memory') as MM.
      { red; ins.
        erewrite Memory.add_o; eauto.
        destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
        2: by rewrite (loc_ts_eq_dec_neq LL).
        simpls; rewrite A in *; rewrite B in *.
        exfalso.
        erewrite Memory.add_get0 in LHS; eauto.
        inv LHS. }
      destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
      { subst. rewrite IdentMap.gss in TID0.
        inv TID0; simpls; clear TID0.
        assert (Memory.le promises' memory') as PP.
        { red; ins.
          erewrite Memory.add_o; eauto.
          erewrite Memory.add_o in LHS; [|by apply PADD].
          destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
          { simpls; rewrite A in *; rewrite B in *.
            rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
              by rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in LHS. }
          rewrite (loc_ts_eq_dec_neq LL).
          rewrite (loc_ts_eq_dec_neq LL) in LHS.
          eapply PROM_IN_MEM; eauto. }
        destruct (Rel w); subst; auto.
        etransitivity; eauto.
        eapply memory_remove_le; eauto. }
      red; ins; rewrite IdentMap.gso in TID0; auto.
      eapply PROM_IN_MEM in LHS; eauto. }
    { intros NFSC l; simpls.
      eapply sc_view_f_issued; eauto. }
    { eapply closedness_preserved_add; eauto. }
    { simpls. red. ins.
      destruct (is_rel lab w) eqn:WREL; subst.
      { erewrite Memory.remove_o in PROM; eauto.
        destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
        { simpls; rewrite A' in *; rewrite B' in *.
          rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM; desf. }
        rewrite (loc_ts_eq_dec_neq LL) in PROM.
        erewrite Memory.add_o in PROM; eauto.
        rewrite (loc_ts_eq_dec_neq LL) in PROM.
        edestruct SIM_PROM as [b H]; eauto; desc.
        rewrite <- ISSEQ_TO in TO; auto.
        rewrite <- ISSEQ_FROM in FROM; auto.
        exists b; splits; auto.
        { by left. }
        { intros [H|H]; desf. }
        cdes IMMCON.
        eapply sim_mem_helper_f_issued.
        6: by apply HELPER0.
        5: by apply ISSEQ_TO.
        all: auto. }
      erewrite Memory.add_o in PROM; eauto.
      destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A' B']|LL].
      { simpls; rewrite A' in *; rewrite B' in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
        destruct (is_rel lab w); simpls.
        inv PROM. exists w; splits; auto.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL) in PROM.
      edestruct SIM_PROM as [b H]; eauto; desc.
      rewrite <- ISSEQ_TO in TO; auto.
      rewrite <- ISSEQ_FROM in FROM; auto.
      exists b; splits; auto.
      { by left. }
      cdes IMMCON.
      eapply sim_mem_helper_f_issued.
      6: by apply HELPER0.
      5: by apply ISSEQ_TO.
      all: auto. }
    { ins.
      rewrite IdentMap.gso in TID'; auto.
      destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
      { desc. subst. right.
        destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
        exfalso.
        destruct p as [from msg].
        eapply PROM_IN_MEM in HH; eauto.
        erewrite Memory.add_get0 in HH; eauto.
        inv HH. }
      edestruct (PROM_DISJOINT thread') as [HH|HH]; eauto.
      left.
      destruct (Rel w); subst.
      erewrite Memory.remove_o; eauto.
      rewrite loc_ts_eq_dec_neq; auto.
      all: erewrite Memory.add_o; eauto.
      all: rewrite loc_ts_eq_dec_neq; auto. }
    { red; ins. 
      destruct ISSB as [ISSB|]; subst.
      { edestruct SIM_MEM as [rel]; eauto.
        simpls; desc.
        rewrite (ISSEQ_TO b); auto. rewrite (ISSEQ_FROM b); auto.
        exists rel; splits; auto.
        { erewrite Memory.add_o; eauto.
          destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A' B']|LL].
          2: by rewrite (loc_ts_eq_dec_neq LL).
          simpls; rewrite A' in *; rewrite B' in *.
          exfalso.
          rewrite <- ISSEQ_TO in B'; auto.
          eapply f_to_eq in B'.
          4: by apply TCCOH'.
          all: eauto.
          { by desf. }
          { red. rewrite LOC. desf. }
            by left.
            by right. }
        { eapply sim_mem_helper_f_issued.
          4: by eauto.
          all: eauto. }
        { eapply closedness_preserved_add; eauto. }
        ins. simpls.
        destruct H1 as [MM [p_rel' RR]]; auto; desc.
        { intros HH. apply H0. by destruct (Rel w); [left|]. }
        split; auto.
        { destruct (Rel w); auto.
          { erewrite Memory.remove_o; eauto.
            destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
            { simpls; rewrite A in *; rewrite B in *.
              exfalso.
              rewrite <- ISSEQ_TO in B; auto.
              eapply f_to_eq in B.
              4: by apply TCCOH'.
              all: eauto.
              { desf. }
              { red. by rewrite LOC. }
                by left.
                by right. }
            rewrite (loc_ts_eq_dec_neq LL).
            erewrite Memory.add_o; eauto. by rewrite (loc_ts_eq_dec_neq LL). }
          subst.
          erewrite Memory.add_o; eauto.
          destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
          2: by rewrite (loc_ts_eq_dec_neq LL).
          simpls; rewrite A in *; rewrite B in *.
          exfalso.
          rewrite <- ISSEQ_TO in B; auto.
          eapply f_to_eq in B.
          4: by apply TCCOH'.
          all: eauto.
          { desf. }
          { red. by rewrite LOC. }
            by left.
            by right. }
        destruct RR0 as [[RR NN]|RR].
        2: { exists p_rel'; split; auto.
             { destruct (Rel w) eqn: WREL; simpls.
               unfold LocFun.add.
               destruct (Loc.eq_dec l locw); subst; auto.
               exfalso.
               destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
               apply WNCOV. apply TCCOH in ISSB. eapply ISSB.
               2: apply H0; left; apply WISSUABLE.
               all: eexists; apply seq_eqv_r; split; auto.
               all: red; left; left.
               { right. apply seq_eqv_l; split; [by split|].
                 apply seq_eqv_r; split; [split; auto|by apply ISSB].
                 red. by rewrite LOC. }
               left. apply seq_eqv_r. split; [|split]; auto. }
             right. desc. exists p; splits; auto.
             { by left. }
             eexists; splits; eauto.
             rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto.
             erewrite Memory.add_o; eauto.
             destruct (loc_ts_eq_dec (l, f_to p) (locw, f_to' w)) as [[A B]|NEQ]; simpls. 
             2: by rewrite (loc_ts_eq_dec_neq NEQ).
             exfalso. rewrite <- ISSEQ_TO in B; auto.
             eapply f_to_eq in B.
             4: by apply TCCOH'.
             all: eauto.
             { desf. }
             { red; desc. etransitivity.
               { eapply wf_rfrmwl; eauto. }
                 by rewrite LOC; subst. }
               by left. by right. }
        destruct (classic ((rf ⨾ rmw) w b)) as [RFRMW|].
        2: { exists p_rel'. split; auto.
             { destruct (Rel w) eqn: WREL; simpls.
               unfold LocFun.add.
               destruct (Loc.eq_dec l locw); subst; auto.
               exfalso.
               destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
               apply WNCOV. apply TCCOH in ISSB. eapply ISSB.
               2: apply H0; left; apply WISSUABLE.
               all: eexists; apply seq_eqv_r; split; auto.
               all: red; left; left.
               { right. apply seq_eqv_l; split; [by split|].
                 apply seq_eqv_r; split; [split; auto|by apply ISSB].
                 red. by rewrite LOC. }
               left. apply seq_eqv_r. split; [|split]; auto. }
             left.
             splits; auto. intros [y UU]; apply RR.
             exists y. apply seq_eqv_l in UU; destruct UU as [[UU1|UU1] UU2]; [|by desf].
               by apply seq_eqv_l; split. }
        assert (Some l = Some locw) as LL.
        { rewrite <- LOC, <- LOC0. by apply wf_rfrmwl in RFRMW. }
        inv LL; clear LL.
        eexists; split.
        2: { intros. right.
             exists w; splits; auto. 
             { by right. }
             eexists; splits; eauto.
             erewrite Memory.add_o; eauto.
             rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
             eauto. }
        simpls.
        rewrite <- ISSEQ_TO; auto. rewrite NN.
        assert ((rfi ⨾ rmw) w b) as RFIRMW.
        { hahn_rewrite rfi_union_rfe in RFRMW. apply seq_union_l in RFRMW.
          destruct RFRMW as [|RFRMW]; auto. exfalso.
          apply WNISS. apply TCCOH in ISSB. apply ISSB.
          eexists. apply seq_eqv_r. split; eauto.
          apply seq_eqv_l. split; auto.
          destruct RFRMW as [oo [AA BB]].
          apply ct_ct. exists oo. split; apply ct_step.
          { red. basic_solver. }
          apply ppo_in_ar. by apply WF.(rmw_in_ppo). }
        assert ((sb ∩ same_loc lab) w b) as SBWB.
        { destruct RFIRMW as [z [RFI RMW]].
          eapply sb_same_loc_trans.
            by apply WF.(rfi_in_sbloc'); eauto.
            apply WF.(rmw_in_sb_loc); eauto. }
        assert (~ Rel w) as NREL.
        { intros REL. apply WNISS; apply TCCOH in ISSB; destruct ISSB as [[[A1 A2] A3] A4].
          eapply w_covered_issued; eauto. split; auto.
          apply A3. unfold fwbob. exists b.
          apply seq_eqv_r; split; auto. left; left; right.
          apply seq_eqv_l; split; [by split|].
          apply seq_eqv_r; split; auto. }
        destruct (is_rel lab w); simpls.
        assert (p_rel = None); subst.
        { desf. exfalso. apply WNISS.
          apply TCCOH in ISSB.
          assert (W_ex_acq w) as WEX.
          { apply ACQEX. destruct INRMW as [z [RF RFMW]].
            eexists; eauto. }
          apply ISSB.
          exists b; apply seq_eqv_r; split; auto.
          apply seq_eqv_l; split; auto.
          apply ct_step. apply w_ex_acq_sb_w_in_ar.
          apply seq_eqv_lr. splits; auto.
          { apply SBWB. }
          apply ISSB. }
        simpls.
        unfold View.unwrap. rewrite !view_join_bot_r.
        rewrite <- !View.join_assoc. rewrite view_join_id.
        rewrite !View.join_assoc.
        assert ((View.join (View.singleton_ur locw (f_to' w))
                           (View.singleton_ur locw (f_to' b))) =
                (View.singleton_ur locw (f_to' b))) as QQ.
        2: by rewrite QQ.
        assert (Time.join (f_to' w) (f_to' b) = f_to' b) as QQ.
        { apply time_join_le_r. apply Time.le_lteq; left.
          eapply f_to_co_mon; eauto.
          { eapply (rfrmw_in_im_co) in RFRMW; eauto. apply RFRMW. }
            by right. by left. }
        unfold View.singleton_ur, View.join, TimeMap.join, TimeMap.singleton,
        LocFun.add; apply View.ext; apply LocFun.ext; simpls.
        all: intros a; unfold LocFun.find; simpls; desf. }
      assert (l = locw); subst.
      { rewrite LOC in LOC0. inv LOC0. }
      assert (v = valw); subst.
      { rewrite VAL in VAL0. inv VAL0. }
      eexists; splits.
      { erewrite Memory.add_o; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
      all: simpls.
      { cdes PLN_RLX_EQ.
        destruct (is_rel lab b); simpls.
        rewrite EQ_CUR.
        2: rewrite EQ_REL.
        all: rewrite REL_PLN_RLX; reflexivity. }
      ins. destruct (Rel b); simpls; subst.
      { by exfalso; apply H0; right. }
      splits; auto.
      { erewrite Memory.add_o; eauto.
        rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
      eexists; splits; eauto.
      desf.
      { left; split; auto.
        intros [z HH]. apply seq_eqv_l in HH. destruct HH as [[ISS|]RFRMW]; subst.
        { apply NINRMW. exists z. apply seq_eqv_l. by split. }
        eapply wf_rfrmw_irr in RFRMW; eauto. }
      right. eexists; splits; eauto.
      { by left. }
      eexists; splits; eauto.
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_neq.
      { rewrite ISSEQ_TO; auto. by rewrite ISSEQ_FROM. }
      right. intros HH.
      eapply f_to_eq in HH.
      4: by apply TCCOH'.
      all: eauto.
      { by desf. }
      { red. by rewrite LOC0. }
        by left.
        by right. }
      { apply Memory.promise_add; eauto. }
      { constructor.
        assert ((fun x => View.pln x = View.rlx x)
                  (View.join (View.join (if Rel w
                                         then TView.cur (Local.tview local)
                                         else TView.rel (Local.tview local) locw)
                                        (View.unwrap p_rel))
                             (View.singleton_ur locw (f_to' w)))) as PLN_RLX.
        { unfold View.join; simpls.
          cdes PLN_RLX_EQ.
          destruct (Rel w); simpls.
          rewrite EQ_CUR.
          2: rewrite EQ_REL.
          all: by rewrite REL_PLN_RLX. }
        constructor; simpls. by rewrite PLN_RLX. }
      { destruct (Rel w) eqn: WREL; simpls.
        2: by eapply tview_closedness_preserved_add; eauto.
        unfold TView.write_tview.
        cdes MEM_CLOSE.
        red; splits; simpls.
        1,2: apply Memory.join_closed_timemap; auto.
        1,2: by eapply Memory.add_closed_timemap; eauto.
        intros loc. unfold LocFun.add.
        destruct (Loc.eq_dec loc locw) as [|NEQ]; subst.
        2: by eapply Memory.add_closed_timemap; eauto.
        destruct (Ordering.le Ordering.acqrel (wmod (mod lab w))).
        all: apply Memory.join_closed_timemap; auto.
        all: by eapply Memory.add_closed_timemap; eauto. }
      intros REL. red; ins. exfalso.
      destruct msg as [v rel].
      eapply SIM_PROM in GET; eauto. desc.
      destruct (same_thread G w b) as [[EQ|SB]|SB]; subst; auto.
      apply WNCOV. apply TCCOH in ISS. apply ISS.
      2: apply NCOV; apply WISSUABLE.
      all: eexists; apply seq_eqv_r; split; eauto.
      { red. left; left; right. apply seq_eqv_l; split; [by split|].
        apply seq_eqv_r; split; [split; auto|by apply ISS].
        by red; rewrite LOC. }
      red. repeat left. by  apply seq_eqv_r; split; [|split]. }
  red in H; desc. simpls. right.
  assert (tid w = tid ws) as TWWS.
  { destruct (sb_tid_init SBWW); desf. }
  splits; auto.

  assert (Memory.closed_timemap
            (TimeMap.join
               (TimeMap.join
                  (View.rlx (TView.rel (Local.tview local) locw))
                  (View.rlx (View.unwrap p_rel))) (TimeMap.singleton locw (f_to' w)))
            memory') as YY.
  { apply Memory.join_closed_timemap.
    { eapply closedness_preserved_split; eauto.
      apply Memory.join_closed_timemap; auto.
      apply MEM_CLOSE. }
    eapply Memory.singleton_closed_timemap.
    2: by eapply Memory.split_inhabited; eauto.
    erewrite Memory.split_o; eauto.
      by rewrite loc_ts_eq_dec_eq. }

  exists ws; exists valws; eexists; eexists; exists f_to'; exists f_from'.
  exists promises'; exists memory'.
  splits; eauto.
  { etransitivity; eauto.
    apply clos_rt1n_step.
      econstructor.
      { apply Memory.op_split. eauto. }
      { constructor. constructor; simpls.
        rewrite REL_PLN_RLX.
        cdes PLN_RLX_EQ.
          by rewrite EQ_REL. }
      eauto. }
  { ins.
    destruct (Ident.eq_dec (tid e) (tid w)) as [EQ|NEQ].
    { rewrite EQ. rewrite IdentMap.gss.
      eexists. eauto. }
    rewrite IdentMap.gso; auto. }
  { ins.
    destruct (Ident.eq_dec thread' (tid w)) as [EQ|NEQ].
    { subst. rewrite IdentMap.gss in TID0.
      inv TID0; simpls; clear TID0.
      red; ins.
      erewrite Memory.split_o; eauto.
      erewrite Memory.split_o in LHS; [|by apply PADD].
      destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
          by rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in LHS. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (loc, to) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite (loc_ts_eq_dec_neq LL) in LHS.
          by rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in LHS. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite (loc_ts_eq_dec_neq LL) in LHS.
      rewrite (loc_ts_eq_dec_neq LL') in LHS.
      eapply PROM_IN_MEM; eauto. }
    red; ins; rewrite IdentMap.gso in TID0; auto.
    assert (loc <> locw \/ to <> f_to' ws) as LL'.
    { destruct (classic (loc = locw)); [subst|by left].
      right. 
      destruct (classic (to = f_to' ws)); [subst|done].
      exfalso.
      rewrite ISSEQ_TO in LHS; auto.
      edestruct PROM_DISJOINT as [H|H].
      { intros H. apply NEQ. by rewrite H. }
      { eauto. }
      { rewrite H in WSPROM. inv WSPROM. }
      rewrite H in LHS. inv LHS. }
    eapply PROM_IN_MEM in LHS; eauto.
    erewrite Memory.split_o; eauto.
    destruct (loc_ts_eq_dec (loc, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      exfalso.
      edestruct Memory.split_get0 as [H _]; eauto.
      rewrite H in LHS. inv LHS. }
    rewrite (loc_ts_eq_dec_neq LL).
      by rewrite (loc_ts_eq_dec_neq LL'). }
  { eapply closedness_preserved_split; eauto. }
  { simpls. red. ins.
    erewrite Memory.split_o in PROM; eauto.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' w)) as [[A B]|LL].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' w)) in PROM.
      inv PROM.
      exists w; splits; auto.
        by right. }
    rewrite (loc_ts_eq_dec_neq LL) in PROM.
    destruct (loc_ts_eq_dec (l, to) (locw, f_to' ws)) as [[A B]|LL'].
    { simpls; rewrite A in *; rewrite B in *.
      rewrite (loc_ts_eq_dec_eq locw (f_to' ws)) in PROM.
      inv PROM.
      exists ws; splits; auto.
      { by apply TCCOH. }
      { by left. }
      red; splits; auto.
      { left. by eapply f_to_co_mon; eauto; [right|left]. }
      edestruct SIM_PROM as [b H]; eauto; desc.
      red in HELPER0; desc.
      destruct (classic (b = ws)) as [|NEQ]; subst. 
      { eapply (@sim_msg_f_issued f_to (upd f_to w (f_to' w)) _ _ _ TCCOH) in SIMMSG;
          eauto.
        { eapply sim_msg_f_issued.
          { apply TCCOH'. }
          5: by apply SIMMSG.
          all: eauto.
          { simpls. rewrite set_inter_union_r.
            apply set_subset_union_l; split; auto.
            generalize NREL. basic_solver. }
          { by left. }
          intros e [H|]; subst; [rewrite updo|by rewrite upds].
          { by apply ISSEQ_TO. }
            by intros HH; subst. }
        ins; rewrite updo; [done|].
          by intros HH; subst. }
      exfalso.
      rewrite <- ISSEQ_TO in TO; auto.
      (* TODO: generalize to a lemma! *)
      edestruct WF.(wf_co_total) as [CO|CO].
      3: by apply NEQ.
      1,2: split; [split|]; auto.
      1-3: by apply TCCOH.
      { by rewrite LOC0. }
      all: eapply (f_to_co_mon WF IMMCON FCOH0) in CO; [|by left|by left].
      all: rewrite TO in CO.
      all: rewrite ISSEQ_TO in CO; auto.
      all: by apply Time.lt_strorder in CO. }
    rewrite (loc_ts_eq_dec_neq LL') in PROM.
    eapply SIM_PROM in PROM; eauto.
    destruct PROM as [b H]; desc.
    exists b; splits; auto.
    { by left. }
    { rewrite <- ISSEQ_FROM in FROM; auto.
      split; auto.
      intros H; subst. simpls. desf.
      all: by apply LL'; rewrite ISSEQ_TO. }
    { rewrite <- ISSEQ_TO in TO; auto. }
    eapply sim_mem_helper_f_issued.
    6: by apply HELPER0.
    5: by apply ISSEQ_TO.
    all: auto. }
  { apply RESERVED_TIME0. }
  { apply RESERVED_TIME0. }
  { ins.
    rewrite IdentMap.gso in TID'; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' w))) as [EQ|NEQ]; simpls.
    { desc. subst. right.
      destruct (Memory.get locw (f_to' w) (Local.promises local')) eqn: HH; auto.
      exfalso.
      destruct p as [from msg].
      eapply PROM_IN_MEM in HH; eauto.
      edestruct Memory.split_get0 as [Y1 Y2].
      { apply MADD. }
      red in Y1. rewrite Y1 in HH.
      inv HH. }
    edestruct (PROM_DISJOINT thread') as [HH|HH]; eauto.
    left.
    erewrite Memory.split_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    destruct (loc_ts_eq_dec (loc, to) (locw, (f_to' ws))) as [EQ|NEQ2]; simpls.
    2: by rewrite (loc_ts_eq_dec_neq NEQ2).
    desc. subst.
    exfalso.
    edestruct Memory.split_get0 as [Y1 Y2].
    { apply PADD. }
    red in Y2. rewrite Y2 in HH.
    inv HH. }
  red; ins.
  destruct ISSB as [ISSB|]; subst.
  { edestruct SIM_MEM as [rel HY]; eauto; simpls.
    desc.
    rewrite (ISSEQ_TO b); auto.
    exists rel; splits; auto. 
    { erewrite Memory.split_o; eauto.
      (* TODO: generalize! *)
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        exfalso.
        rewrite <- ISSEQ_TO in B; auto.
        eapply f_to_eq in B.
        4: by apply TCCOH'.
        all: eauto.
        { desf. }
        { red. by rewrite LOC. }
          by left.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite FEQ1.
        destruct (classic (b = ws)) as [|NEQ]; subst.
        { edestruct Memory.split_get0 as [_ H].
          { apply MADD. }
          rewrite H in INMEM.
          inv INMEM. }
        exfalso.
        rewrite ISSEQ_TO in B.
        edestruct WF.(wf_co_total) as [CO|CO].
        3: by apply NEQ.
        1,2: split; [split|]; auto.
        1-3: by apply TCCOH.
        { by rewrite LOC0. }
        3: done.
        1,2: eapply (f_to_co_mon WF IMMCON FCOH) in CO; auto.
        1,2: rewrite B in CO.
        1,2: by apply Time.lt_strorder in CO. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite ISSEQ_FROM; [done|].
      split; auto.
      intros H; desf; simpls.
      all: apply LL'.
      all: by rewrite ISSEQ_TO. }
    { eapply sim_mem_helper_f_issued.
      5: by apply ISSEQ_TO.
      all: auto.
      red; splits; auto.
      { destruct (classic (is_init b)) as [BB|BB]; [right|left].
        { splits; auto.
          2: { apply FCOH. by split. }
          rewrite ISSEQ_FROM.
          { apply FCOH. by split. }
          split; auto. intros H; subst.
          apply WSNCOV. apply TCCOH. by split. }
        rewrite <- ISSEQ_TO; auto.
        apply FCOH0; auto. by left. }
      apply HELPER0. }
    { eapply closedness_preserved_split; eauto. }
    ins. simpls.
    destruct HY1 as [MM RR]; auto; unnw; subst.
    split.
    { erewrite Memory.split_o; eauto.
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' w)) as [[A B]|LL].
      { simpls; rewrite A in *; rewrite B in *.
        exfalso.
        rewrite <- ISSEQ_TO in B; auto.
        eapply f_to_eq in B.
        4: apply TCCOH'.
        all: eauto.
        { desf. }
        { red. by rewrite LOC0. }
          by left.
          by right. }
      rewrite (loc_ts_eq_dec_neq LL).
      destruct (loc_ts_eq_dec (l, f_to b) (locw, f_to' ws)) as [[A B]|LL'].
      { simpls; rewrite A in *; rewrite B in *.
        rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
        rewrite FEQ1.
        destruct (classic (b = ws)) as [|NEQ]; subst.
        { edestruct Memory.split_get0 as [_ HH].
          { apply MADD. }
          rewrite HH in INMEM.
          inv INMEM. }
        exfalso.
        rewrite ISSEQ_TO in B.
        edestruct WF.(wf_co_total) as [CO|CO].
        3: by apply NEQ.
        1,2: split; [split|]; auto.
        1-3: by apply TCCOH.
        { by rewrite LOC0. }
        1,2: eapply (f_to_co_mon WF IMMCON FCOH) in CO; auto.
        1,2: rewrite B in CO.
        1,2: by apply Time.lt_strorder in CO.
        done. }
      rewrite (loc_ts_eq_dec_neq LL').
      rewrite ISSEQ_FROM; [done|].
      split; auto.
      intros HH; subst; simpls.
      destruct LL' as [LL'|LL'].
      2: by apply LL'; rewrite ISSEQ_TO.
      rewrite SAME_LOC in LOC0. inv LOC0. }
    destruct RR as [p_rel' [FF [[RR NN]|RR]]].
    2: { exists p_rel'; split; auto.
         right. desc. exists p; splits; auto.
         { by left. }
         eexists; splits; eauto.
         erewrite Memory.split_o; eauto.
         destruct (loc_ts_eq_dec (l, f_to' p) (locw, f_to' w)) as [[A B]|NEQ]; simpls. 
         2: { rewrite (loc_ts_eq_dec_neq NEQ).
              destruct (loc_ts_eq_dec (l, f_to' p) (locw, f_to' ws)) as [[A B]|NEQ'];
                simpls. 
              2: { intros. rewrite (loc_ts_eq_dec_neq NEQ').
                   rewrite ISSEQ_TO; auto.
                   rewrite ISSEQ_FROM; auto.
                   split; auto. intros HH; subst.
                   destruct NEQ' as [NN|NN]; [|by desf].
                   apply WF.(wf_rfrmwl) in RR0. red in RR0.
                   rewrite LOC0 in RR0. rewrite SAME_LOC in RR0.
                   inv RR0. }
              rewrite A in *; rewrite B in *.
              rewrite (loc_ts_eq_dec_eq locw (f_to' ws)).
              assert (p = ws); subst.
              { eapply f_to_eq.
                3: by apply TCCOH'.
                all: eauto.
                { apply WF.(wf_rfrmwl) in RR0.
                  red. rewrite SAME_LOC. by rewrite RR0. }
                all: by left. }
              rewrite FEQ1. rewrite WSVAL in RR1. inv RR1. }
         rewrite A in *; rewrite B in *.
         rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
         assert (p = w); subst.
         { eapply f_to_eq.
           3: by apply TCCOH'.
           all: eauto.
           { apply WF.(wf_rfrmwl) in RR0.
             red. rewrite LOC. by rewrite RR0. }
             by left. by right. }
         rewrite VAL in RR1. inv RR1. }
    destruct (classic ((rf ⨾ rmw) w b)) as [RFRMW|].
    2: { exists p_rel'. split; auto. left.
         splits; auto. intros [y UU]; apply RR.
         exists y. apply seq_eqv_l in UU; destruct UU as [[UU1|UU1] UU2]; [|by desf].
           by apply seq_eqv_l; split. }
    assert (Some l = Some locw) as LL.
    { rewrite <- LOC, <- LOC0. by apply wf_rfrmwl in RFRMW. }
    inv LL; clear LL.
    eexists; split.
    2: { intros. right.
         exists w; splits; auto. 
         { by right. }
         eexists; splits; eauto.
         erewrite Memory.split_o; eauto.
         rewrite (loc_ts_eq_dec_eq locw (f_to' w)).
         eauto. }
    simpls.
    assert (p_rel = None); subst.
    2: { simpls.
         unfold View.unwrap. rewrite !view_join_bot_r.
         rewrite <- !View.join_assoc. rewrite view_join_id.
         rewrite !View.join_assoc.
         assert ((View.join (View.singleton_ur locw (f_to' w))
                            (View.singleton_ur locw (f_to b))) =
                 (View.singleton_ur locw (f_to b))) as QQ; [|by rewrite QQ].
         rewrite <- ISSEQ_TO; auto. 
         assert (Time.join (f_to' w) (f_to' b) = f_to' b) as QQ.
         { apply time_join_le_r. apply Time.le_lteq; left.
           eapply f_to_co_mon; eauto.
           { eapply rfrmw_in_im_co in RFRMW; eauto. apply RFRMW. }
             by right. by left. }
         unfold View.singleton_ur, View.join, TimeMap.join, TimeMap.singleton,
         LocFun.add; apply View.ext; apply LocFun.ext; simpls.
         all: intros a; unfold LocFun.find; simpls; desf. }
    desf.
    hahn_rewrite rfi_union_rfe in RFRMW. apply seq_union_l in RFRMW.
    destruct RFRMW as [RFRMW|RFRMW]; exfalso.
    all: apply WNISS; apply TCCOH in ISSB; destruct ISSB as [A1 A2]. 
    2: { apply A2. eexists. apply seqA. apply seq_eqv_lr. splits; eauto.
         destruct RFRMW as [oo [AA BB]].
         apply ct_ct. exists oo. split; apply ct_step.
         { red. basic_solver. }
         apply ppo_in_ar. by apply WF.(rmw_in_ppo). }
    apply A2.
    assert (W_ex_acq w) as WEX.
    { apply ACQEX. destruct P_REL_CH1 as [z [RF RFMW]].
      eexists; eauto. }
    exists b; apply seq_eqv_r; split; auto.
    apply seq_eqv_l; split; auto.
    destruct RFRMW as [z [RF RMW]].
    apply ct_step. apply w_ex_acq_sb_w_in_ar.
    apply seq_eqv_l. split.
    { apply ACQEX. apply WEX. }
    apply seq_eqv_r. split; auto.
    { eapply sb_trans. by apply WF.(rfi_in_sbloc'); eauto.
        by apply WF.(wf_rmwi). }
    apply (dom_r WF.(wf_rmwD)) in RMW. apply seq_eqv_r in RMW. apply RMW. }
  assert (l = locw); subst.
  { rewrite LOC in LOC0; inv LOC0. }
  assert (v = valw); subst.
  { rewrite VAL in VAL0; inv VAL0. }
  eexists; splits.
  { erewrite Memory.split_o; eauto.
    rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
  all: simpls.
  { cdes PLN_RLX_EQ. rewrite EQ_REL. rewrite REL_PLN_RLX. reflexivity. }
  { ins; splits; auto.
    { erewrite Memory.split_o; eauto.
      rewrite (loc_ts_eq_dec_eq locw (f_to' b)); eauto. }
    eexists; split; eauto.
    desf.
    { left; split; auto.
      intros [z HH]. apply seq_eqv_l in HH. destruct HH as [[ISS|]RFRMW]; subst.
      { apply NINRMW. exists z. apply seq_eqv_l. by split. }
      eapply wf_rfrmw_irr in RFRMW; eauto. }
    right. eexists; splits; eauto.
    { by left. }
    eexists; splits; eauto.
    erewrite Memory.split_o; eauto.
    assert (p <> b) as PNEQ.
    { intros HH; subst. eapply wf_rfrmw_irr in INRMW; eauto. }
    assert (p <> ws) as PWNEQ.
    { intros HH; subst.
      cdes IMMCON. eapply Cint.
      exists ws; split.
      { apply sb_in_hb; eauto. }
      edestruct INRMW as [z [RF RMW]].
      apply r_step.
      eapply WF.(eco_trans).
      { apply G.(rf_in_eco); eauto. }
      apply fr_in_eco; auto. apply rmw_in_fr; auto.
        by apply coherence_sc_per_loc. }
    rewrite loc_ts_eq_dec_neq.
    { rewrite loc_ts_eq_dec_neq.
      { rewrite ISSEQ_TO; auto. rewrite ISSEQ_FROM; auto. split; auto. }
      right. intros HH.
      apply PWNEQ. eapply f_to_eq.
      3: by eauto.
      all: eauto.
      { red. by rewrite SAME_LOC. }
      all: by left. }
    right. intros HH.
    apply PNEQ. eapply f_to_eq.
    3: by apply TCCOH'.
    all: eauto.
    { red. by rewrite LOC0. }
      by left.
      by right. }
  { apply Memory.promise_split; eauto. }
  constructor.
  assert ((fun x => View.pln x = View.rlx x)
            (View.join (View.join (TView.rel (Local.tview local) locw)
                                  (View.unwrap p_rel))
                       (View.singleton_ur locw (f_to' w)))) as PLN_RLX.
  { unfold View.join; simpls.
    cdes PLN_RLX_EQ. rewrite EQ_REL. by rewrite REL_PLN_RLX. }
  constructor; simpls. by rewrite PLN_RLX.
Qed.

End Aux.
