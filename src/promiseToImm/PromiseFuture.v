From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Configuration TView View Time Event Cell Thread Memory.
Require Import MaxValue.
Require Import MemoryAux.

Set Implicit Arguments.
Remove Hints plus_n_O.

(* Proposition "up_memory memory memory'" states that each message in memory' has
   a counterpart in memory w/ smaller or equal left timestamp border. *)
Record up_memory memory memory' :=
  { TOU :
      forall loc t val f' view'
             (INT : Memory.get loc t memory' =
                    Some (f', Message.mk val view')),
      exists f view,
        ⟪ INF : Memory.get loc t memory =
                 Some (f, Message.mk val view) ⟫ /\
        ⟪ FFT : Time.le f' f ⟫ /\
        ⟪ VVT : View.opt_le view view' ⟫ ;
    TOUIN :
      forall loc t' val' f' view' m
             (IMU : Interval.mem (f', t') m)
             (INT : Memory.get loc t' memory' =
                    Some (f', Message.mk val' view')),
      exists t f val view,
        ⟪ INF : Memory.get loc t memory =
                 Some (f, Message.mk val view) ⟫ /\
        ⟪ IMP : Interval.mem (f, t) m ⟫ ;
    FROMU :
      forall loc t val f view
             (INT : Memory.get loc t memory =
                    Some (f, Message.mk val view)),
      exists f' t' val' view',
        ⟪ INT : Memory.get loc t' memory' =
                 Some (f', Message.mk val' view') ⟫ /\
        ⟪ ILE : Interval.le (f, t) (f', t') ⟫;
  }.

Lemma up_memory_refl memory :
  up_memory memory memory.
Proof.
  constructor; ins.
  { eexists. eexists. splits; eauto.
    all: reflexivity. }
  { repeat eexists; eauto.
    all: apply IMU. }
  repeat eexists; eauto.
  all: reflexivity.
Qed.

Lemma exists_all_conj_disj (A B : Type) (P Q R : A -> B -> Prop)
      (HH : exists f, forall a : A, P a f /\ Q a f /\ R a f) :
  exists f, (forall a : A, P a f) /\ (forall a : A, Q a f) /\
            (forall a : A, R a f).
Proof. desf. exists f. splits; apply HH. Qed.

Require Import Logic.IndefiniteDescription.

Lemma up_memory_closed_bigger_timemap memory memory' tmap
      (FUTURE  : Memory.future Memory.init memory)
      (INHAB   : Memory.inhabited memory')
      (TM_CLOS : Memory.closed_timemap tmap memory)
      (UP_MEM  : up_memory memory memory') :
  exists tmap',
    ⟪ TM_LE  : TimeMap.le tmap tmap' ⟫ /\
    ⟪ TM_CLOS : Memory.closed_timemap tmap' memory' ⟫ /\
    ⟪ TM_EQ :
      forall loc to from val view view'
             (TS_LT'     : ts_lt_or_bot memory')
             (MSG_DISJ   : message_disjoint memory')
             (GET  : Memory.get loc to memory =
                     Some (from, Message.mk val view))
             (GET' : Memory.get loc to memory' =
                     Some (from, Message.mk val view'))
             (TLE  : Time.le (tmap loc) to),
        Time.le (tmap' loc) to ⟫.
Proof.
  unnw.
  unfold TimeMap.le.
  unfold Memory.closed_timemap.
  unfold TimeMap.t.
  apply exists_all_conj_disj.

  set (R := fun a b =>
    Time.le (tmap a) b /\
    (exists (from : Time.t) (val : Const.t) (released : option View.t),
       Memory.get a b memory' =
       Some (from, {| Message.val := val; Message.released := released |})) /\
    (forall to from val view view',
        ts_lt_or_bot memory' ->
        message_disjoint memory' ->
        Memory.get a to memory =
          Some (from, Message.mk val view) ->
        Memory.get a to memory' =
          Some (from, Message.mk val view') ->
        Time.le (tmap a) to ->
        Time.le b to)).
  apply functional_choice with (R:=R).
  unfold R. clear R.
  intros l.
  specialize (TM_CLOS l). desf.
  
  set (GET := TM_CLOS).
  apply ts_lt_or_bot_future_init in GET; auto.
  desf.
  { eexists. splits; auto.
    { reflexivity. }
    2: by ins.
    rewrite GET in *. repeat eexists.
    apply INHAB. }
  assert (tmap l <> Time.bot) as XX.
  { intros HH. rewrite HH in *.
    eapply MaxValue.time_lt_bot. eauto. }
  set (TM_CLOS' := TM_CLOS).
  eapply UP_MEM in TM_CLOS'.
  desf.
  eexists. splits; eauto.
  { apply ILE. }
  ins.
  destruct (Time.le_lt_dec t' to) as [|LT]; auto.
  exfalso.
  
  set (CC := H2).
  eapply H in CC.
  desf.
  { apply Time.le_lteq in H3.
    desf. eapply MaxValue.time_lt_bot; eauto. }
  eapply H0 in H2. apply H2 in INT.
  destruct INT as [AA|AA].
  { subst. eapply Time.lt_strorder. eauto. }
  eapply AA; constructor; simpls.
  2: reflexivity.
  { done. }
  2: { apply Time.le_lteq. by left. }
  eapply TimeFacts.lt_le_lt; eauto.
  eapply TimeFacts.le_lt_lt.
  { apply ILE. }
  simpls.
Qed.

Lemma up_memory_closed_bigger_view memory memory' view
      (FUTURE  : Memory.future Memory.init memory)
      (INHAB   : Memory.inhabited memory')
      (VW_CLOS : Memory.closed_opt_view view memory)
      (VW_WF : View.opt_wf view)
      (UP_MEM : up_memory memory memory') :
  exists view',
    ⟪ VW_LE  : View.opt_le view view' ⟫ /\
    ⟪ VW_CLOS : Memory.closed_opt_view view' memory' ⟫ /\
    ⟪ VW_WF : View.opt_wf view' ⟫ /\
    ⟪ VW_EQ :
      forall loc to from val released released'
             (TS_LT'     : ts_lt_or_bot memory')
             (MSG_DISJ   : message_disjoint memory')
             (GET  : Memory.get loc to memory =
                     Some (from, Message.mk val released))
             (GET' : Memory.get loc to memory' =
                     Some (from, Message.mk val released'))
             (TLE  : Time.le (View.rlx (View.unwrap view) loc) to),
        Time.le (View.rlx (View.unwrap view') loc) to ⟫.
Proof.
  destruct view as [view|].
  2: { exists None. splits; auto.
       { reflexivity. }
       constructor. }
  destruct view as [tmap_pln tmap].
  edestruct up_memory_closed_bigger_timemap with
      (memory:=memory) (memory':=memory') as [tmap']; eauto.
  { inv VW_CLOS. destruct CLOSED. apply RLX. }
  desc.
  exists (Some (View.mk tmap' tmap')).
  splits; auto.
  { constructor. constructor; simpls.
    etransitivity; eauto.
    inv VW_WF. inv WF. }
  { constructor. constructor; simpls. }
  constructor. constructor.
  reflexivity.
Qed.

Lemma up_memory_add_exists_r_view_eq memory memory' memory_add
           loc from to val released released'
           (ADD      : Memory.add memory loc from to val released memory_add)
           (VW_WF    : View.opt_wf released')
           (LE       : View.opt_le released released')
           (UP_MEM   : up_memory memory memory') :
  exists memory_add',
    ⟪ ADDU       : Memory.add memory' loc from to val released' memory_add' ⟫ /\
    ⟪ UP_MEM_ADD : up_memory memory_add memory_add' ⟫.
Proof.
  assert (ADD':=ADD).
  destruct ADD'. destruct ADD0.
  edestruct Memory.add_exists with (mem1:=memory') (released:=released')
    as [memory_add' MM]; eauto.
  { ins. destruct msg2 as [v rel].
    red. ins.
    eapply UP_MEM in RHS; eauto. desc.
    eapply DISJOINT; eauto. }
  exists memory_add'. splits; eauto.
  constructor; ins.
  { erewrite Memory.add_o; eauto.
    erewrite Memory.add_o in INT; eauto.
    destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
    2: by apply UP_MEM.
    desf. repeat eexists; unnw; auto.
    reflexivity. }
  { erewrite Memory.add_o in INT; eauto.
    desf.
    { simpls. desf.
      repeat eexists.
      2,3: by apply IMU.
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_eq; eauto. }
    eapply UP_MEM in IMU; eauto.
    desc.
    repeat eexists.
    2,3: by apply IMP.
    eapply Memory.add_get1; eauto. }
  erewrite Memory.add_o in INT; eauto.
  destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
  { desf. repeat eexists; eauto.
    2,3: reflexivity.
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_eq. eauto. }
  apply UP_MEM in INT. desc.
  destruct ILE.
  repeat eexists; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma up_memory_add_bigger_view memory_add memory' memory_add''
           loc from to val released released'
           (VW_LE : View.opt_le released released')
           (VW_WF : View.opt_wf released')
           (ADDU : Memory.add memory' loc from to val released memory_add'')
           (UP_MEM_ADD : up_memory memory_add memory_add'') :
  exists memory_add',
    ⟪ ADDU : Memory.add memory' loc from to val released' memory_add' ⟫ /\
    ⟪ UP_MEM_ADD : up_memory memory_add memory_add' ⟫.
Proof.
  inv ADDU. inv ADD.
  edestruct Memory.add_exists with (released:=released')
    as [memory_add' ADD']; eauto.
  eexists. splits; eauto.
  constructor; ins.
  { assert (exists view'',
               ⟪ VLE : View.opt_le view'' view' ⟫ /\
               ⟪ INT' :
                 Memory.get loc0 t (LocFun.add loc r memory') =
                 Some (f', Message.mk val0 view'') ⟫) as [view''].
    { erewrite Memory.add_o in INT; eauto.
      desf.
      { simpls; desf.
        eexists. splits; eauto.
        erewrite Memory.add_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_neq; auto.
      eexists. splits; [|by eauto].
      reflexivity. }
    desc.
    eapply (TOU UP_MEM_ADD) in INT'.
    desc. eexists. eexists.
    splits; eauto. etransitivity; eauto. }
  { assert (exists view'',
               ⟪ VLE : View.opt_le view'' view' ⟫ /\
               ⟪ INT' :
                 Memory.get loc0 t' (LocFun.add loc r memory') =
                 Some (f', Message.mk val' view'') ⟫) as [view''].
    { erewrite Memory.add_o in INT; eauto.
      desf.
      { simpls; desf.
        eexists. splits; eauto.
        erewrite Memory.add_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_neq; auto.
      eexists. splits; [|by eauto].
      reflexivity. }
    desc.
    eapply (TOUIN UP_MEM_ADD) in INT'; eauto. }
  eapply (FROMU UP_MEM_ADD) in INT; eauto.
  desc.
  erewrite Memory.add_o in INT0; eauto.
  desf.
  { simpls; desf. repeat eexists.
    2,3: by apply ILE.
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_eq. by unnw. }
  repeat eexists.
  2,3: by apply ILE.
  erewrite Memory.add_o; eauto.
  rewrite loc_ts_eq_dec_neq; auto. eauto.
Qed.

Lemma up_memory_add_exists_r memory memory' memory_add
           loc from to val released
           (FUTURE  : Memory.future Memory.init memory)
           (FUTURE' : Memory.future Memory.init memory')
           (FUTURE_ADD : Memory.future memory memory_add)
           (VW_CLOS : Memory.closed_opt_view released memory_add)
           (ULE : Time.le (View.rlx (View.unwrap released) loc) to)
           (ADD : Memory.add memory loc from to val released memory_add)
           (UP_MEM: up_memory memory memory') :
  exists released' memory_add',
    ⟪ LE : View.opt_le released released' ⟫ /\
    ⟪ VW_WF : View.opt_wf released' ⟫ /\
    ⟪ ADDU : Memory.add memory' loc from to val released' memory_add' ⟫ /\
    ⟪ FUTURE : Memory.future Memory.init memory_add' ⟫ /\
    ⟪ UP_MEM_ADD : up_memory memory_add memory_add' ⟫.
Proof.
  assert (View.opt_wf released) as VW_WF.
  { inv ADD. inv ADD0. }
  edestruct up_memory_add_exists_r_view_eq as [memory_add'']; eauto.
  { reflexivity. }
  desc.
  edestruct up_memory_closed_bigger_view with
      (memory:=memory_add) (memory':=memory_add'') as [released']; eauto.
  { etransitivity; [|by eauto].
    done. }
  { eapply Memory.add_inhabited; eauto.
      by apply inhabited_future_init. }
  desc.
  edestruct up_memory_add_bigger_view as [memory_add']; eauto.
  desc.
  eexists. eexists. splits; eauto.
  etransitivity; eauto.
  apply clos_rt1n_step.

  assert (Time.le (View.rlx (View.unwrap released') loc) to) as TT.
  { eapply VW_EQ; eauto.
    { eapply ts_lt_or_bot_add; [|by eauto].
        by apply ts_lt_or_bot_future_init. }
    { eapply message_disjoint_add; eauto.
        by apply message_disjoint_future_init. }
    all: erewrite Memory.add_o; eauto.
    all: by rewrite loc_ts_eq_dec_eq. }

  econstructor.
  { apply Memory.op_add. eauto. }
  2: done.
  eapply Memory.add_closed with (mem1:=memory') (released:=released'); eauto.
  { eapply Memory.future_closed; eauto.
    apply Memory.init_closed. }
  2: { erewrite Memory.add_o; eauto.
         by rewrite loc_ts_eq_dec_eq. }
  destruct released'; constructor.
  inv VW_CLOS0.
  destruct CLOSED as [AA BB].
  red in AA. red in BB.
  clear -AA BB ADDU ADDU0.
  constructor.
  all: red; intros loc'.
  all:  specialize (AA loc'); specialize (BB loc').
  all: desc.
  all: erewrite Memory.add_o; eauto.
  all: erewrite Memory.add_o in AA; [|by eauto].
  all: erewrite Memory.add_o in BB; [|by eauto].
  all: desf; eauto.
Qed.

Lemma up_memory_add_exists_l memory memory' memory_add'
           loc from to val released released'
           (ADD : Memory.add memory' loc from to val released' memory_add')
           (MSG_DISJ : message_disjoint memory)
           (TS_LT    : ts_lt_or_bot memory)
           (INHAB'   : Memory.inhabited memory')
           (LE : View.opt_le released released')
           (VWF : View.opt_wf released)
           (UP_MEM: up_memory memory memory') :
  exists memory_add,
    ⟪ ADDU : Memory.add memory loc from to val released memory_add ⟫ /\
    ⟪ UP_MEM_ADD : up_memory memory_add memory_add' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_add ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_add ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_add' ⟫.
Proof.
  assert (ADD':=ADD).
  destruct ADD'. destruct ADD0.
  edestruct Memory.add_exists with (mem1:=memory) (released:=released)
    as [memory_add MM]; eauto.
  { ins. destruct msg2 as [v rel].
    apply (FROMU UP_MEM) in GET2.
    desc. apply DISJOINT in INT.
    symmetry.
    eapply Interval.le_disjoint; eauto.
    by symmetry. }
  exists memory_add; splits; eauto.
  4: by eapply Memory.add_inhabited; eauto.
  3: by eapply ts_lt_or_bot_add; eauto.
  2: by eapply message_disjoint_add; eauto.
  constructor; ins.
  { erewrite Memory.add_o; eauto.
    erewrite Memory.add_o in INT; eauto.
    destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
    2: by apply UP_MEM.
    desf. repeat eexists; unnw; auto.
    reflexivity. }
  { erewrite Memory.add_o in INT; eauto.
    desf.
    { simpls. desf.
      repeat eexists.
      2,3: by apply IMU.
      erewrite Memory.add_o; eauto.
      rewrite loc_ts_eq_dec_eq; eauto. }
    eapply UP_MEM in IMU; eauto. desc.
    repeat eexists.
    2,3: by apply IMP.
    eapply Memory.add_get1; eauto. }
  erewrite Memory.add_o in INT; eauto.
  destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
  { desf. repeat eexists; eauto.
    2,3: reflexivity.
    erewrite Memory.add_o; eauto.
    rewrite loc_ts_eq_dec_eq. eauto. }
  apply UP_MEM in INT. desc.
  destruct ILE.
  repeat eexists; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma up_memory_add_exists_l_view_eq memory memory' memory_add'
           loc from to val released
           (ADD : Memory.add memory' loc from to val released memory_add')
           (MSG_DISJ : message_disjoint memory)
           (TS_LT    : ts_lt_or_bot memory)
           (INHAB'   : Memory.inhabited memory')
           (UP_MEM: up_memory memory memory') :
  exists memory_add,
    ⟪ ADDU : Memory.add memory loc from to val released memory_add ⟫ /\
    ⟪ UP_MEM_ADD : up_memory memory_add memory_add' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_add ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_add ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_add' ⟫.
Proof.
  eapply up_memory_add_exists_l; eauto.
  { reflexivity. }
  inv ADD. inv ADD0.
Qed.

Lemma up_memory_closed_view view memory memory'
      (UP_MEM : up_memory memory memory')
      (CLOS : Memory.closed_view view memory') :
  Memory.closed_view view memory.
Proof.
  destruct CLOS.
  constructor; red; ins.
  2: specialize (RLX loc).
  specialize (PLN loc).
  all: desc.
  2: apply UP_MEM in RLX.
  apply UP_MEM in PLN.
  all: desc.
  all: repeat eexists; eauto.
Qed.

Lemma up_memory_closed_opt_view view memory memory'
      (UP_MEM : up_memory memory memory')
      (CLOS : Memory.closed_opt_view view memory') :
  Memory.closed_opt_view view memory.
Proof.
  destruct view.
  2: by apply Memory.closed_opt_view_none.
  apply Memory.closed_opt_view_some.
  inv CLOS.
  eapply up_memory_closed_view; eauto.
Qed.

(* TODO: add explanation *)
Lemma future_memory_to_append_memory
      memory memory'
      (FUTURE_INIT : Memory.future Memory.init memory)
      (FUTURE : Memory.future memory memory') :
  exists memory'',
    ⟪ FUTURE : Memory.future Memory.init memory'' ⟫ /\
    ⟪ MEM_LE   : Memory.le memory memory'' ⟫ /\
    ⟪ UP_MEM   : up_memory memory' memory'' ⟫.
Proof.
  assert (Memory.future Memory.init memory') as FUTURE_INIT'.
  { etransitivity; eauto. }
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE.
  { eexists. splits; eauto.
    { reflexivity. }
    apply up_memory_refl. }
  assert (Memory.future Memory.init y) as YY.
  { etransitivity; [by apply FUTURE_INIT|].
    apply clos_rt_rt1n_iff.
      by apply clos_rt_rtn1_iff. }
  destruct IHFUTURE as [memory'']; auto.
  desc.
  set (H':=H).
  destruct H'.
  destruct OP.
  { edestruct up_memory_add_exists_r with
        (released:=released) (memory:=y) (memory':=memory'') (memory_add:=z)
      as [released' [memory_add]]; eauto.
    { by apply clos_rt1n_step. }
    desc.
    exists memory_add. splits; auto.
    etransitivity; eauto.
    eapply memory_add_le; eauto. }
  2: { exists memory''. splits; auto.
       constructor; ins.
       { apply (TOU UP_MEM) in INT.
         desc.
         assert (UU := INF). 
         eapply Memory.lower_get1 in UU; eauto.
         desc. rewrite UU.
         eexists. eexists. splits; eauto.
         etransitivity; eauto. }
       { ins. eapply (TOUIN UP_MEM) in INT; eauto.
         desc.
         eapply Memory.lower_get1 in INF; eauto.
         desc. repeat eexists; eauto.
         all: apply IMP. }
       erewrite Memory.lower_o in INT; eauto.
       destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
       2: by eapply FROMU; eauto.
       desf.
       destruct LOWER. destruct LOWER.
       eapply FROMU in GET2; eauto. }
  exists memory''. splits; auto.
  constructor; ins.
  { apply (TOU UP_MEM) in INT. desc.
    assert (UU := INF).
    eapply Memory.split_get1 in UU; eauto.
    desc. rewrite UU.
    eexists. eexists. splits; eauto. }
  { eapply UP_MEM in IMU; eauto. desc.
    destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls; subst.
    { edestruct Memory.split_get0 as [HH _]; eauto.
      rewrite HH in INF. inv INF. }
    destruct (loc_ts_eq_dec (loc0, t) (loc, to3)) as [[BB CC]|BB]; simpls; subst.
    2: { repeat eexists.
         2,3: by apply IMP.
         erewrite Memory.split_o; eauto.
         repeat (rewrite loc_ts_eq_dec_neq; eauto). }
    assert (f = from); subst.
    { destruct SPLIT. destruct SPLIT.
      unfold Memory.get, Cell.get in INF.
      rewrite GET2 in INF. desf. }
    destruct (Time.le_lt_dec m to) as [BB|BB].
    { repeat eexists.
      3: by apply BB.
      2: by apply IMP.
      erewrite Memory.split_o; eauto.
      rewrite loc_ts_eq_dec_eq.
      eauto. }
    exists to3. exists to. repeat eexists; simpls.
    2: by apply IMP.
    erewrite Memory.split_o; eauto.
    rewrite loc_ts_eq_dec_neq; auto.
    rewrite loc_ts_eq_dec_eq; auto. }
  erewrite Memory.split_o in INT; eauto.
  destruct (loc_ts_eq_dec (loc0, t) (loc, to)) as [[AA BB]|AA]; simpls.
  { desf.
    destruct SPLIT. destruct SPLIT.
    eapply FROMU in GET2; eauto. desc.
    eexists. eexists. eexists. eexists.
    splits; eauto.
    destruct ILE.
    constructor; splits; simpls.
    apply Time.le_lteq. left.
    eapply TimeFacts.lt_le_lt; eauto. }
  destruct (loc_ts_eq_dec (loc0, t) (loc, to3)) as [[BB CC]|BB]; simpls.
  2: by eapply FROMU; eauto.
  desf.
  destruct SPLIT. destruct SPLIT.
  eapply FROMU in GET2; eauto. desc.
  eexists. eexists. eexists. eexists.
  splits; eauto.
  destruct ILE.
  constructor; simpls.
  apply Time.le_lteq. left.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma up_memory_split_exists memory memory' memory_split'
      loc from to ts val val' released released' view
      (UP_MEM   : up_memory memory memory')
      (MSG_DISJ : message_disjoint memory)
      (TS_LT    : ts_lt_or_bot memory)
      (INHAB'   : Memory.inhabited memory')
      (VWF : View.opt_wf released)
      (VLE : View.opt_le released released')
      (SP' : Memory.split
               memory' loc from to ts val val' released' view memory_split')
      (GET : Memory.get loc ts memory = Some (from, Message.mk val' view)):
  exists memory_split,
    ⟪ SP : Memory.split memory loc from to ts val val' released view memory_split ⟫ /\
    ⟪ UP_SP : up_memory memory_split memory_split' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_split ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_split ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_split' ⟫.
Proof.
  assert (Memory.get loc ts memory' = Some (from, Message.mk val' view)) as GET'.
  { eapply memory_split_get_old. eauto. }
  assert (ts <> to) as TT.
  { intros HH. subst. inv SP'. inv SPLIT.
      by apply Time.lt_strorder in TS23. }
  set (SP'' := SP'). destruct SP''.
  destruct SPLIT.
  edestruct Memory.split_exists with (mem1:=memory) (released2:=released) as [memory_split];
    eauto.
  exists memory_split. splits; eauto.
  constructor; ins.
  { erewrite Memory.split_o in INT; eauto.
    erewrite Memory.split_o; eauto.
    desf; simpls; desc; subst.
    3: by apply UP_MEM.
    all: eexists; eexists; splits; eauto; reflexivity. }
  { erewrite Memory.split_o in INT; eauto.
    desf; simpls; desc; subst.
    { repeat eexists; simpls; eauto.
      2,3: by apply IMU.
      erewrite Memory.split_o; eauto.
      rewrite loc_ts_eq_dec_eq; simpls. }
    { repeat eexists; simpls; eauto.
      2,3: by apply IMU.
      erewrite Memory.split_o; eauto.
      rewrite loc_ts_eq_dec_neq; simpls.
      rewrite (loc_ts_eq_dec_eq loc ts); simpls. }
    eapply (TOUIN UP_MEM) in INT; eauto. desc.
    destruct (loc_ts_eq_dec (loc0,t) (loc,ts)) as [[AA BB]|BB]; simpls; subst.
    { destruct (Time.le_lt_dec m to) as [LL|LL].
      { repeat eexists; simpls; eauto.
        2: by apply IMP.
        erewrite Memory.split_o; eauto.
        rewrite loc_ts_eq_dec_eq; simpls.
        rewrite INF in GET. inv GET. }
      repeat eexists; simpls; eauto.
      2: by apply IMP.
      erewrite Memory.split_o; eauto.
      erewrite loc_ts_eq_dec_neq; eauto.
      erewrite loc_ts_eq_dec_eq; eauto. }
    repeat eexists; simpls; eauto.
    2,3: by apply IMP.
    simpls.
    erewrite Memory.split_o; eauto.
    repeat erewrite loc_ts_eq_dec_neq; eauto.
    destruct (classic (loc0 = loc)) as [|LNEQ]; [subst; right| by left].
    intros HH. subst.
    edestruct Memory.split_get0 as [AA]; eauto.
    rewrite AA in INF. inv INF. }
  4: by eapply Memory.split_inhabited; eauto.
  3: by eapply ts_lt_or_bot_split; eauto.
  2: by eapply message_disjoint_split; eauto.
  ins.
  erewrite Memory.split_o in INT; eauto.
  desf; simpls; desc; subst.
  { repeat eexists; simpls.
    2,3: reflexivity.
    erewrite Memory.split_o; eauto.
    rewrite loc_ts_eq_dec_eq; eauto. }
  { repeat eexists; simpls.
    2,3: reflexivity.
    erewrite Memory.split_o; eauto.
    rewrite loc_ts_eq_dec_neq; eauto.
    rewrite loc_ts_eq_dec_eq; eauto. }
  set (INT' := INT).
  apply (FROMU UP_MEM) in INT'. desc.
  destruct (loc_ts_eq_dec (loc0,t') (loc,ts)) as [[AA BB]|BB]; simpls; subst.
  2: { repeat eexists; simpls; eauto.
       2,3: by apply ILE.
       simpls.
       erewrite Memory.split_o; eauto.
       repeat erewrite loc_ts_eq_dec_neq; eauto.
       destruct (classic (loc0 = loc)) as [|LNEQ]; [subst; right| by left].
       intros HH. subst.
       clear -INT0 SP'.
       edestruct Memory.split_get0 as [AA]; eauto.
       rewrite AA in INT0. inv INT0. }
  desf.
  set (UU := INT).
  eapply TS_LT in UU; eauto. desf.
  { assert (Memory.inhabited (LocFun.add loc r memory')) as XX.
    { eapply Memory.split_inhabited; eauto. }
    repeat eexists.
    2,3: reflexivity.
    apply XX. }
  desf.
  exfalso.
  clear -ILE o0 GET INT H FTLT MSG_DISJ.
  eapply interval_le_not_disjoint.
  3,4: by eauto.
  all: eauto.
  { inv ILE. simpls.
    eapply TimeFacts.lt_le_lt; eauto.
    eapply TimeFacts.le_lt_lt; eauto. }
  eapply MSG_DISJ in INT; eauto. eapply INT in GET; eauto.
  desf.
Qed.

Lemma up_memory_split_exists_view_eq memory memory' memory_split'
      loc from to ts val val' released released'
      (UP_MEM : up_memory memory memory')
      (MSG_DISJ : message_disjoint memory)
      (TS_LT    : ts_lt_or_bot memory)
      (INHAB'   : Memory.inhabited memory')
      (SP' : Memory.split
               memory' loc from to ts val val' released released' memory_split')
      (GET : Memory.get loc ts memory = Some (from, Message.mk val' released')):
  exists memory_split,
    ⟪ SP : Memory.split memory loc from to ts val val' released released' memory_split ⟫ /\
    ⟪ UP_SP : up_memory memory_split memory_split' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_split ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_split ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_split' ⟫.
Proof.
  eapply up_memory_split_exists; eauto.
  2: reflexivity.
  inv SP'. inv SPLIT.
Qed.

Lemma up_memory_lower_exists memory memory' memory_lower'
      loc from to val view released released'
      (UP_MEM : up_memory memory memory')
      (MSG_DISJ : message_disjoint memory)
      (TS_LT    : ts_lt_or_bot memory)
      (INHAB'   : Memory.inhabited memory')
      (VWF : View.opt_wf released)
      (VLE : View.opt_le released released')
      (LW' : Memory.lower
               memory' loc from to val view released' memory_lower')
      (GET : Memory.get loc to memory = Some (from, Message.mk val view)):
  exists memory_lower,
    ⟪ LW : Memory.lower memory loc from to val view released memory_lower ⟫ /\
    ⟪ UP_LW : up_memory memory_lower memory_lower' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_lower ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_lower ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_lower' ⟫.
Proof.
  inv LW'. inv LOWER.
  edestruct Memory.lower_exists with (mem1:=memory) (released1:=view) (released2:=released)
    as [memory_lower]; eauto.
  { etransitivity; eauto. }
  exists memory_lower. splits; eauto.
  constructor; ins.
  { erewrite Memory.lower_o in INT; eauto.
    erewrite Memory.lower_o; eauto.
    desf; simpls; desc; subst.
    2: by apply UP_MEM.
    eexists; eexists. splits; eauto; reflexivity. }
  { erewrite Memory.lower_o in INT; eauto.
    desf; simpls; desc; subst.
    { repeat eexists; simpls; eauto.
      2,3: by apply IMU.
      erewrite Memory.lower_o; eauto.
      rewrite loc_ts_eq_dec_eq; simpls. }
    eapply (TOUIN UP_MEM) in INT; eauto. desc.
    destruct (loc_ts_eq_dec (loc0, t) (loc, to)); simpls.
    { clear o. desf. repeat eexists.
      2,3: by apply IMP.
      erewrite Memory.lower_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }
    repeat eexists.
    2,3: by apply IMP.
    erewrite Memory.lower_o; eauto.
    rewrite loc_ts_eq_dec_neq; eauto. }
  4: by eapply Memory.lower_inhabited; eauto.
  3: by eapply ts_lt_or_bot_lower; eauto.
  2: by eapply message_disjoint_lower; eauto.
  ins.
  erewrite Memory.lower_o in INT; eauto.
  desf; simpls; desc; subst.
  { repeat eexists; simpls.
    2,3: reflexivity.
    erewrite Memory.lower_o; eauto.
    rewrite loc_ts_eq_dec_eq; eauto. }
  apply UP_MEM in INT. desc.
  destruct (loc_ts_eq_dec (loc0, t') (loc, to)); simpls.
  { desf. repeat eexists.
    2,3: by apply ILE.
    erewrite Memory.lower_o; eauto.
    rewrite loc_ts_eq_dec_eq; eauto.
    inv LW'. inv LOWER0. unfold Memory.get, Cell.get in INT0.
    rewrite INT0 in GET0. inv GET0. }
  repeat eexists.
  2,3: by apply ILE.
  erewrite Memory.lower_o; eauto.
  rewrite loc_ts_eq_dec_neq; eauto.
Qed.

Lemma up_memory_lower_exists_view_eq memory memory' memory_lower'
      loc from to val released released'
      (UP_MEM : up_memory memory memory')
      (MSG_DISJ : message_disjoint memory)
      (TS_LT    : ts_lt_or_bot memory)
      (INHAB'   : Memory.inhabited memory')
      (LW' : Memory.lower
               memory' loc from to val released released' memory_lower')
      (GET : Memory.get loc to memory = Some (from, Message.mk val released)):
  exists memory_lower,
    ⟪ LW : Memory.lower memory loc from to val released released' memory_lower ⟫ /\
    ⟪ UP_LW : up_memory memory_lower memory_lower' ⟫ /\
    ⟪ MSG_DISJ : message_disjoint memory_lower ⟫ /\
    ⟪ TS_LT    : ts_lt_or_bot memory_lower ⟫ /\
    ⟪ INHAB'   : Memory.inhabited memory_lower' ⟫.
Proof.
  eapply up_memory_lower_exists; eauto.
  2: reflexivity.
  inv LW'. inv LOWER.
Qed.

Record future_sim_rel lang (tc tc' : Thread.t lang) :=
  { ST     : tc.(Thread.state) = tc'.(Thread.state);
    PROM   : tc.(Thread.local).(Local.promises) = tc'.(Thread.local).(Local.promises);
    TVIEW  : TView.le_ tc.(Thread.local).(Local.tview) tc'.(Thread.local).(Local.tview);
    SC_LE  : TimeMap.le tc.(Thread.sc) tc'.(Thread.sc);
    UP_MEM : up_memory tc.(Thread.memory) tc'.(Thread.memory);
    MSG_DISJ : message_disjoint tc.(Thread.memory);
    TS_LT    : ts_lt_or_bot tc.(Thread.memory);
    REL_WF   : message_view_wf tc.(Thread.memory);
    INHAB'   : Memory.inhabited tc'.(Thread.memory);
  }.

Lemma future_sim_step lang (tc tc' tc_new' : Thread.t lang)
      (WF  : Local.wf tc .(Thread.local) tc .(Thread.memory))
      (WF' : Local.wf tc'.(Thread.local) tc'.(Thread.memory))
      (STEP : Thread.tau_step (lang:=lang) tc' tc_new')
      (SIM : future_sim_rel tc tc') :
  exists tc_new,
      ⟪ STEP : (Thread.tau_step (lang:=lang))⁺ tc tc_new ⟫ /\
      ⟪ SIM : future_sim_rel tc_new tc_new' ⟫.
Proof.
  destruct SIM.
  destruct STEP. destruct TSTEP.
  destruct STEP.
  { destruct STEP.
    destruct lc1. destruct lc2.
    destruct tc  as [st_ [] sc_ mem_].
    simpls; subst. 
    destruct LOCAL. simpls.
    assert (exists mem_2,
               ⟪ MM1 : Memory.promise promises mem_ loc from to val released
                              promises2 mem_2 kind ⟫ /\
               ⟪ MM2 : Memory.closed_opt_view released mem_2 ⟫ /\
               ⟪ MM3 : Time.le (View.rlx (View.unwrap released) loc) to ⟫ /\
               ⟪ MMU : up_memory mem_2 mem2 ⟫ /\
               ⟪ MMD : message_disjoint mem_2 ⟫ /\
               ⟪ MMT : ts_lt_or_bot mem_2 ⟫ /\
               ⟪ MMI : Memory.inhabited mem2 ⟫
           ) as [mem_2].
    { destruct PROMISE.
      { edestruct up_memory_add_exists_l_view_eq with (memory:=mem_) as [mem_2]; eauto.
        desc. exists mem_2. splits; auto.
        { by apply Memory.promise_add. }
        eapply up_memory_closed_opt_view; eauto. }
      { edestruct up_memory_split_exists_view_eq with
            (memory:=mem_) (memory':=mem1) as [mem_2]; eauto.
        { inv PROMISES. inv SPLIT. by apply WF in GET2. }
        desc.
        exists mem_2. splits; auto.
        { by apply Memory.promise_split. }
        eapply up_memory_closed_opt_view; eauto. }
      edestruct up_memory_lower_exists_view_eq with (memory:=mem_) (memory':=mem1) as [mem_2];
          eauto.
      { inv PROMISES. inv LOWER. by apply WF in GET2. }
      desc.
      exists mem_2. splits; auto.
      { by apply Memory.promise_lower. }
      eapply up_memory_closed_opt_view; eauto. }
    desc.
    eexists. splits.
    { apply t_step. econstructor.
      { econstructor. eapply Thread.step_promise.
        repeat (econstructor; eauto). }
      done. }
    constructor; simpls.
    eapply message_view_wf_promise; eauto. }
  destruct STEP. simpls.
  destruct lc1. destruct lc2.
  destruct tc  as [st_ [] sc_ mem_].
  simpls; subst. 
  inv LOCAL.
  { eexists. splits.
    { apply t_step. econstructor.
      { econstructor. eapply Thread.step_program.
        econstructor; eauto.
        econstructor. }
      done. }
    constructor; simpls. }
  { destruct LOCAL0. simpls.
    apply (TOU UP_MEM0) in GET. desc.
    eexists. splits.
    { apply t_step. econstructor.
      { econstructor. eapply Thread.step_program.
        econstructor.
        2: { eapply Local.step_read.
             econstructor; eauto.
             eapply TViewFacts.readable_mon; eauto.
             2: reflexivity.
             apply TVIEW0. }
        eauto. }
      done. }
    constructor; simpls. subst.
    unfold TView.read_tview.
    constructor; simpls.
    { by apply TVIEW0. }
    all: apply view_le_rect; [|desf; [by apply View.unwrap_opt_le|reflexivity]].
    all: apply view_le_rect; [|reflexivity].
    all: apply TVIEW0. }
  { destruct LOCAL0. simpls.
    destruct WRITE.
    set (released_ := TView.write_released tview1 sc_ loc to None ord).
    assert (View.opt_le released_ released) as RLE.
    { subst. unfold released_, TView.write_released.
      desf; [|reflexivity].
      apply View.opt_le_some.
      apply view_le_rect; [reflexivity|].
      unfold TView.write_tview. simpls.
      unfold LocFun.add. desf.
      all: apply view_le_rect; [|reflexivity].
      all: apply TVIEW0. }
    assert (View.opt_wf released_) as VWF.
    { unfold released_, TView.write_released.
      desf; constructor.
      rewrite View.join_bot_l.
      unfold TView.write_tview; simpls.
      unfold LocFun.add. rewrite Loc.eq_dec_eq.
      unfold View.join. constructor; desf; simpls.
      all: apply timemap_le_rect; [|reflexivity].
      all: apply WF. }
    assert (TView.le_ (TView.write_tview tview1 sc_ loc to ord)
                      (TView.write_tview tview sc1 loc to ord)) as WV.
    { unfold TView.write_tview. constructor; simpls.
      ins. unfold LocFun.find, LocFun.add.
      desf.
      all: try (apply view_le_rect; [apply TVIEW0|reflexivity]).
      apply TVIEW0. }
    destruct PROMISE.
    { (* add case *)
      edestruct up_memory_add_exists_l with (memory:=mem_) (released:=released_)
        as [mem_']; eauto.
      desc.
      assert (exists (promise_ : Memory.t),
                 Memory.add promises loc from to val released_ promise_)
        as [promise_ PP].
      { eapply Memory.add_exists_le.
        { apply WF. }
        apply ADDU. }
      assert (exists (promise_' : Memory.t),
                 Memory.remove promise_ loc from to val released_ promise_')
        as [promise_' RR].
      { apply Memory.remove_exists.
        erewrite Memory.add_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      eexists. splits.
      { apply t_step.
        econstructor.
        { econstructor. eapply Thread.step_program.
          econstructor.
          2: { eapply Local.step_write.
               econstructor.
               { done. }
               { constructor. eapply TimeFacts.le_lt_lt.
                 2: by apply WRITABLE.
                 apply TVIEW0. }
               2: by eauto.
               econstructor; eauto.
               apply Memory.promise_add; eauto.
               etransitivity; eauto.
               subst.
               unfold TView.write_released.
               desf; simpls.
               2: by apply Time.bot_spec.
               repeat (rewrite TimeMap.le_join_r; [|by apply TimeMap.bot_spec]).
               unfold LocFun.add. rewrite !Loc.eq_dec_eq.
               desf; unfold View.join; simpls.
               all: apply timemap_le_rect; [apply TVIEW0|reflexivity]. }
          eauto. }
        done. }
      constructor; simpls.
      all: try by apply UP_EXTRA.
      apply Memory.ext.
      ins.
      erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
      desf.
      erewrite Memory.add_o; eauto.
      erewrite Memory.add_o with (mem2:=promises1); [|by apply PROMISES].
      desf; simpls; desf.
      eapply message_view_wf_add; eauto. }
    { (* split case *)
      edestruct up_memory_split_exists with (memory:=mem_) (released:=released_) as [mem_'];
        eauto.
      { inv PROMISES. inv SPLIT. by apply WF in GET2. }
      desc.
      assert (exists (promise_ : Memory.t),
                 Memory.split promises loc from to ts3 val val3 released_ released3 promise_)
        as [promise_ PP].
      { inv PROMISES. inv SPLIT.
        apply Memory.split_exists; auto. }
      assert (exists (promise_' : Memory.t),
                 Memory.remove promise_ loc from to val released_ promise_')
        as [promise_' RR].
      { apply Memory.remove_exists.
        erewrite Memory.split_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      eexists. splits.
      { apply t_step.
        econstructor.
        { econstructor. eapply Thread.step_program.
          econstructor.
          2: { eapply Local.step_write.
               econstructor.
               { done. }
               { constructor. eapply TimeFacts.le_lt_lt.
                 2: by apply WRITABLE.
                 apply TVIEW0. }
               2: by eauto.
               econstructor; eauto.
               apply Memory.promise_split; eauto.
               etransitivity; eauto.
               subst.
               unfold TView.write_released.
               desf; simpls.
               2: by apply Time.bot_spec.
               repeat (rewrite TimeMap.le_join_r; [|by apply TimeMap.bot_spec]).
               unfold LocFun.add. rewrite !Loc.eq_dec_eq.
               desf; unfold View.join; simpls.
               all: apply timemap_le_rect; [apply TVIEW0|reflexivity]. }
          eauto. }
        done. }
      constructor; simpls.
      apply Memory.ext.
      ins.
      erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
      desf.
      erewrite Memory.split_o; eauto.
      erewrite Memory.split_o with (mem2:=promises1); [|by apply PROMISES].
      desf; simpls; desf.
      eapply message_view_wf_split; eauto. }
    (* lower case *)
    edestruct up_memory_lower_exists with (memory:=mem_) (released:=released_) as [mem_'];
      eauto.
    { inv PROMISES. inv LOWER. by apply WF in GET2. }
    assert (exists (promise_ : Memory.t),
               Memory.lower promises loc from to val released0 released_ promise_)
      as [promise_ PP].
    { inv PROMISES. inv LOWER.
      apply Memory.lower_exists; auto.
      etransitivity; eauto. }
    assert (exists (promise_' : Memory.t),
               Memory.remove promise_ loc from to val released_ promise_')
      as [promise_' RR].
    { apply Memory.remove_exists.
      erewrite Memory.lower_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }
    desc.
    eexists. splits.
    { apply t_step.
      econstructor.
      { econstructor. eapply Thread.step_program.
        econstructor.
        2: { eapply Local.step_write.
             econstructor.
             { done. }
             { constructor. eapply TimeFacts.le_lt_lt.
               2: by apply WRITABLE.
               apply TVIEW0. }
             2: by eauto.
             econstructor; eauto.
             apply Memory.promise_lower; eauto.
             etransitivity; eauto.
             subst.
             unfold TView.write_released.
             desf; simpls.
             2: by apply Time.bot_spec.
             repeat (rewrite TimeMap.le_join_r; [|by apply TimeMap.bot_spec]).
             unfold LocFun.add. rewrite !Loc.eq_dec_eq.
             desf; unfold View.join; simpls.
             all: apply timemap_le_rect; [apply TVIEW0|reflexivity]. }
        eauto. }
      done. }
    constructor; simpls.
    apply Memory.ext.
    ins.
    erewrite Memory.remove_o; eauto.
    erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
    desf.
    erewrite Memory.lower_o; eauto.
    erewrite Memory.lower_o with (mem2:=promises1); [|by apply PROMISES].
    desf; simpls; desf.
    eapply message_view_wf_lower; eauto. }
  { (* RMW cover case *)
    destruct LOCAL1. simpls.
    destruct LOCAL2. simpls.
    destruct WRITE.
    set (GET' := GET).
    apply (TOU UP_MEM0) in GET'. desc.
    set (tview_ := TView.read_tview tview1 loc tsr view ordr).
    set (released_ := TView.write_released tview_ sc_ loc tsw view ordw).
    assert (View.le (View.unwrap view) (View.unwrap releasedr)) as XX.
    { by apply View.unwrap_opt_le. }
    assert (View.opt_le released_ releasedw) as RLE.
    { subst. unfold released_, TView.write_released.
      desf; [|reflexivity].
      apply View.opt_le_some.
      apply view_le_rect; auto.
      unfold TView.write_tview. simpls.
      unfold LocFun.add. desf.
      all: repeat (apply view_le_rect); auto.
      all: try reflexivity.
      all: by apply TVIEW0. }
    assert (View.wf (View.unwrap view)) as VVWF.
    { apply REL_WF0 in INF. inv INF. apply View.bot_wf. }
    assert (View.opt_wf released_) as VWF.
    { unfold released_, TView.write_released.
      desf; constructor.
      apply View.join_wf; auto.
      unfold TView.write_tview; simpls.
      unfold LocFun.add. rewrite Loc.eq_dec_eq.
      unfold View.join. constructor; desf; simpls.
      all: repeat (apply timemap_le_rect).
      all: try by apply WF.
      all: try reflexivity.
      2: by apply VVWF.
      all: unfold View.singleton_ur_if, View.singleton_ur, View.singleton_rw.
      all: desf; simpls.
      all: try reflexivity.
      all: apply TimeMap.bot_spec. }
    assert (TimeMap.le (View.rlx (View.unwrap view)) (View.rlx (View.unwrap releasedr)))
      as VLE.
    { by apply View.unwrap_opt_le. }
    assert (TimeMap.le
              (View.rlx (TView.cur tview_))
              (View.rlx (TView.cur tview2))) as TLE.
    { intros ll.
      rewrite <- TVIEW1. unfold TView.read_tview. simpls.
      repeat apply timemap_le_rect.
      { apply TVIEW0. }
      { reflexivity. }
      desf.
      reflexivity. }
    assert (TView.le_ (TView.write_tview tview_ sc_ loc tsw ordw)
                      (TView.write_tview tview2 sc1 loc tsw ordw)) as WV.
    { rewrite <- TVIEW1.
      unfold TView.write_tview. constructor; simpls.
      all: ins; unfold LocFun.find, LocFun.add.
      all: desf.
      all: repeat apply view_le_rect; auto.
      all: try reflexivity.
      all: apply TVIEW0. }
    destruct PROMISE.
    { (* add case *)
      edestruct up_memory_add_exists_l with (memory:=mem_) (released:=released_)
        as [mem_']; eauto.
      desc.
      assert (exists (promise_ : Memory.t),
                 Memory.add promises loc tsr tsw valw released_ promise_)
        as [promise_ PP].
      { eapply Memory.add_exists_le.
        { apply WF. }
        apply ADDU. }
      assert (exists (promise_' : Memory.t),
                 Memory.remove promise_ loc tsr tsw valw released_ promise_')
        as [promise_' RR].
      { apply Memory.remove_exists.
        erewrite Memory.add_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      eexists. splits.
      { apply t_step.
        econstructor.
        { econstructor. eapply Thread.step_program.
          econstructor.
          2: { eapply Local.step_update.
               { econstructor; eauto.
                 eapply TViewFacts.readable_mon; eauto.
                 2: reflexivity.
                 apply TVIEW0. }
               econstructor.
               { done. }
               { constructor. eapply TimeFacts.le_lt_lt; auto.
                   by apply WRITABLE. }
               2: by eauto.
               econstructor; eauto.
               apply Memory.promise_add; eauto.
               etransitivity; eauto.
               subst.
               unfold TView.write_released.
               desf; simpls.
               2: by apply Time.bot_spec.
               apply timemap_le_rect; auto.
               unfold LocFun.add. rewrite !Loc.eq_dec_eq.
               desf; unfold View.join; simpls.
               all: repeat apply timemap_le_rect; auto.
               all: try reflexivity.
               all: apply TVIEW0. }
          eauto. }
        done. }
      constructor; simpls.
      2: by eapply message_view_wf_add; eauto.
      apply Memory.ext.
      ins.
      erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
      desf.
      all: erewrite Memory.add_o; eauto.
      all: erewrite Memory.add_o with (mem2:=promises1); [|by apply PROMISES].
      all: desf; simpls; desf. }
    { (* split case *)
      edestruct up_memory_split_exists with (memory:=mem_) (released:=released_) as [mem_'];
        eauto.
      { inv PROMISES. inv SPLIT. by apply WF in GET2. }
      desc.
      assert (exists (promise_ : Memory.t),
                 Memory.split promises loc tsr tsw ts3 valw val3 released_ released3 promise_)
        as [promise_ PP].
      { inv PROMISES. inv SPLIT.
        apply Memory.split_exists; auto. }
      assert (exists (promise_' : Memory.t),
                 Memory.remove promise_ loc tsr tsw valw released_ promise_')
        as [promise_' RR].
      { apply Memory.remove_exists.
        erewrite Memory.split_o; eauto.
          by rewrite loc_ts_eq_dec_eq. }
      eexists. splits.
      { apply t_step.
        econstructor.
        { econstructor. eapply Thread.step_program.
          econstructor.
          2: { eapply Local.step_update.
               { econstructor; eauto.
                 eapply TViewFacts.readable_mon; eauto.
                 2: reflexivity.
                 apply TVIEW0. }
               econstructor.
               { done. }
               { constructor. eapply TimeFacts.le_lt_lt; auto.
                   by apply WRITABLE. }
               2: by eauto.
               econstructor; eauto.
               apply Memory.promise_split; eauto.
               etransitivity; eauto.
               subst.
               unfold TView.write_released.
               desf; simpls.
               2: by apply Time.bot_spec.
               apply timemap_le_rect; auto.
               unfold LocFun.add. rewrite !Loc.eq_dec_eq.
               desf; unfold View.join; simpls.
               all: repeat apply timemap_le_rect; auto.
               all: try reflexivity.
               all: apply TVIEW0. }
          eauto. }
        done. }
      constructor; simpls.
      apply Memory.ext.
      ins.
      erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
      desf.
      3: { eapply message_view_wf_split; eauto. }
      all: erewrite Memory.split_o; eauto.
      all: erewrite Memory.split_o with (mem2:=promises1); [|by apply PROMISES].
      all: desf; simpls; desf. }
    (* lower case *)
    edestruct up_memory_lower_exists with (memory:=mem_) (released:=released_) as [mem_'];
      eauto.
    { inv PROMISES. inv LOWER. by apply WF in GET2. }
    assert (exists (promise_ : Memory.t),
               Memory.lower promises loc tsr tsw valw released0 released_ promise_)
      as [promise_ PP].
    { inv PROMISES. inv LOWER.
      apply Memory.lower_exists; auto.
      etransitivity; eauto. }
    assert (exists (promise_' : Memory.t),
               Memory.remove promise_ loc tsr tsw valw released_ promise_')
      as [promise_' RR].
    { apply Memory.remove_exists.
      erewrite Memory.lower_o; eauto.
        by rewrite loc_ts_eq_dec_eq. }
    desc.
    eexists. splits.
    { apply t_step.
        econstructor.
        { econstructor. eapply Thread.step_program.
          econstructor.
          2: { eapply Local.step_update.
               { econstructor; eauto.
                 eapply TViewFacts.readable_mon; eauto.
                 2: reflexivity.
                 apply TVIEW0. }
               econstructor.
               { done. }
               { constructor. eapply TimeFacts.le_lt_lt; auto.
                   by apply WRITABLE. }
               2: by eauto.
               econstructor; eauto.
               apply Memory.promise_lower; eauto.
               etransitivity; eauto.
               subst.
               unfold TView.write_released.
               desf; simpls.
               2: by apply Time.bot_spec.
               apply timemap_le_rect; auto.
               unfold LocFun.add. rewrite !Loc.eq_dec_eq.
               desf; unfold View.join; simpls.
               all: repeat apply timemap_le_rect; auto.
               all: try reflexivity.
               all: apply TVIEW0. }
          eauto. }
        done. }
    constructor; simpls.
    apply Memory.ext.
    ins.
    erewrite Memory.remove_o; eauto.
    erewrite Memory.remove_o with (mem2:=promises2); [|by apply REMOVE].
    desf.
    3: { eapply message_view_wf_lower; eauto. }
    all: erewrite Memory.lower_o; eauto.
    all: erewrite Memory.lower_o with (mem2:=promises1); [|by apply PROMISES].
    all: desf; simpls; desf. }
  destruct LOCAL0. simpls.
  eexists. splits.
  { apply t_step. econstructor.
    { econstructor. eapply Thread.step_program.
      econstructor.
      2: { eapply Local.step_fence.
           econstructor; eauto. }
      eauto. }
    done. }
  constructor; simpls; subst.
  { unfold TView.write_fence_tview.
    constructor; simpls.
    { ins. unfold LocFun.find.
      desf.
      2-4: by apply TVIEW0.
      constructor; simpls.
      all: unfold TView.write_fence_sc, TView.read_fence_tview; desf; simpls.
      all: apply timemap_le_rect; auto.
      all: apply TVIEW0. }
    { desf.
      2-3: by apply TVIEW0.
      constructor; simpls.
      all: unfold TView.write_fence_sc, TView.read_fence_tview; desf; simpls.
      all: apply timemap_le_rect; auto.
      all: apply TVIEW0. }
    desf.
    2: by rewrite !view_join_bot_r; apply TVIEW0.
    constructor; simpls.
    all: unfold TView.write_fence_sc, TView.read_fence_tview; desf; simpls.
    all: repeat (apply timemap_le_rect); auto.
    all: apply TVIEW0. }
  unfold TView.write_fence_sc, TView.read_fence_tview; desf; simpls.
  all: repeat (apply timemap_le_rect); auto.
  all: apply TVIEW0.
Qed.

Lemma future_memory_switch
      lang (state : Language.Language.state lang)
      local sc_view memory sc_view' memory'
      (FUTURE_INIT : Memory.future Memory.init memory)
      (FUTURE      : Memory.future memory memory')
      (SC_LE       : TimeMap.le sc_view sc_view')
      (PROMISES    : Memory.le (Local.promises local) memory')
      (LOCAL_WF    : Local.wf local memory)
      (SC_CLOS     : Memory.closed_timemap sc_view' memory') :
  exists sc_view'' memory'',
    ⟪ MEM_LE : Memory.le memory memory'' ⟫ /\
    ⟪ FUTURE : Memory.future Memory.init memory'' ⟫ /\
    ⟪ SC_LE  : TimeMap.le sc_view sc_view'' ⟫ /\
    ⟪ LOCAL_WF : Local.wf local memory'' ⟫ /\
    ⟪ SC_CLOS : Memory.closed_timemap sc_view'' memory'' ⟫ /\
    ⟪ MEM_CLOS : Memory.closed memory' ⟫ /\
    ⟪ STEPS :
      forall (thread_conf : Thread.t lang)
             (EXEC : rtc (Thread.tau_step (lang:=lang))
                         (Thread.mk lang state local sc_view'' memory'')
                         thread_conf),
      exists (thread_conf' : Thread.t lang),
        ⟪ STEPS :
          rtc (Thread.tau_step (lang:=lang))
              (Thread.mk lang state local sc_view' memory')
              thread_conf' ⟫ /\
        ⟪ SIM : future_sim_rel thread_conf' thread_conf ⟫ ⟫.
Proof.
  assert (Memory.closed memory') as MEM_CLOS'.
  { eapply Memory.future_closed; eauto.
    eapply Memory.future_closed; eauto.
    apply Memory.init_closed. }
  edestruct future_memory_to_append_memory with (memory:=memory) (memory':=memory')
    as [memory'']; eauto.
  desc.
  edestruct up_memory_closed_bigger_timemap with (memory:=memory') (memory':=memory'')
    as [sc_view'']; eauto.
  { by etransitivity; [|by eauto]. }
  { by apply inhabited_future_init. }
  desc.
  exists sc_view''. exists memory''.
  assert (Local.wf local memory') as LOCAL_WF'.
  { constructor; auto.
    1,3: by apply LOCAL_WF.
    constructor; ins.
    all: eapply Memory.future_closed_view; eauto.
    all: apply LOCAL_WF. }
  assert (Local.wf local memory'') as LOCAL_WF''.
  { constructor.
    1,4: by apply LOCAL_WF.
    { constructor; ins.
      all: eapply closed_view_le; eauto.
      all: apply LOCAL_WF. }
    etransitivity; [apply LOCAL_WF|apply MEM_LE]. }
  splits; auto.
  { etransitivity; eauto. }
  ins.
  assert (future_sim_rel
            (Thread.mk _ state local sc_view'  memory' )
            (Thread.mk _ state local sc_view'' memory'')) as XX.
  { constructor; simpls.
    { reflexivity. }
    { apply message_disjoint_future_init.
        by etransitivity; [|by eauto]. }
    { apply ts_lt_or_bot_future_init.
        by etransitivity; [|by eauto]. }
    2: by apply inhabited_future_init.
    apply message_view_wf_future_init.
      by etransitivity; [|by eauto]. }
  clear -EXEC LOCAL_WF LOCAL_WF' LOCAL_WF'' MEM_CLOS' XX SC_CLOS TM_CLOS FUTURE0.
  apply clos_rt_rt1n_iff in EXEC.
  apply clos_rt_rtn1_iff in EXEC.
  induction EXEC.
  { eexists. splits.
    { reflexivity. }
    done. }
  desc.
  assert (Local.wf (Thread.local thread_conf') (Thread.memory thread_conf')) as AA.
  { eapply Thread.rtc_tau_step_future; eauto. }
  assert (Local.wf (Thread.local y) (Thread.memory y)) as BB.
  { apply clos_rt_rtn1_iff in EXEC.
    apply clos_rt_rt1n in EXEC.
    eapply Thread.rtc_tau_step_future; eauto.
    all: simpls.
    eapply Memory.future_closed; [|by eauto].
    apply Memory.init_closed. }
  eapply future_sim_step in H.
  { desc. eexists. splits.
    2: by eauto.
    apply clos_rt_rt1n_iff.
    eapply rt_trans.
    { apply clos_rt_rt1n_iff. eauto. }
    apply clos_trans_in_rt; eauto. }
  all: auto.
Qed.
