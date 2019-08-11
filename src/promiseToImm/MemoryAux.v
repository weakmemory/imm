From hahn Require Import Hahn.
From PromisingLib Require Import Basic DenseOrder.
From Promising Require Import Memory View Time Cell TView.

Definition memory_close tview memory :=
  ⟪ CLOSED_CUR :
    Memory.closed_timemap (View.rlx (TView.cur tview)) memory ⟫ /\
  ⟪ CLOSED_ACQ :
    Memory.closed_timemap (View.rlx (TView.acq tview)) memory ⟫ /\
  ⟪ CLOSED_REL :
    forall loc,
      Memory.closed_timemap (View.rlx (TView.rel tview loc)) memory ⟫.

Lemma loc_ts_eq_dec_eq {A} {a b : A} l ts :
  (if loc_ts_eq_dec (l, ts) (l, ts) then a else b) = a.
Proof. edestruct loc_ts_eq_dec; desf. Qed.

Lemma loc_ts_eq_dec_neq {A} {a b : A} {l ts l' ts'}
      (NEQ: l <> l' \/ ts <> ts'):
  (if loc_ts_eq_dec (l, ts) (l', ts') then a else b) = b.
Proof. edestruct loc_ts_eq_dec; desf. Qed.


Lemma memory_add_le memory memory' loc from to val released
      (ADD : Memory.add memory loc from to val released memory'):
  Memory.le memory memory'.
Proof.
  red. ins. erewrite Memory.add_o; eauto.
  destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); [simpls; desf|done].
  exfalso. erewrite Memory.add_get0 in LHS; eauto.
  desf.
Qed.

Lemma memory_remove_le memory memory' loc from to val released
      (ADD : Memory.remove memory loc from to val released memory'):
  Memory.le memory' memory.
Proof.
  red. ins. erewrite Memory.remove_o in LHS; eauto.
    by destruct (loc_ts_eq_dec (loc0, to0) (loc, to)) in LHS; [desf|].
Qed.

Set Implicit Arguments.
Remove Hints plus_n_O.

Lemma inhabited_init : Memory.inhabited Memory.init.
Proof. red. ins. Qed.

Lemma inhabited_future memory memory'
      (INHAB : Memory.inhabited memory)
      (FUTURE : Memory.future memory memory') :
  Memory.inhabited memory'.
Proof.
  destruct FUTURE; auto.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  { destruct H.
    eapply Memory.op_future0; eauto. }
  destruct H0.
  eapply Memory.op_future0; eauto.
Qed.

Lemma inhabited_future_init memory (FUTURE : Memory.future Memory.init memory) :
  Memory.inhabited memory.
Proof. eapply inhabited_future; eauto. apply inhabited_init. Qed.

Definition ts_lt_or_bot memory :=
  forall loc to from msg (GET : Memory.get loc to memory = Some (from, msg)),
    (to = Time.bot /\ from = Time.bot) \/
    ⟪ FTLT : Time.lt from to ⟫.

Lemma memory_init_o loc to from msg
      (GET : Memory.get loc to Memory.init = Some (from, msg)) :
  to = Time.bot /\ from = Time.bot /\ msg = Message.elt.
Proof.
  unfold Memory.init, Cell.init, Cell.Raw.init in *.
  unfold Memory.get, Cell.get in *; simpls.
  apply IdentMap.singleton_find_inv in GET.
  desf.
Qed.

Lemma ts_lt_or_bot_init : ts_lt_or_bot Memory.init.
Proof. red. ins. apply memory_init_o in GET. left. desf. Qed.

Definition message_disjoint memory :=
  forall loc to1 from1 msg1 to2 from2 msg2
         (GET1 : Memory.get loc to1 memory = Some (from1, msg1))
         (GET2 : Memory.get loc to2 memory = Some (from2, msg2)),
    to1 = to2 \/ Interval.disjoint (from1, to1) (from2, to2).

Lemma message_disjoint_init : message_disjoint Memory.init.
Proof.
  red. ins.
  apply memory_init_o in GET1.
  apply memory_init_o in GET2.
  desf. by left.
Qed.

Lemma ts_lt_or_bot_add loc from to val released memory memory_add
      (TLOB : ts_lt_or_bot memory)
      (ADD : Memory.add memory loc from to val released memory_add) :
  ts_lt_or_bot memory_add.
Proof.
  red. ins.
  erewrite Memory.add_o in GET; eauto.
  desf; simpls; desf.
  { right. inv ADD. inv ADD0. }
  all: by eapply TLOB; eauto.
Qed.

Lemma message_disjoint_add loc from to val released memory memory_add
      (MD : message_disjoint memory)
      (ADD : Memory.add memory loc from to val released memory_add) :
  message_disjoint memory_add.
Proof.
  red. ins.
  erewrite Memory.add_o in GET1; eauto.
  erewrite Memory.add_o in GET2; eauto.
  desf; simpls; desf.
  { by left. }
  { right. inv ADD. inv ADD0.
    symmetry.
    eapply DISJOINT; eauto. }
  { right. inv ADD. inv ADD0.
    eapply DISJOINT; eauto. }
  all: by eapply MD; eauto.
Qed.

Lemma ts_lt_or_bot_lower loc from to val released released' memory memory_lower
      (TLOB : ts_lt_or_bot memory)
      (LOWER : Memory.lower memory loc from to val released released' memory_lower) :
  ts_lt_or_bot memory_lower.
Proof.
  red. ins.
  erewrite Memory.lower_o in GET; eauto.
  desf; simpls; desf.
  { right. inv LOWER. inv LOWER0. }
  all: by eapply TLOB; eauto.
Qed.

Lemma message_disjoint_lower loc from to val released released' memory memory_lower
      (MD : message_disjoint memory)
      (LOWER : Memory.lower memory loc from to val released released' memory_lower) :
  message_disjoint memory_lower.
Proof.
  red. ins.
  erewrite Memory.lower_o in GET1; eauto.
  erewrite Memory.lower_o in GET2; eauto.
  desf; simpls; desf.
  { by left. }
  all: inv LOWER; inv LOWER0; eapply MD; eauto.
Qed.

Lemma ts_lt_or_bot_split loc from to to' val val' released released' memory memory_split
      (TLOB : ts_lt_or_bot memory)
      (SPLIT : Memory.split memory loc from to to' val val' released released' memory_split) :
  ts_lt_or_bot memory_split.
Proof.
  red. ins.
  erewrite Memory.split_o in GET; eauto.
  desf; simpls; desf.
  1,2: by right; inv SPLIT; inv SPLIT0.
  all: eapply TLOB; eauto.
Qed.

Lemma ts_lt_or_bot_op loc from to val released kind memory memory'
      (TLOB : ts_lt_or_bot memory)
      (OP : Memory.op memory loc from to val released memory' kind) :
  ts_lt_or_bot memory'.
Proof.
  destruct OP.
  { eapply ts_lt_or_bot_add; eauto. }
  { eapply ts_lt_or_bot_split; eauto. }
  eapply ts_lt_or_bot_lower; eauto.
Qed.

Lemma ts_lt_or_bot_future memory memory'
      (TLOB : ts_lt_or_bot memory)
      (FUTURE : Memory.future memory memory') :
  ts_lt_or_bot memory'.
Proof.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  destruct H.
  eapply ts_lt_or_bot_op; eauto.
Qed.

Lemma ts_lt_or_bot_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  ts_lt_or_bot memory.
Proof. eapply ts_lt_or_bot_future; eauto. apply ts_lt_or_bot_init. Qed.

Lemma message_disjoint_split loc from to to' val val' released released' memory memory_split
      (MD : message_disjoint memory)
      (SPLIT : Memory.split memory loc from to to' val val' released released' memory_split) :
  message_disjoint memory_split.
Proof.
  assert (exists msg, Memory.get loc to' memory = Some (from, msg))
    as [msg GETI].
  { inv SPLIT. inv SPLIT0. eexists. apply GET2. }
  assert (Time.lt from to /\ Time.lt to to') as [LTF LTT].
  { inv SPLIT. inv SPLIT0. }
  assert (Interval.le (from, to) (from, to')) as ILE1.
  { constructor; simpls. reflexivity. apply Time.le_lteq. by left. }
  assert (Interval.le (to, to') (from, to')) as ILE2.
  { constructor; simpls. 2: reflexivity. apply Time.le_lteq. by left. }
  red. ins.
  erewrite Memory.split_o in GET1; eauto.
  erewrite Memory.split_o in GET2; eauto.
  desf; simpls; desf.
  all: try by left.
  all: try by (eapply MD in GET1; eapply GET1 in GET2; desf).
  all: right.
  { symmetry. apply Interval.disjoint_imm. }
  { symmetry.
    eapply Interval.le_disjoint; eauto.
    eapply MD in GET1. eapply GET1 in GETI.
    symmetry.
    desf. }
  { apply Interval.disjoint_imm. }
  { symmetry.
    eapply Interval.le_disjoint; eauto.
    eapply MD in GET1. eapply GET1 in GETI.
    symmetry.
    desf. }
  all: eapply Interval.le_disjoint; eauto.
  all: eapply MD in GET2; eapply GET2 in GETI.
  all: symmetry.
  all: desf.
Qed.

Lemma message_disjoint_op loc from to val released memory memory' kind
      (MD : message_disjoint memory)
      (OP : Memory.op memory loc from to val released memory' kind) :
  message_disjoint memory'.
Proof.
  destruct OP.
  { eapply message_disjoint_add; eauto. }
  { eapply message_disjoint_split; eauto. }
  eapply message_disjoint_lower; eauto.
Qed.

Lemma message_disjoint_future memory memory'
      (TLOB : message_disjoint memory)
      (FUTURE : Memory.future memory memory') :
  message_disjoint memory'.
Proof.
  apply clos_rt1n_rt in FUTURE.
  apply clos_rt_rtn1 in FUTURE.
  induction FUTURE; auto.
  destruct H.
  eapply message_disjoint_op; eauto.
Qed.

Lemma message_disjoint_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  message_disjoint memory.
Proof. eapply message_disjoint_future; eauto. apply message_disjoint_init. Qed.

Lemma time_le_rect a b c d (AB : Time.le a b) (CD : Time.le c d) :
  Time.le (Time.join a c) (Time.join b d).
Proof.
  unfold Time.join.
  desf.
  { apply Time.le_lteq. left.
    eapply TimeFacts.le_lt_lt; eauto. }
  etransitivity; eauto.
Qed.

Lemma timemap_le_rect a b c d (AB : TimeMap.le a b) (CD : TimeMap.le c d) :
  TimeMap.le (TimeMap.join a c) (TimeMap.join b d).
Proof.
  unfold TimeMap.join. intros x.
  all: by apply time_le_rect.
Qed.

Lemma view_le_rect a b c d (AB : View.le a b) (CD : View.le c d) :
  View.le (View.join a c) (View.join b d).
Proof.
  unfold View.join in *.
  destruct AB. destruct CD.
  constructor; simpls; intros x.
  all: by apply timemap_le_rect.
Qed.

Lemma memory_split_get_old memory memory_split
      loc from to ts val val' released released'
      (SP : Memory.split memory loc from to ts val val' released released' memory_split) :
  Memory.get loc ts memory = Some (from, Message.mk val' released').
Proof. inv SP. inv SPLIT. Qed.

Lemma interval_le_not_disjoint la ra lb rb
      (LTA : Time.lt la ra)
      (LTB : Time.lt lb rb)
      (NEQ : ra <> rb)
      (ILE : Interval.le (la, ra) (lb, rb)) :
  ~ Interval.disjoint (la, ra) (lb, rb).
Proof.
  inv ILE. simpls.
  intros HH. eapply HH; constructor; simpls; eauto.
  { reflexivity. }
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma closed_view_le view memory memory'
      (LE : Memory.le memory memory')
      (CLOS : Memory.closed_view view memory) :
  Memory.closed_view view memory'.
Proof.
  destruct CLOS.
  constructor; red; [clear RLX; rename PLN into RLX|]; ins.
  all: specialize (RLX loc); desc.
  all: apply LE in RLX; eauto.
Qed.

(*********************************************)
(* TODO: explanation. Maybe a separate file. *)
(*********************************************)
Definition message_view_wf memory :=
  forall loc to from val released
         (GET : Memory.get loc to memory = 
                Some (from, Message.mk val released)),
    View.opt_wf released.

Lemma message_view_wf_add
      memory loc from to val released memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.add memory loc from to val released memory') :
  message_view_wf memory'.
Proof.
  red. ins.
  erewrite Memory.add_o in GET; eauto.
  desf.
  2: by eapply REL_WF; eauto.
  simpls; desf.
  inv PROM. inv ADD.
Qed.

Lemma message_view_wf_split
      memory loc from to to' val val' released released' memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.split memory loc from to to' val val' released released' memory') :
  message_view_wf memory'.
Proof.
  red. ins.
  erewrite Memory.split_o in GET; eauto.
  desf.
  3: by eapply REL_WF; eauto.
  all: simpls; desf.
  { inv PROM. inv SPLIT. }
  inv PROM. inv SPLIT.
  eapply REL_WF.
  apply GET2.
Qed.

Lemma message_view_wf_lower
      memory loc from to val released released' memory'
      (REL_WF : message_view_wf memory)
      (PROM : Memory.lower memory loc from to val released released' memory') :
  message_view_wf memory'.
Proof.
  red. ins.
  erewrite Memory.lower_o in GET; eauto.
  desf.
  2: by eapply REL_WF; eauto.
  simpls; desf.
  inv PROM. inv LOWER.
Qed.

Lemma message_view_wf_op
      memory loc from to val released memory' kind
      (REL_WF : message_view_wf memory)
      (PROM : Memory.op memory loc from to val released memory' kind) :
  message_view_wf memory'.
Proof.
  destruct PROM.
  { eapply message_view_wf_add; eauto. }
  { eapply message_view_wf_split; eauto. }
  eapply message_view_wf_lower; eauto.
Qed.

Lemma message_view_wf_promise
      promises memory loc from to val released promises' memory' kind
      (REL_WF : message_view_wf memory)
      (PROM : Memory.promise promises memory loc from to
                             val released promises' memory' kind) :
  message_view_wf memory'.
Proof.
  destruct PROM.
  { eapply message_view_wf_add; eauto. }
  { eapply message_view_wf_split; eauto. }
  eapply message_view_wf_lower; eauto.
Qed.

Lemma message_view_wf_init : message_view_wf Memory.init.
Proof.
  red. ins. apply memory_init_o in GET. desf.
  unfold Message.elt in *. desf.
  apply View.opt_wf_none.
Qed.

Lemma message_view_wf_future memory memory'
      (MVW    : message_view_wf memory)
      (FUTURE : Memory.future memory memory') :
  message_view_wf memory'.
Proof.
  induction FUTURE; auto.
  apply IHFUTURE.
  destruct H.
  eapply message_view_wf_op; eauto.
Qed.

Lemma message_view_wf_future_init memory
      (FUTURE : Memory.future Memory.init memory) :
  message_view_wf memory.
Proof.
  eapply message_view_wf_future; eauto.
  apply message_view_wf_init.
Qed.

Lemma memory_closed_timemap_le view memory memory'
      (MEM_LE : Memory.le memory memory')
      (MEM_CLOS : Memory.closed_timemap view memory) :
  Memory.closed_timemap view memory'.
Proof.
  red; ins. specialize (MEM_CLOS loc). desf.
  apply MEM_LE in MEM_CLOS.
  eauto.
Qed.

Lemma memory_close_le tview memory memory'
      (MEM_LE : Memory.le memory memory')
      (MEM_CLOS : memory_close tview memory) :
  memory_close tview memory'.
Proof.
  cdes MEM_CLOS.
  red; splits; ins.
  all: eapply memory_closed_timemap_le; eauto.
Qed.


(*********************************************)
(* TODO: explanation. Maybe a separate file. *)
(*********************************************)
Lemma opt_wf_unwrap (view : option View.t) (H: View.wf (View.unwrap view)) :
  View.opt_wf view.
Proof. by destruct view; simpls; constructor. Qed.

Lemma view_join_bot_r (lhs : View.t): View.join lhs View.bot = lhs.
Proof. rewrite View.join_comm. apply View.join_bot_l. Qed.

Lemma view_join_id l : View.join l l = l.
Proof. rewrite View.le_join_l; reflexivity. Qed.

Lemma time_join_le_r lhs rhs (LE : Time.le lhs rhs): Time.join lhs rhs = rhs.
Proof.
  unfold Time.join. desf.
  exfalso. eapply DenseOrder.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma time_join_le_l lhs rhs (LE : Time.le rhs lhs): Time.join lhs rhs = lhs.
Proof. unfold Time.join. desf. by apply TimeFacts.antisym. Qed.

Lemma time_join_bot_r lhs: Time.join lhs Time.bot = lhs.
Proof. apply time_join_le_l. apply Time.bot_spec. Qed.

Lemma time_join_bot_l rhs: Time.join Time.bot rhs = rhs.
Proof. apply time_join_le_r. apply Time.bot_spec. Qed.

Lemma time_lt_join_l lhs rlhs rrhs (LT : Time.lt lhs rlhs) :
  Time.lt lhs (Time.join rlhs rrhs).
Proof. unfold Time.join. desf. eapply TimeFacts.lt_le_lt; eauto. Qed.

Lemma time_lt_join_r lhs rlhs rrhs (LT : Time.lt lhs rrhs) :
  Time.lt lhs (Time.join rlhs rrhs).
Proof. unfold Time.join. desf. etransitivity; eauto. Qed.
