From hahn Require Import Hahn.
From promising Require Import View Time Event.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section MaxValue.
  Variable A : Type.
  
  Definition max_value f (INR : A -> Prop) val :=
    ⟪ UB: forall a (INa: INR a), Time.le (f a) val ⟫ /\
    ⟪ MAX: ((forall a, ~ INR a) /\ val = Time.bot) \/
       (exists a_max, ⟪ INam: INR a_max ⟫ /\
                      ⟪LB': Time.le val (f a_max)⟫) ⟫.

  Lemma max_value_singleton f b t (T: t = f b) : max_value f (eq b) t.
  Proof.
    red; splits; ins; desc; subst.
      by apply Time.le_lteq; eauto.
      right; exists b; splits; try apply Time.le_lteq; eauto.
  Qed.

  Lemma max_value_new_f f f' P t 
        (MAX: max_value f P t) (F: forall x, P x -> f' x = f x): max_value f' P t.
  Proof.
    unfold max_value in *; ins; desf; splits; ins.
    all: try rewrite F; auto.
    right; exists a_max; rewrite F; auto.
  Qed.

  Lemma max_value_same_set f P P' t 
        (MAX: max_value f P t) (SAME: P' ≡₁ P): max_value f P' t.
  Proof.
    unfolder in *; desc.
    unfold max_value in *; ins; desf; splits; ins.
    all: try specialize (SAME a); desf; eauto.
    left; split; eauto; ins; intro;  eapply MAX0; apply SAME; edone.
  Qed.

  Lemma max_value_join f P P' P'' t t'
        (MAX: max_value f P t) (MAX':  max_value f P' t')
        (SAME_: P'' ≡₁ P ∪₁ P'):
    max_value f P'' (Time.join t t').
  Proof.
    assert (SAME: forall x, P'' x <-> P x \/ P' x).
      by unfolder in *; basic_solver 12.
    unfold max_value in *; ins; desf; splits; ins.
    all: try apply SAME in INa; desf.
    all: try apply SAME0 in INa; desf.
    all: try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
    - left; split; eauto. ins; intro. 
      specialize (MAX1 a). specialize (MAX0 a).
      apply SAME in H; desf.
    - right; exists a_max; splits.
      rewrite SAME; eauto.
      apply Time.join_spec; eauto; etransitivity; eauto; rewrite Time.le_lteq; eauto.
      apply Time.le_lteq. apply Time.bot_spec.
    - right; exists a_max; splits.
      apply SAME; eauto.
      apply Time.join_spec; eauto; etransitivity; eauto; rewrite Time.le_lteq; eauto.
      apply Time.le_lteq. apply Time.bot_spec.
    - right;
        destruct (Time.le_lt_dec (f a_max) (f a_max0)); [exists a_max0|exists a_max]; splits.
      all: try rewrite SAME; eauto.
      all: try (apply Time.join_spec; eauto;
                etransitivity; eauto; rewrite Time.le_lteq; eauto). 
  Qed.

  Lemma max_value_loc f f' P P' t b
        (MAX: max_value f P t)
        (SAME_: P' ≡₁ P ∪₁ eq b)
        (F: forall x, P x -> f' x = f x):
    max_value f' P'  (Time.join t (f' b)).
  Proof.
    assert (SAME: forall x, P' x <-> P x \/ eq b x).
      by unfolder in *; basic_solver 12.
    eapply max_value_join with (P':= eq b); eauto.
    eapply max_value_new_f with (f:=f); eauto.
    eapply max_value_singleton; done.
  Qed.

  Lemma max_value_empty f P (SAME: forall x, ~ P x): max_value f P Time.bot.
  Proof.
    red; splits.
    ins; exfalso; eapply SAME; edone.
    left; splits; eauto.
  Qed.

  Lemma max_value_le f b c tm l P
        (LE: Time.le (tm l) (f b))
        (MAX: max_value f P (LocFun.find l tm))
        (LT: Time.lt (f b) (f c))
        (IN: P c) : False.
  Proof.
    unfold LocFun.find in *.
    red in MAX; desf.
    eby eapply MAX0.
    apply UB in IN.
    eapply Time.lt_strorder; eauto using TimeFacts.le_lt_lt.
  Qed.

  Lemma max_value_lt f b tm l P t
        (LT1: Time.lt t (f b))
        (MAX: max_value f P (LocFun.find l tm))
        (LT2: Time.lt (tm l) t)
        (IN: P b) : False.
  Proof.
    unfold LocFun.find in *.
    red in MAX; desf.
    eby eapply MAX0.
    apply UB in IN.
    assert (Time.lt (tm l) (f b)).
    eapply Time.lt_strorder; eauto.
    eapply Time.lt_strorder; eauto using TimeFacts.le_lt_lt.
  Qed.
  
Lemma time_lt_bot a : ~ Time.lt a Time.bot.
Proof.
  intros H.
  destruct (classic (a = Time.bot)) as [|NEQ]; subst.
  all: eapply Time.lt_strorder; etransitivity; eauto.
  assert (Time.le Time.bot a) as HH by apply Time.bot_spec.
  apply Time.le_lteq in HH; destruct HH as [HH|HH]; desf.
Qed.

Lemma max_value_le_join f (P P' : A -> Prop) t
      (LT: forall x, P' x -> Time.lt (f x) t) :
  max_value f (P ∪₁ P') t -> max_value f P t.
Proof.
  intros MAX; red in MAX; desf; red; split; unnw; ins.
  1,3: by apply UB; left.
  { destruct (classic (exists a, P a)) as [[a PP]|NN]; [right|left].
    { exists a; split; auto. apply Time.bot_spec. }
    split; auto. intros a PP. apply NN. eexists; eauto. }
  destruct INam as [H|H].
  { right; eexists; eauto. }
  exfalso. eapply Time.lt_strorder.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma max_value_same_value f S a b
      (H : max_value f S a) (B : max_value f S b) :
  a = b.
Proof.
  red in H; red in B; desf.
  { exfalso. eapply MAX; eauto. }
  { exfalso. eapply MAX0; eauto. }
  specialize (UB0 a_max INam).
  specialize (UB a_max0 INam0).
  apply TimeFacts.antisym.
  all: etransitivity; eauto. 
Qed.

Lemma timemap_same_max_value_implies_eq f S (a b : TimeMap.t)
      (H : forall l, max_value f (S l) (a l)) (B : forall l, max_value f (S l) (b l)):
  a = b.
Proof.
  apply LocFun.ext.
  intros l. specialize (H l). specialize (B l).
  eapply max_value_same_value; eauto.
Qed.

Lemma view_same_max_value_implies_eq f S a b
      (A_PLN_RLX : TimeMap.eq (View.pln a) (View.rlx a))
      (B_PLN_RLX : TimeMap.eq (View.pln b) (View.rlx b))
      (H : forall l, max_value f (S l) (View.rlx a l))
      (B : forall l, max_value f (S l) (View.rlx b l)) :
  a = b.
Proof.
  apply View.ext.
  rewrite A_PLN_RLX. rewrite B_PLN_RLX.
  all: eapply timemap_same_max_value_implies_eq; eauto.
Qed.

Lemma max_value_bot_f S :
  max_value (fun _ => Time.bot) S Time.bot.
Proof.
  red. splits.
  { ins. apply Time.bot_spec. }
  destruct (classic (exists e, S e)) as [[e SE]|SE]; [right|left].
  { exists e. split; auto. apply Time.bot_spec. }
  split; auto. by apply not_ex_all_not.
Qed.

End MaxValue.
