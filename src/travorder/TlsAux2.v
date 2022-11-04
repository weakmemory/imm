From hahn Require Import Hahn.

From imm Require Import AuxDef Events Execution.
From imm Require Import Execution_eco imm_s_hb imm_s imm_bob.
From imm Require Import imm_s_ppo CombRelations.
From imm Require Import imm_s_rfppo.
From imm Require Import FinExecution.

From imm Require Import TraversalOrder.
From imm Require Import TLSCoherency.
From imm Require Import IordCoherency.

From imm Require Import AuxRel2.

Set Implicit Arguments.

Section TLSCoherentMore.
Context G G'
        (EQACTS : acts_set    G' ≡₁ acts_set    G)
        (EQTIDS : threads_set G' ≡₁ threads_set G)
        (EQW    : is_w (lab G')  ≡₁ is_w (lab G))
        T
        (TCOH   : tls_coherent G T).

Lemma is_ta_propagate_to_G_more :
  is_ta_propagate_to_G G' ≡₁ is_ta_propagate_to_G G.
Proof using EQTIDS.
  unfold is_ta_propagate_to_G.
  now rewrite EQTIDS.
Qed.

Lemma init_tls_more : init_tls G' ≡₁ init_tls G.
Proof using EQACTS EQTIDS.
  unfold init_tls.
  apply set_pair_more.
  2: now rewrite EQACTS.
  now rewrite is_ta_propagate_to_G_more.
Qed.

Lemma exec_tls_more : exec_tls G' ≡₁ exec_tls G.
Proof using EQACTS EQTIDS EQW.
  unfold exec_tls.
  rewrite EQACTS.
  rewrite is_ta_propagate_to_G_more.
  now rewrite EQW.
Qed.

Lemma tls_coherent_more : tls_coherent G' T.
Proof using EQACTS EQTIDS EQW TCOH.
  destruct TCOH as [AA BB].
  constructor.
  all: rewrite init_tls_more; auto.
  rewrite exec_tls_more; auto.
Qed.

End TLSCoherentMore.
