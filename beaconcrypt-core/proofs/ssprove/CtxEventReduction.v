(* SPDX-License-Identifier: 0BSD *)

(** The computational part of CTX binding is an event reduction: every successful protocol misattribution must give the reduction a hash collision. The deterministic implication is supplied by the CTX contract; this file only lifts it to SSProve's probability semantics. *)

From Stdlib Require Import Utf8.
From mathcomp Require Import ssreflect ssrbool ssrnum eqtype choice reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr.

Local Open Scope ring_scope.

(** A run records the adversary's protocol-success bit and the collision bit extracted by the reduction. Keeping both in one observation constructs the collision experiment from the protocol execution without assuming an external coupling. *)
Definition ctx_observation : choiceType :=
  prod_choiceType bool_choiceType bool_choiceType.

Definition ctx_misattribution_event (outcome : ctx_observation) : bool :=
  fst outcome.

Definition ctx_collision_event (outcome : ctx_observation) : bool :=
  snd outcome.

Section CtxEventReduction.

  Variable experiment : {distr ctx_observation / R}.

  (** Cross-prover contract: the deterministic CTX witness maps every successful misattribution observation to a genuine hash collision. *)
  Hypothesis misattribution_yields_collision :
    {subset ctx_misattribution_event <= ctx_collision_event}.

  Theorem ctx_misattribution_reduces_to_collision :
    \P_[ experiment ] ctx_misattribution_event <=
    \P_[ experiment ] ctx_collision_event.
  Proof.
    exact: subset_pr misattribution_yields_collision.
  Qed.

End CtxEventReduction.

Print Assumptions ctx_misattribution_reduces_to_collision.
