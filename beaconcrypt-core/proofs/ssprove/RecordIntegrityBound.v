(* SPDX-License-Identifier: 0BSD *)

(** Exact one-bit fresh-authenticator bound for the existing bounded record verifier.

    This file works directly over the finite uniform hidden table and evaluates the exact [record_attach_verifier] runner from [RecordIntegrity]. It avoids the generic marginal-probability rewrite whose pinned implementation carries an unaccepted interchange dependency. A table-dependent involution flips the verifier answer at the completed adversary's fresh candidate input. Since that input differs from the honest input and is absent from the adversary trace, the honest payload and adaptive adversary execution are unchanged, while acceptance is toggled.

    The result is specific to a deterministic bounded adversary, one honest payload, one final candidate, and a one-bit ideal combined authenticator. The capstone is a direct probability over uniform tables that evaluates the exact runner pointwise; it does not prove a distribution-level bridge to [record_uniform_hidden_integrity_game]. It supplies no verification/decryption oracle, multi-record theorem, production-width bound, or composition theorem for separate AEAD and CTX primitives. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum order eqtype choice fintype finfun seq all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom RecordIntegrity.

Import Num.Theory.
Import Order.POrderTheory.
Import GRing.Theory.

Local Open Scope ring_scope.

Definition record_flip_tag_at
    (input : record_auth_input)
    (table : record_tag_table) : record_tag_table :=
  [ffun query => if query == input then negb (table query) else table query].

Lemma record_flip_tag_at_selected
    (input : record_auth_input) (table : record_tag_table) :
  record_flip_tag_at input table input = negb (table input).
Proof. by rewrite /record_flip_tag_at ffunE eqxx. Qed.

Lemma record_flip_tag_at_away
    (input query : record_auth_input) (table : record_tag_table) :
  query != input ->
  record_flip_tag_at input table query = table query.
Proof.
  move=> differs.
  by rewrite /record_flip_tag_at ffunE (negbTE differs).
Qed.

Lemma record_flip_tag_at_involutive (input : record_auth_input) :
  cancel (record_flip_tag_at input) (record_flip_tag_at input).
Proof.
  move=> table.
  apply/ffunP=> query.
  rewrite /record_flip_tag_at !ffunE.
  case: (query == input) => //=.
  by rewrite negbK.
Qed.

Definition record_trace_queries_input
    (input : record_auth_input) (trace : record_tag_trace) : bool :=
  has (fun entry => entry.1 == input) trace.

Lemma record_runs_agree_after_unqueried_flip
    (result : choiceType)
    (fuel : nat)
    (table : record_tag_table)
    (input : record_auth_input)
    (program : rom_tree record_auth_input bool result) :
  ~~ record_trace_queries_input input
    (run_bounded_rom record_auth_input bool fuel table program).2 ->
  run_bounded_rom record_auth_input bool fuel
      (record_flip_tag_at input table) program =
  run_bounded_rom record_auth_input bool fuel table program.
Proof.
  revert program.
  induction fuel as [| fuel induction_hypothesis];
    intros [value | query next]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite /record_trace_queries_input /=.
    move=> /norP [query_differs tail_avoids_input].
    rewrite (record_flip_tag_at_away input query table query_differs).
    rewrite (induction_hypothesis
      (next (table query)) tail_avoids_input).
    reflexivity.
Qed.

Section UniformFreshBound.

  Variable adversary_fuel : nat.
  Variable honest_context : record_context.
  Variable honest_ciphertext : bool.
  Variable adversary : record_payload ->
    rom_tree record_auth_input bool record_attempt.

  Definition record_bound_honest_input : record_auth_input :=
    (honest_context, honest_ciphertext).

  Definition record_bound_honest_payload
      (table : record_tag_table) : record_payload :=
    record_honest_payload table honest_context honest_ciphertext.

  Definition record_bound_preverification
      (table : record_tag_table) :
      (option record_attempt * record_tag_trace)%type :=
    let honest_payload := record_bound_honest_payload table in
    run_bounded_rom record_auth_input bool adversary_fuel table
      (adversary honest_payload).

  Definition record_bound_candidate_input
      (table : record_tag_table) : record_auth_input :=
    match (record_bound_preverification table).1 with
    | Some attempt => record_attempt_input attempt
    | None => record_bound_honest_input
    end.

  Definition record_bound_fresh_eligible
      (table : record_tag_table) : bool :=
    match (record_bound_preverification table).1 with
    | Some attempt =>
        (record_attempt_input attempt != record_bound_honest_input) &&
        ~~ record_trace_queries_input (record_attempt_input attempt)
          (record_bound_preverification table).2
    | None => false
    end.

  Definition record_bound_table_flip
      (table : record_tag_table) : record_tag_table :=
    if record_bound_fresh_eligible table
    then record_flip_tag_at (record_bound_candidate_input table) table
    else table.

  Lemma record_bound_honest_input_is_payload_input
      (table : record_tag_table) :
    record_auth_input_of honest_context
      (record_bound_honest_payload table) = record_bound_honest_input.
  Proof. reflexivity. Qed.

  Lemma record_bound_eligible_facts
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    exists attempt,
      (record_bound_preverification table).1 = Some attempt /\
      record_attempt_input attempt != record_bound_honest_input /\
      ~~ record_trace_queries_input (record_attempt_input attempt)
        (record_bound_preverification table).2.
  Proof.
    rewrite /record_bound_fresh_eligible.
    case execution: (record_bound_preverification table) => [result trace] /=.
    case: result execution=> [attempt |] execution //=.
    move=> /andP [differs unqueried].
    exists attempt.
    by repeat split=> //; rewrite execution.
  Qed.

  Lemma record_bound_flip_preserves_honest_payload
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    record_bound_honest_payload (record_bound_table_flip table) =
    record_bound_honest_payload table.
  Proof.
    move=> eligible.
    move: (record_bound_eligible_facts table eligible) =>
      [attempt [completed [candidate_differs unqueried]]].
    rewrite /record_bound_table_flip eligible
      /record_bound_honest_payload /record_honest_payload.
    congr (honest_ciphertext, _).
    apply: record_flip_tag_at_away.
    rewrite /record_bound_candidate_input completed.
    by rewrite eq_sym.
  Qed.

  Lemma record_bound_flip_preserves_preverification
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    record_bound_preverification (record_bound_table_flip table) =
    record_bound_preverification table.
  Proof.
    move=> eligible.
    move: (record_bound_eligible_facts table eligible) =>
      [attempt [completed [candidate_differs unqueried]]].
    rewrite /record_bound_preverification
      (record_bound_flip_preserves_honest_payload table eligible)
      /record_bound_table_flip eligible.
    apply: record_runs_agree_after_unqueried_flip.
    rewrite /record_bound_candidate_input completed.
    exact: unqueried.
  Qed.

  Lemma record_bound_flip_preserves_candidate
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    record_bound_candidate_input (record_bound_table_flip table) =
    record_bound_candidate_input table.
  Proof.
    move=> eligible.
    by rewrite /record_bound_candidate_input
      (record_bound_flip_preserves_preverification table eligible).
  Qed.

  Lemma record_bound_flip_preserves_eligibility
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    record_bound_fresh_eligible (record_bound_table_flip table).
  Proof.
    move=> eligible.
    by rewrite /record_bound_fresh_eligible
      (record_bound_flip_preserves_preverification table eligible).
  Qed.

  Lemma record_bound_table_flip_involutive :
    cancel record_bound_table_flip record_bound_table_flip.
  Proof.
    move=> table.
    case eligible: (record_bound_fresh_eligible table).
    - have eligible_flipped :
        record_bound_fresh_eligible (record_bound_table_flip table).
      { exact: record_bound_flip_preserves_eligibility. }
      have candidate_preserved :=
        record_bound_flip_preserves_candidate table eligible.
      rewrite [record_bound_table_flip (record_bound_table_flip table)]
        /record_bound_table_flip eligible_flipped.
      rewrite candidate_preserved
        [record_bound_table_flip table]/record_bound_table_flip eligible
        record_flip_tag_at_involutive.
      reflexivity.
    - have flip_identity : record_bound_table_flip table = table.
      { by rewrite /record_bound_table_flip eligible. }
      exact: eq_trans
        (congr1 record_bound_table_flip flip_identity) flip_identity.
  Qed.

  Lemma record_bound_table_flip_bijective :
    bijective record_bound_table_flip.
  Proof.
    exists record_bound_table_flip.
    - exact record_bound_table_flip_involutive.
    - exact record_bound_table_flip_involutive.
  Qed.

  Definition record_bound_full_observation
      (table : record_tag_table) : record_integrity_observation :=
    let honest_payload := record_bound_honest_payload table in
    run_bounded_rom record_auth_input bool (Nat.add adversary_fuel 1)
      table
      (record_attach_verifier honest_payload (adversary honest_payload)).

  Lemma record_attach_verifier_completed
      (table : record_tag_table)
      (honest_payload : record_payload)
      (program : rom_tree record_auth_input bool record_attempt)
      (attempt : record_attempt)
      (trace : record_tag_trace) :
    run_bounded_rom record_auth_input bool adversary_fuel table program =
      (Some attempt, trace) ->
    run_bounded_rom record_auth_input bool (Nat.add adversary_fuel 1) table
      (record_attach_verifier honest_payload program) =
      (Some (honest_payload,
          (attempt, table (record_attempt_input attempt))),
        rcons trace
          (record_attempt_input attempt,
            table (record_attempt_input attempt))).
  Proof.
    revert program attempt trace.
    induction adversary_fuel as [| fuel induction_hypothesis].
    - intros [value | query next] attempt trace; simpl.
      + move=> completed.
        inversion completed; subst value trace.
        reflexivity.
      + discriminate.
    - intros [value | query next] attempt trace; simpl.
      + move=> completed.
        inversion completed; subst value trace.
        case: (fuel + 1)%coq_nat; reflexivity.
      + case recursive_execution:
        (run_bounded_rom record_auth_input bool fuel table
          (next (table query))) => [recursive_result recursive_trace].
        move=> completed.
        inversion completed; subst recursive_result trace.
        rewrite (induction_hypothesis (next (table query)) attempt
          recursive_trace recursive_execution).
        reflexivity.
  Qed.

  Lemma record_attach_verifier_some_implies_adversary_some
      (table : record_tag_table)
      (honest_payload : record_payload)
      (program : rom_tree record_auth_input bool record_attempt)
      (verified : record_verified_attempt)
      (trace : record_tag_trace) :
    (run_bounded_rom record_auth_input bool (Nat.add adversary_fuel 1) table
      (record_attach_verifier honest_payload program)).1 = Some verified ->
    exists attempt,
      (run_bounded_rom record_auth_input bool adversary_fuel table program).1 =
      Some attempt.
  Proof.
    revert program verified trace.
    induction adversary_fuel as [| fuel induction_hypothesis].
    - intros [attempt | query next] verified trace; simpl.
      + by move=> _; exists attempt.
      + case: (next (table query)); discriminate.
    - intros [attempt | query next] verified trace; simpl.
      + by move=> _; exists attempt.
      + case attached_execution:
          (run_bounded_rom record_auth_input bool (fuel + 1)%coq_nat table
            (record_attach_verifier honest_payload (next (table query)))) =>
          [attached_result attached_trace].
        move=> completed.
        have recursive_some : attached_result = Some verified.
        { exact: completed. }
        move: (induction_hypothesis (next (table query)) verified
          attached_trace).
        rewrite attached_execution /=.
        move=> /(_ recursive_some) [attempt recursive_completed].
        exists attempt.
        exact: recursive_completed.
  Qed.

  Lemma record_bound_full_observation_of_eligible
      (table : record_tag_table) :
    record_bound_fresh_eligible table ->
    exists attempt trace,
      record_bound_preverification table = (Some attempt, trace) /\
      record_bound_full_observation table =
        (Some (record_bound_honest_payload table,
            (attempt, table (record_attempt_input attempt))),
          rcons trace
            (record_attempt_input attempt,
              table (record_attempt_input attempt))).
  Proof.
    move=> eligible.
    move: (record_bound_eligible_facts table eligible) =>
      [attempt [completed [candidate_differs unqueried]]].
    case execution: (record_bound_preverification table) => [result trace].
    rewrite execution in completed.
    case: result completed execution=> [actual_attempt |] completed execution.
    - inversion completed; subst actual_attempt.
      exists attempt, trace.
      split.
      + reflexivity.
      + rewrite /record_bound_full_observation.
        apply: record_attach_verifier_completed.
        move: execution.
        by rewrite /record_bound_preverification.
    - discriminate.
  Qed.

  Lemma record_adversary_trace_of_rcons
      (honest_payload : record_payload)
      (attempt : record_attempt)
      (answer : bool)
      (trace : record_tag_trace)
      (final_entry : record_auth_input * bool) :
    record_adversary_trace
      (Some (honest_payload, (attempt, answer)), rcons trace final_entry) =
    trace.
  Proof.
    rewrite /record_adversary_trace /= size_rcons.
    change (take (size trace) (rcons trace final_entry) = trace).
    by rewrite -cats1 take_size_cat.
  Qed.

  Lemma record_bound_fresh_event_characterization
      (table : record_tag_table) :
    record_fresh_tag_guess_event honest_context
      (record_bound_full_observation table) =
    record_bound_fresh_eligible table &&
      (table (record_bound_candidate_input table) ==
        record_tag
          (record_attempt_payload
            (odflt
              (honest_context,
                (honest_ciphertext,
                  table record_bound_honest_input))
              (record_bound_preverification table).1))).
  Proof.
    case eligible: (record_bound_fresh_eligible table).
    - move: (record_bound_full_observation_of_eligible table eligible) =>
        [attempt [trace [preexecution full_execution]]].
      rewrite full_execution /record_fresh_tag_guess_event
        /record_active_modification_event
        /record_active_modification_verified
        /record_candidate_accepted
        /record_candidate_differs_from_honest
        /record_candidate_was_queried
        record_adversary_trace_of_rcons /=.
      move: (record_bound_eligible_facts table eligible) =>
        [same_attempt [completed [candidate_differs unqueried]]].
      rewrite preexecution in completed.
      inversion completed; subst same_attempt.
      rewrite preexecution /= in candidate_differs unqueried.
      rewrite /record_bound_candidate_input preexecution /=
        /record_bound_honest_payload record_bound_honest_input_is_payload_input
        candidate_differs unqueried /=.
      by rewrite !andbT.
    - apply/eqP; rewrite eqbF_neg.
      apply/negP=> fresh_event.
      move: fresh_event.
      rewrite /record_fresh_tag_guess_event
        /record_active_modification_event.
      case full_execution: (record_bound_full_observation table) =>
        [[verified |] trace] //=.
      move=> /andP [/andP [accepted differs] unqueried].
      move: full_execution.
      rewrite /record_bound_full_observation.
      case preexecution:
        (record_bound_preverification table) => [result pretrace].
      case: result preexecution=> [attempt |] preexecution.
      + rewrite /record_bound_preverification in preexecution.
        rewrite (record_attach_verifier_completed table
          (record_bound_honest_payload table)
          (adversary (record_bound_honest_payload table))
          attempt pretrace preexecution).
        move=> completed_full.
        inversion completed_full; subst verified trace.
        move: differs unqueried.
        rewrite /record_candidate_differs_from_honest
          /record_candidate_was_queried
          record_adversary_trace_of_rcons
          record_bound_honest_input_is_payload_input /=.
        move=> differs unqueried.
        move: eligible.
        rewrite /record_bound_fresh_eligible
          /record_bound_preverification preexecution /=
          differs unqueried.
        discriminate.
      + rewrite /record_bound_preverification in preexecution.
        move=> impossible_completion.
        have full_some :
          (run_bounded_rom record_auth_input bool
            (Nat.add adversary_fuel 1) table
            (record_attach_verifier (record_bound_honest_payload table)
              (adversary (record_bound_honest_payload table)))).1 =
          Some verified.
        { by rewrite impossible_completion. }
        move: (record_attach_verifier_some_implies_adversary_some table
          (record_bound_honest_payload table)
          (adversary (record_bound_honest_payload table)) verified trace
          full_some) => [attempt adversary_some].
        rewrite preexecution /= in adversary_some.
        discriminate.
  Qed.

  Definition record_bound_success_event : pred record_tag_table :=
    fun table => record_fresh_tag_guess_event honest_context
      (record_bound_full_observation table).

  Definition record_bound_failure_event : pred record_tag_table :=
    fun table =>
      record_bound_fresh_eligible table &&
      ~~ record_bound_success_event table.

  Lemma record_bound_flip_toggles_success
      (table : record_tag_table) :
    record_bound_success_event (record_bound_table_flip table) =
    record_bound_failure_event table.
  Proof.
    rewrite /record_bound_failure_event.
    case eligible: (record_bound_fresh_eligible table).
    - move: (record_bound_eligible_facts table eligible) =>
        [attempt [completed [candidate_differs unqueried]]].
      have eligible_flipped :=
        record_bound_flip_preserves_eligibility table eligible.
      have preverification_preserved :=
        record_bound_flip_preserves_preverification table eligible.
      have candidate_preserved :=
        record_bound_flip_preserves_candidate table eligible.
      rewrite /record_bound_success_event
        !record_bound_fresh_event_characterization
        eligible_flipped /= candidate_preserved preverification_preserved
        completed.
      rewrite /record_bound_table_flip eligible
        record_flip_tag_at_selected.
      case candidate_tag:
        (record_tag (record_attempt_payload attempt));
      case table_answer:
        (table (record_bound_candidate_input table)) => /=; reflexivity.
    - have flip_identity : record_bound_table_flip table = table.
      { by rewrite /record_bound_table_flip eligible. }
      rewrite flip_identity /record_bound_success_event
        record_bound_fresh_event_characterization eligible.
      reflexivity.
  Qed.

  Lemma record_bound_uniform_event_reindex
      (event : pred record_tag_table) :
    \P_[uniform_hidden_rom_table record_auth_input bool false] event =
    \P_[uniform_hidden_rom_table record_auth_input bool false]
      (fun table => event (record_bound_table_flip table)).
  Proof.
    rewrite /pr.
    have flip_reindex :
      psum (fun table : record_tag_table =>
        ((nat_of_bool (event table))%:R *
          uniform_hidden_rom_table record_auth_input bool false table : R)) =
      psum (fun table : record_tag_table =>
        ((nat_of_bool (event (record_bound_table_flip table)))%:R *
          uniform_hidden_rom_table record_auth_input bool false
            (record_bound_table_flip table) : R)).
    {
      apply: reindex_psum.
      - by move=> table _.
      - exists record_bound_table_flip.
        + by move=> table _; apply: record_bound_table_flip_involutive.
        + by move=> table _; apply: record_bound_table_flip_involutive.
    }
    rewrite flip_reindex.
    apply: eq_psum=> table.
    congr (_ * _).
  Qed.

  Lemma record_bound_success_failure_disjoint :
    [predI record_bound_success_event & record_bound_failure_event] =1 pred0.
  Proof.
    move=> table.
    rewrite !inE /record_bound_failure_event.
    by rewrite andbCA andbN andbF.
  Qed.

  (** Exact finite bound: a fresh one-bit authenticator value can be guessed with probability at most one half, even after the bounded deterministic adversary adaptively queries every other input exposed by its trace. *)
  Theorem record_uniform_one_bit_fresh_tag_guess_bound :
    \P_[uniform_hidden_rom_table record_auth_input bool false]
      record_bound_success_event <= (1 / 2%:R : R).
  Proof.
    have success_equals_failure :
      \P_[uniform_hidden_rom_table record_auth_input bool false]
        record_bound_success_event =
      \P_[uniform_hidden_rom_table record_auth_input bool false]
        record_bound_failure_event.
    {
      rewrite (record_bound_uniform_event_reindex
        record_bound_success_event).
      apply: eq_pr=> table.
      exact: record_bound_flip_toggles_success.
    }
    have union_le_one :=
      le1_pr [predU record_bound_success_event & record_bound_failure_event]
        (uniform_hidden_rom_table record_auth_input bool false).
    have intersection_zero :
        \P_[uniform_hidden_rom_table record_auth_input bool false]
          [predI record_bound_success_event & record_bound_failure_event] = 0 :=
      pr_pred0_eq
        (uniform_hidden_rom_table record_auth_input bool false)
        record_bound_success_failure_disjoint.
    rewrite pr_or intersection_zero GRing.subr0 -success_equals_failure
      in union_le_one.
    rewrite ler_pdivlMr; last by rewrite ltr0n.
    rewrite GRing.mulr_natr.
    exact: union_le_one.
  Qed.

End UniformFreshBound.

Print Assumptions record_runs_agree_after_unqueried_flip.
Print Assumptions record_bound_table_flip_involutive.
Print Assumptions record_bound_flip_toggles_success.
Print Assumptions record_uniform_one_bit_fresh_tag_guess_bound.
