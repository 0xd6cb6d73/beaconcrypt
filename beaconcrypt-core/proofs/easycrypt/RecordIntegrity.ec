(* SPDX-License-Identifier: 0BSD *)

(** Capstones for the bounded record-integrity game.

    The authentication table and its probability distribution remain hidden.
    The main results classify one public trace and extract same-run collision
    witnesses.  A separate one-bit fresh-tag sanity game proves exact one-half
    acceptance; it is not an AEAD-integrity or production-width bound. *)

require import AllCore Int List Real Distr DBool.
require import Ctx.

type record_context = associated_data * sequence_number * sender_id.
type record_auth_input = record_context * ciphertext_core.
type record_trace = record_auth_input list.

op record_context_ad (context : record_context) = context.`1.
op record_context_sequence (context : record_context) = context.`2.
op record_context_sender (context : record_context) = context.`3.

type record_payload = ciphertext_core * digest.
op record_payload_ciphertext (payload : record_payload) = payload.`1.
op record_payload_tag (payload : record_payload) = payload.`2.

type record_attempt = record_context * record_payload.
op record_attempt_context (attempt : record_attempt) = attempt.`1.
op record_attempt_payload (attempt : record_attempt) = attempt.`2.
op record_attempt_input (attempt : record_attempt) : record_auth_input =
  (record_attempt_context attempt,
   record_payload_ciphertext (record_attempt_payload attempt)).

op record_candidate_accepted (attempt : record_attempt)
                             (table_answer : digest) : bool =
  table_answer = record_payload_tag (record_attempt_payload attempt).

op record_known_input_attempt (trace : record_trace)
                              (attempt : record_attempt) : bool =
  record_attempt_input attempt \in trace.

op record_fresh_tag_guess (trace : record_trace)
                          (attempt : record_attempt)
                          (table_answer : digest) : bool =
  !record_known_input_attempt trace attempt /\
  record_candidate_accepted attempt table_answer.

op record_active_modification (honest_context : record_context)
                              (honest_payload : record_payload)
                              (attempt : record_attempt)
                              (table_answer : digest) : bool =
  record_candidate_accepted attempt table_answer /\
  (record_attempt_context attempt <> honest_context \/
   record_attempt_payload attempt <> honest_payload).

(** Exact query-or-guess classification.  This is bookkeeping, not a primitive
    forgery reduction: the fresh branch is definitionally the accepted guess
    made without a prior exact-input query. *)
lemma record_active_modification_query_or_guess_classification
  (trace : record_trace) (honest_context : record_context)
  (honest_payload : record_payload) (attempt : record_attempt)
  (table_answer : digest) :
  record_active_modification honest_context honest_payload attempt table_answer =>
  record_known_input_attempt trace attempt \/
  record_fresh_tag_guess trace attempt table_answer.
proof.
  rewrite /record_active_modification /record_fresh_tag_guess.
  smt.
qed.

op record_collision (left right : record_auth_input * digest) : bool =
  left.`1 <> right.`1 /\ left.`2 = right.`2.

op record_cross_context_reuse
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) : bool =
  record_candidate_accepted attempt table_answer /\
  record_attempt_payload attempt = honest_payload /\
  record_attempt_context attempt <> honest_context.

op record_cross_sequence_reuse
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) : bool =
  record_candidate_accepted attempt table_answer /\
  record_attempt_payload attempt = honest_payload /\
  record_context_sequence (record_attempt_context attempt) <>
    record_context_sequence honest_context.

op record_extracted_collision
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) : bool =
  record_collision
    ((honest_context, record_payload_ciphertext honest_payload),
      record_payload_tag honest_payload)
    (record_attempt_input attempt, table_answer).

lemma record_cross_context_reuse_implies_collision
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) :
  record_cross_context_reuse honest_context honest_payload attempt table_answer =>
  record_extracted_collision honest_context honest_payload attempt table_answer.
proof.
  rewrite /record_cross_context_reuse /record_extracted_collision
    /record_collision /record_candidate_accepted /record_attempt_input.
  smt.
qed.

lemma record_cross_sequence_reuse_implies_cross_context
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) :
  record_cross_sequence_reuse honest_context honest_payload attempt table_answer =>
  record_cross_context_reuse honest_context honest_payload attempt table_answer.
proof.
  rewrite /record_cross_sequence_reuse /record_cross_context_reuse.
  smt.
qed.

lemma record_cross_sequence_reuse_implies_collision
  (honest_context : record_context) (honest_payload : record_payload)
  (attempt : record_attempt) (table_answer : digest) :
  record_cross_sequence_reuse honest_context honest_payload attempt table_answer =>
  record_extracted_collision honest_context honest_payload attempt table_answer.
proof.
  move=> cross_sequence.
  apply (record_cross_context_reuse_implies_collision
    honest_context honest_payload attempt table_answer).
  exact (record_cross_sequence_reuse_implies_cross_context
    honest_context honest_payload attempt table_answer cross_sequence).
qed.

op record_verified_trace (candidate : record_auth_input)
                         (adversary_trace : record_trace) : record_trace =
  adversary_trace ++ [candidate].

(** The record verifier adds exactly one authentication-table query. *)
lemma record_integrity_trace_size_bound
  (fuel : int) (candidate : record_auth_input)
  (adversary_trace : record_trace) :
  0 <= fuel => size adversary_trace <= fuel =>
  size (record_verified_trace candidate adversary_trace) <= fuel + 1.
proof.
  move=> ge0 bounded.
  rewrite /record_verified_trace size_cat /=.
  smt.
qed.

type record_tag_table = record_auth_input -> digest.
type record_integrity_observation =
  record_trace * record_context * record_payload * record_attempt * digest.

module type RecordIntegrityAdversary = {
  proc run(honest_context : record_context, honest_payload : record_payload)
    : record_trace * record_attempt
}.

module RecordIntegrityEvents(A : RecordIntegrityAdversary) = {
  proc main(table : record_tag_table, honest_context : record_context,
            honest_ciphertext : ciphertext_core)
      : bool * bool * bool * bool = {
    var honest_payload, result, trace, attempt, answer;
    var active, known, fresh, collision;
    honest_payload <- (honest_ciphertext,
      table (honest_context, honest_ciphertext));
    result <@ A.run(honest_context, honest_payload);
    trace <- result.`1;
    attempt <- result.`2;
    answer <- table (record_attempt_input attempt);
    active <- record_active_modification honest_context honest_payload attempt answer;
    known <- record_known_input_attempt trace attempt;
    fresh <- record_fresh_tag_guess trace attempt answer;
    collision <- record_extracted_collision honest_context honest_payload attempt answer;
    return (active, known, fresh, collision);
  }
}.

lemma record_active_modification_probability_classification
  (A <: RecordIntegrityAdversary) (table : record_tag_table)
  (honest_context : record_context) (honest_ciphertext : ciphertext_core) &m :
  Pr[RecordIntegrityEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`1] <=
  Pr[RecordIntegrityEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`2 \/ res.`3].
proof.
  byequiv (_ : ={glob A, table, honest_context, honest_ciphertext} ==>
    res{1}.`1 => res{2}.`2 \/ res{2}.`3) => //.
  proc; wp.
  call (_ : true).
  auto; smt(record_active_modification_query_or_guess_classification).
qed.

module RecordCollisionEvents(A : RecordIntegrityAdversary) = {
  proc main(table : record_tag_table, honest_context : record_context,
            honest_ciphertext : ciphertext_core) : bool * bool * bool = {
    var honest_payload, result, attempt, answer;
    var cross_context, cross_sequence, collision;
    honest_payload <- (honest_ciphertext,
      table (honest_context, honest_ciphertext));
    result <@ A.run(honest_context, honest_payload);
    attempt <- result.`2;
    answer <- table (record_attempt_input attempt);
    cross_context <- record_cross_context_reuse honest_context honest_payload
      attempt answer;
    cross_sequence <- record_cross_sequence_reuse honest_context honest_payload
      attempt answer;
    collision <- record_extracted_collision honest_context honest_payload
      attempt answer;
    return (cross_context, cross_sequence, collision);
  }
}.

lemma record_cross_context_collision_probability_bound
  (A <: RecordIntegrityAdversary) (table : record_tag_table)
  (honest_context : record_context) (honest_ciphertext : ciphertext_core) &m :
  Pr[RecordCollisionEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`1] <=
  Pr[RecordCollisionEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`3].
proof.
  byequiv (_ : ={glob A, table, honest_context, honest_ciphertext} ==>
    res{1}.`1 => res{2}.`3) => //.
  proc; wp.
  call (_ : true).
  auto; smt(record_cross_context_reuse_implies_collision).
qed.

lemma record_cross_sequence_collision_probability_bound
  (A <: RecordIntegrityAdversary) (table : record_tag_table)
  (honest_context : record_context) (honest_ciphertext : ciphertext_core) &m :
  Pr[RecordCollisionEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`2] <=
  Pr[RecordCollisionEvents(A).main(table, honest_context, honest_ciphertext) @ &m : res.`3].
proof.
  byequiv (_ : ={glob A, table, honest_context, honest_ciphertext} ==>
    res{1}.`2 => res{2}.`3) => //.
  proc; wp.
  call (_ : true).
  auto; smt(record_cross_sequence_reuse_implies_collision).
qed.

module type OneBitFreshTagAdversary = {
  proc guess() : bool
}.

(** The sampled tag is local to the game and unavailable to the arbitrary
    adversary.  This is the finite one-bit fresh-input case. *)
module OneBitFreshTagGame(A : OneBitFreshTagAdversary) = {
  proc main() : bool = {
    var tag, guess;
    guess <@ A.guess();
    tag <$ {0,1};
    return guess = tag;
  }
}.

lemma record_uniform_one_bit_fixed_guess_probability (guess : bool) :
  mu dbool (fun tag => guess = tag) = 1%r / 2%r.
proof.
  rewrite dboolE.
  by case guess.
qed.

lemma record_uniform_one_bit_success_failure_symmetry
  (A <: OneBitFreshTagAdversary) &m :
  Pr[OneBitFreshTagGame(A).main() @ &m : res] =
  Pr[OneBitFreshTagGame(A).main() @ &m : !res].
proof.
  byequiv (_ : ={glob A} ==> res{1} = !res{2}) => //.
  proc; wp.
  rnd (fun tag => !tag) (fun tag => !tag).
  call (_ : true).
  auto=> /> tag guess; case tag; case guess; smt.
qed.

lemma one_bit_fresh_tag_game_ll (A <: OneBitFreshTagAdversary) :
  islossless A.guess => islossless OneBitFreshTagGame(A).main.
proof.
  move=> A_guess_ll.
  proc; islossless.
qed.

lemma record_uniform_one_bit_fresh_tag_acceptance_exact
  (A <: OneBitFreshTagAdversary) &m :
  islossless A.guess =>
  Pr[OneBitFreshTagGame(A).main() @ &m : res] = 1%r / 2%r.
proof.
  move=> A_guess_ll.
  have symmetry_eq :
    Pr[OneBitFreshTagGame(A).main() @ &m : res] =
      Pr[OneBitFreshTagGame(A).main() @ &m : !res].
  + exact (record_uniform_one_bit_success_failure_symmetry A &m).
  have complement_eq :
    Pr[OneBitFreshTagGame(A).main() @ &m : !res] =
      1%r - Pr[OneBitFreshTagGame(A).main() @ &m : res].
  + rewrite Pr[mu_not].
    congr => //.
    by byphoare (one_bit_fresh_tag_game_ll A A_guess_ll).
  smt.
qed.
