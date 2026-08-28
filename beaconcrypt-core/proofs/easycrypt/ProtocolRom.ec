(* SPDX-License-Identifier: 0BSD *)

(** Finite, bounded classical-ROM bookkeeping used by the protocol reduction.
    Queries are ordinary lists: there are no superposition queries or QROM
    semantics in this file. *)

require import AllCore Bool Int List.

type rom_domain = bool.
type rom_input = bool.
type rom_query = rom_domain * rom_input.
type rom_answer = bool * bool * bool.
type rom_entry = rom_query * rom_answer.
type rom_trace = rom_entry list.

op root_domain : rom_domain = false.
op symmetric_domain : rom_domain = true.
op root_query (x : rom_input) : rom_query = (root_domain, x).
op symmetric_query (x : rom_input) : rom_query = (symmetric_domain, x).

lemma protocol_rom_domain_separation (x y : rom_input) :
  root_query x <> symmetric_query y.
proof. by rewrite /root_query /symmetric_query /root_domain /symmetric_domain. qed.

op trace_queries (q : rom_query) (tr : rom_trace) : bool =
  q \in map fst tr.

op trace_consistent (oracle : rom_query -> rom_answer) (tr : rom_trace) : bool =
  all (fun (e : rom_entry) => e.`2 = oracle e.`1) tr.

op bounded_rom_query_count (fuel attempted : int) : int =
  if attempted <= fuel then attempted else fuel.

lemma bounded_rom_query_count_bound (fuel attempted : int) :
  0 <= fuel => 0 <= attempted =>
  0 <= bounded_rom_query_count fuel attempted /\
  bounded_rom_query_count fuel attempted <= fuel.
proof. by rewrite /bounded_rom_query_count; smt. qed.

lemma bounded_rom_trace_consistent_empty (oracle : rom_query -> rom_answer) :
  trace_consistent oracle [] .
proof. by rewrite /trace_consistent. qed.

lemma bounded_rom_trace_consistent_extend
  (oracle : rom_query -> rom_answer) (tr : rom_trace) (q : rom_query) :
  trace_consistent oracle tr =>
  trace_consistent oracle ((q, oracle q) :: tr).
proof. by rewrite /trace_consistent /=. qed.

op flip_answer (a : rom_answer) : rom_answer = (!a.`1, a.`2, a.`3).
op reprogram (oracle : rom_query -> rom_answer) (hidden q : rom_query) : rom_answer =
  if q = hidden then flip_answer (oracle q) else oracle q.

lemma reprogram_away (oracle : rom_query -> rom_answer) hidden q :
  q <> hidden => reprogram oracle hidden q = oracle q.
proof. by move=> ne; rewrite /reprogram ne. qed.

lemma reprogram_involutive (oracle : rom_query -> rom_answer) hidden q :
  reprogram (reprogram oracle hidden) hidden q = oracle q.
proof.
  rewrite /reprogram.
  case (q = hidden)=> //=.
  by rewrite /flip_answer; case (oracle q)=> x yz; case yz=> y z /=.
qed.

op bounded_rom_extract_hidden (hidden : rom_query) (tr : rom_trace) : bool =
  trace_queries hidden tr.

lemma bounded_rom_same_run_extractor_reduction
  (hidden : rom_query) (tr : rom_trace) :
  trace_queries hidden tr => bounded_rom_extract_hidden hidden tr.
proof. by rewrite /bounded_rom_extract_hidden. qed.

(** Beaconcrypt's protocol hidden query is in the symmetric domain and hence
    cannot alias the PQXDH root query. *)
op protocol_hidden_pad_query (initial_chain : bool) : rom_query =
  symmetric_query initial_chain.

lemma protocol_root_hidden_pad_domain_separation root initial_chain :
  root_query root <> protocol_hidden_pad_query initial_chain.
proof. exact (protocol_rom_domain_separation root initial_chain). qed.

op protocol_bad_query_event (hidden : rom_query) (tr : rom_trace) : bool =
  trace_queries hidden tr.

(** Stateful classical oracle interface.  Calls after [fuel] return a public
    default and are not added to the accepted-query trace.  Thus even an
    adversary that keeps calling cannot make the recorded trace exceed fuel. *)
module type ClassicalRomOracle = {
  proc query(q : rom_query) : rom_answer
}.

module type ClassicalRomAdversary(O : ClassicalRomOracle) = {
  proc run(challenge_ciphertext : bool) : bool
}.

op default_rom_answer : rom_answer = (false, false, false).

module BoundedClassicalRom = {
  var table : rom_query -> rom_answer
  var fuel : int
  var count : int
  var trace : rom_trace

  proc init(oracle : rom_query -> rom_answer, query_fuel : int) : unit = {
    table <- oracle;
    fuel <- max 0 query_fuel;
    count <- 0;
    trace <- [];
  }

  proc query(q : rom_query) : rom_answer = {
    var answer;
    answer <- default_rom_answer;
    if (count < fuel) {
      answer <- table q;
      trace <- (q, answer) :: trace;
      count <- count + 1;
    }
    return answer;
  }
}.

lemma bounded_classical_rom_init(oracle : rom_query -> rom_answer) fuel :
  hoare[BoundedClassicalRom.init : arg = (oracle, fuel) ==>
    BoundedClassicalRom.count = 0 /\
    BoundedClassicalRom.fuel = max 0 fuel /\
    BoundedClassicalRom.trace = [] /\
    trace_consistent oracle BoundedClassicalRom.trace].
proof. by proc; auto; rewrite /trace_consistent. qed.

lemma bounded_classical_rom_query_preserves_bound(q : rom_query) :
  hoare[BoundedClassicalRom.query :
    arg = q /\ 0 <= BoundedClassicalRom.count /\
    BoundedClassicalRom.count <= BoundedClassicalRom.fuel ==>
    0 <= BoundedClassicalRom.count /\
    BoundedClassicalRom.count <= BoundedClassicalRom.fuel].
proof. by proc; auto; smt. qed.

lemma bounded_classical_rom_query_preserves_consistency(q : rom_query) :
  hoare[BoundedClassicalRom.query :
    arg = q /\ trace_consistent BoundedClassicalRom.table
      BoundedClassicalRom.trace ==>
    trace_consistent BoundedClassicalRom.table BoundedClassicalRom.trace].
proof. by proc; auto; rewrite /trace_consistent /=. qed.

lemma bounded_classical_rom_count_matches_trace(q : rom_query) :
  hoare[BoundedClassicalRom.query :
    arg = q /\ BoundedClassicalRom.count = size BoundedClassicalRom.trace ==>
    BoundedClassicalRom.count = size BoundedClassicalRom.trace].
proof. by proc; auto; smt. qed.

module ProtocolClassicalRomGame(A : ClassicalRomAdversary) = {
  proc main(oracle : rom_query -> rom_answer, fuel : int,
            challenge : bool, pad : bool, hidden : rom_query) : bool * bool = {
    var decision;
    BoundedClassicalRom.init(oracle, fuel);
    decision <@ A(BoundedClassicalRom).run(challenge <> pad);
    return (decision, protocol_bad_query_event hidden BoundedClassicalRom.trace);
  }
}.
