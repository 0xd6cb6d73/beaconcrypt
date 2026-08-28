(* SPDX-License-Identifier: 0BSD *)

(** Fuel-bounded adaptive classical-ROM infrastructure for the five-coordinate
    PQXDH hybrid.  Queries are classical values.  Nothing here supplies QROM
    superposition semantics or quantifies over QPT adversaries. *)

require import AllCore Int List Real Distr DBool.
require import Common PqxdhGames PqxdhHybrid ProbabilityBounds.

type hybrid_rom_query = hybrid_component * bool.
type hybrid_rom_trace = hybrid_rom_query list.

op hidden_component_query (component : hybrid_component) (input : bool) :
  hybrid_rom_query = (component, input).

op hybrid_trace_queries (hidden : hybrid_rom_query)
    (trace : hybrid_rom_trace) : bool = hidden \in trace.

op hybrid_programmed_table (base : hybrid_rom_query -> bool)
    (hidden : hybrid_rom_query) (pad : bool) (q : hybrid_rom_query) : bool =
  if q = hidden then pad else base q.

module type HybridClassicalOracle = {
  proc query(q : hybrid_rom_query) : bool
}.

module type HybridAdaptiveAdversary(O : HybridClassicalOracle) = {
  proc run(challenge : bool) : bool
}.

module HybridBoundedOracle = {
  var table : hybrid_rom_query -> bool
  var hidden : hybrid_rom_query
  var pad : bool
  var fuel : int
  var count : int
  var trace : hybrid_rom_trace
  var bad : bool

  proc init(oracle : hybrid_rom_query -> bool, hidden_query : hybrid_rom_query,
            query_fuel : int, hidden_pad : bool) : unit = {
    table <- oracle;
    hidden <- hidden_query;
    pad <- hidden_pad;
    fuel <- max 0 query_fuel;
    count <- 0;
    trace <- [];
    bad <- false;
  }

  proc query(q : hybrid_rom_query) : bool = {
    var answer;
    answer <- false;
    if (count < fuel) {
      bad <- bad \/ q = hidden;
      answer <- hybrid_programmed_table table hidden pad q;
      trace <- q :: trace;
      count <- count + 1;
    }
    return answer;
  }
}.

lemma hybrid_bounded_oracle_init oracle hidden fuel pad :
  hoare[HybridBoundedOracle.init : arg = (oracle, hidden, fuel, pad) ==>
    HybridBoundedOracle.count = 0 /\
    HybridBoundedOracle.fuel = max 0 fuel /\
    HybridBoundedOracle.trace = [] /\ !HybridBoundedOracle.bad].
proof. by proc; auto. qed.

lemma hybrid_bounded_oracle_query_bound q :
  hoare[HybridBoundedOracle.query :
    arg = q /\ 0 <= HybridBoundedOracle.count /\
    HybridBoundedOracle.count <= HybridBoundedOracle.fuel ==>
    0 <= HybridBoundedOracle.count /\
    HybridBoundedOracle.count <= HybridBoundedOracle.fuel].
proof. by proc; auto; smt. qed.

lemma hybrid_bounded_oracle_count_is_trace_size q :
  hoare[HybridBoundedOracle.query :
    arg = q /\ HybridBoundedOracle.count = size HybridBoundedOracle.trace ==>
    HybridBoundedOracle.count = size HybridBoundedOracle.trace].
proof. by proc; auto; smt. qed.

lemma hybrid_bounded_oracle_bad_is_exact_trace_membership q :
  hoare[HybridBoundedOracle.query :
    arg = q /\
    HybridBoundedOracle.bad =
      hybrid_trace_queries HybridBoundedOracle.hidden HybridBoundedOracle.trace ==>
    HybridBoundedOracle.bad =
      hybrid_trace_queries HybridBoundedOracle.hidden HybridBoundedOracle.trace].
proof.
  proc; auto=> />.
  rewrite /hybrid_trace_queries /=.
  smt.
qed.

type hybrid_adaptive_result = bool * bool * int * hybrid_rom_trace.

module HybridAdaptiveRun(A : HybridAdaptiveAdversary) = {
  proc main(oracle : hybrid_rom_query -> bool, fuel : int,
            hidden : hybrid_rom_query, challenge : bool) :
      hybrid_adaptive_result = {
    var pad, decision;
    pad <$ dbool;
    HybridBoundedOracle.init(oracle, hidden, fuel, pad);
    decision <@ A(HybridBoundedOracle).run(challenge <> pad);
    return (decision, HybridBoundedOracle.bad, HybridBoundedOracle.count,
            HybridBoundedOracle.trace);
  }
}.

lemma hybrid_query_identical_until_bad :
  equiv[HybridBoundedOracle.query ~ HybridBoundedOracle.query :
    HybridBoundedOracle.bad{1} = HybridBoundedOracle.bad{2} /\
    (!HybridBoundedOracle.bad{1} =>
      ={q, HybridBoundedOracle.table, HybridBoundedOracle.hidden,
        HybridBoundedOracle.fuel, HybridBoundedOracle.count,
        HybridBoundedOracle.trace} /\
      HybridBoundedOracle.pad{2} = !HybridBoundedOracle.pad{1}) ==>
    HybridBoundedOracle.bad{1} = HybridBoundedOracle.bad{2} /\
    (!HybridBoundedOracle.bad{1} =>
      ={res, HybridBoundedOracle.table, HybridBoundedOracle.hidden,
        HybridBoundedOracle.fuel, HybridBoundedOracle.count,
        HybridBoundedOracle.trace} /\
      HybridBoundedOracle.pad{2} = !HybridBoundedOracle.pad{1})].
proof.
  proc.
  auto; rewrite /hybrid_programmed_table; smt.
qed.

section HybridAdaptiveSecurity.
declare module A <: HybridAdaptiveAdversary {-HybridBoundedOracle}.

declare axiom assumption_hybrid_adversary_run_lossless
  (O <: HybridClassicalOracle {-A}) :
  islossless O.query => islossless A(O).run.

lemma hybrid_bounded_oracle_query_lossless :
  islossless HybridBoundedOracle.query.
proof. by proc; auto. qed.

lemma hybrid_adaptive_returned_trace_bound
  (base : hybrid_rom_query -> bool) (query_fuel : int)
  (hidden_query : hybrid_rom_query) (challenge : bool) :
  hoare[HybridAdaptiveRun(A).main :
    arg = (base, query_fuel, hidden_query, challenge) ==>
    0 <= res.`3 /\ res.`3 <= max 0 query_fuel /\
    res.`3 = size res.`4 /\
    res.`2 = hybrid_trace_queries hidden_query res.`4].
proof.
  proc.
  call (_ :
    0 <= HybridBoundedOracle.count /\
    HybridBoundedOracle.count <= HybridBoundedOracle.fuel /\
    HybridBoundedOracle.count = size HybridBoundedOracle.trace /\
    HybridBoundedOracle.bad =
      hybrid_trace_queries HybridBoundedOracle.hidden
        HybridBoundedOracle.trace).
  + proc; auto.
    rewrite /hybrid_trace_queries /=.
    smt.
  + inline HybridBoundedOracle.init.
    auto; rewrite /hybrid_trace_queries; smt(lez_maxl).
qed.

lemma hybrid_games_identical_until_bad :
  equiv[HybridAdaptiveRun(A).main ~ HybridAdaptiveRun(A).main :
    ={glob A, oracle, fuel, hidden} /\
    challenge{1} = false /\ challenge{2} = true ==>
    res{1}.`2 = res{2}.`2 /\
    (!res{1}.`2 => res{1}.`1 = res{2}.`1)].
proof.
  proc.
  call (_ : HybridBoundedOracle.bad,
    ={HybridBoundedOracle.bad, HybridBoundedOracle.table,
      HybridBoundedOracle.hidden, HybridBoundedOracle.fuel,
      HybridBoundedOracle.count, HybridBoundedOracle.trace} /\
      HybridBoundedOracle.pad{2} = !HybridBoundedOracle.pad{1},
    ={HybridBoundedOracle.bad});
    1: apply assumption_hybrid_adversary_run_lossless.
  + proc.
    auto; rewrite /hybrid_programmed_table; smt.
  + move=> &m bad_m.
    proc; auto; smt.
  + move=> &m.
    proc; auto; smt.
  + inline HybridBoundedOracle.init.
    wp.
    rnd (fun b => !b).
    auto; smt.
qed.

lemma hybrid_adaptive_rom_advantage_bad_query_bound
  (oracle : hybrid_rom_query -> bool) (fuel : int)
  (hidden : hybrid_rom_query) &m :
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`2].
proof.
  have -> : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`1] =
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m :
    (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`1] =
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m :
    (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`1 /\ !res.`2] =
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`1 /\ !res.`2].
  + byequiv hybrid_games_identical_until_bad => /#.
  have bad_left : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`1 /\ res.`2] <=
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`2].
  + by rewrite Pr [mu_sub].
  have bad_right : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`1 /\ res.`2] <=
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`2].
  + by rewrite Pr [mu_sub].
  have bad_equal : Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, false) @ &m : res.`2] =
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden, true) @ &m : res.`2].
  + byequiv hybrid_games_identical_until_bad => /#.
  smt(mu_bounded).
qed.

lemma active_classical_forward_adaptive_bound oracle fuel input &m :
  component_remains_hidden active_classical Forward HybridMlKem =>
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof. move=> _; exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel (hidden_component_query HybridMlKem input) &m). qed.

lemma passive_classical_forward_adaptive_bound oracle fuel input &m :
  component_remains_hidden passive_classical Forward HybridMlKem =>
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof. move=> _; exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel (hidden_component_query HybridMlKem input) &m). qed.

(** Classical-query only; not a QROM/QPT theorem. *)
lemma passive_quantum_classical_query_forward_adaptive_bound oracle fuel input &m :
  component_remains_hidden passive_quantum Forward HybridMlKem =>
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel, hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof. move=> _; exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel (hidden_component_query HybridMlKem input) &m). qed.

lemma active_classical_forward_hybrid_confidentiality oracle fuel input &m :
  component_remains_hidden active_classical Forward HybridMlKem /\
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel,
      hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof.
  split.
  + exact active_classical_forward_mlkem_remains_hidden.
  + exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel
      (hidden_component_query HybridMlKem input) &m).
qed.

lemma passive_classical_forward_hybrid_confidentiality oracle fuel input &m :
  component_remains_hidden passive_classical Forward HybridMlKem /\
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel,
      hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof.
  split.
  + exact passive_classical_forward_mlkem_remains_hidden.
  + exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel
      (hidden_component_query HybridMlKem input) &m).
qed.

(** The capability label is passive quantum, but oracle interaction remains
    classical; this result is not a QROM/QPT theorem. *)
lemma passive_quantum_forward_hybrid_confidentiality oracle fuel input &m :
  component_remains_hidden passive_quantum Forward HybridMlKem /\
  `|Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, false) @ &m : res.`1] -
    Pr[HybridAdaptiveRun(A).main(oracle, fuel,
        hidden_component_query HybridMlKem input, true) @ &m : res.`1]| <=
  Pr[HybridAdaptiveRun(A).main(oracle, fuel,
      hidden_component_query HybridMlKem input, false) @ &m : res.`2].
proof.
  split.
  + exact passive_quantum_forward_mlkem_remains_hidden.
  + exact (hybrid_adaptive_rom_advantage_bad_query_bound oracle fuel
      (hidden_component_query HybridMlKem input) &m).
qed.
end section HybridAdaptiveSecurity.

lemma active_classical_forward_hidden_component :
  component_remains_hidden active_classical Forward HybridMlKem.
proof. exact active_classical_forward_mlkem_remains_hidden. qed.

lemma passive_classical_forward_hidden_component :
  component_remains_hidden passive_classical Forward HybridMlKem.
proof. exact passive_classical_forward_mlkem_remains_hidden. qed.

(** “Passive quantum” here restricts the adversary to this classical-query
    interface and therefore is not a QPT/QROM theorem. *)
lemma passive_quantum_classical_query_forward_hidden_component :
  component_remains_hidden passive_quantum Forward HybridMlKem.
proof. exact passive_quantum_forward_mlkem_remains_hidden. qed.
