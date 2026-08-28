(* SPDX-License-Identifier: 0BSD *)

(** Adaptive classical-ROM identical-until-bad game.  The oracle exposes a bounded query interface to an arbitrary adversary module.  The two coupled worlds differ only in the first component of the hidden query's answer. *)

require import AllCore Bool Int List Real Distr DBool.
require import ProtocolRom.
require import Common PqxdhGames.

op pad_programmed_table (base : rom_query -> rom_answer)
                        (hidden : rom_query) (pad : bool)
                        (q : rom_query) : rom_answer =
  if q = hidden then (pad, (base q).`2, (base q).`3) else base q.

lemma pad_programmed_table_away base hidden pad q :
  q <> hidden => pad_programmed_table base hidden pad q = base q.
proof. by move=> ne; rewrite /pad_programmed_table ne. qed.

lemma pad_programmed_table_hidden base hidden pad :
  pad_programmed_table base hidden pad hidden =
    (pad, (base hidden).`2, (base hidden).`3).
proof. by rewrite /pad_programmed_table. qed.

module AdaptiveBoundedRom = {
  var base : rom_query -> rom_answer
  var hidden : rom_query
  var pad : bool
  var fuel : int
  var count : int
  var trace : rom_trace
  var bad : bool

  proc init(base_table : rom_query -> rom_answer, query_fuel : int,
            hidden_query : rom_query, hidden_pad : bool) : unit = {
    base <- base_table;
    hidden <- hidden_query;
    pad <- hidden_pad;
    fuel <- max 0 query_fuel;
    count <- 0;
    trace <- [];
    bad <- false;
  }

  proc query(q : rom_query) : rom_answer = {
    var answer;
    answer <- default_rom_answer;
    if (count < fuel) {
      bad <- bad \/ q = hidden;
      answer <- pad_programmed_table base hidden pad q;
      trace <- (q, answer) :: trace;
      count <- count + 1;
    }
    return answer;
  }
}.

module AdaptiveRomGame(A : ClassicalRomAdversary) = {
  proc main(base : rom_query -> rom_answer, fuel : int,
            hidden : rom_query, challenge : bool) : bool * bool = {
    var pad, challenge_ciphertext, decision;
    pad <$ dbool;
    challenge_ciphertext <- challenge <> pad;
    AdaptiveBoundedRom.init(base, fuel, hidden, pad);
    decision <@ A(AdaptiveBoundedRom).run(challenge_ciphertext);
    return (decision, AdaptiveBoundedRom.bad);
  }
}.

lemma adaptive_rom_query_identical_until_bad :
  equiv[AdaptiveBoundedRom.query ~ AdaptiveBoundedRom.query :
    AdaptiveBoundedRom.bad{1} = AdaptiveBoundedRom.bad{2} /\
    (!AdaptiveBoundedRom.bad{1} =>
      ={q, AdaptiveBoundedRom.base, AdaptiveBoundedRom.hidden,
        AdaptiveBoundedRom.fuel, AdaptiveBoundedRom.count,
        AdaptiveBoundedRom.trace} /\
      AdaptiveBoundedRom.pad{2} = !AdaptiveBoundedRom.pad{1}) ==>
    AdaptiveBoundedRom.bad{1} = AdaptiveBoundedRom.bad{2} /\
    (!AdaptiveBoundedRom.bad{1} =>
      ={res, AdaptiveBoundedRom.base, AdaptiveBoundedRom.hidden,
        AdaptiveBoundedRom.fuel, AdaptiveBoundedRom.count,
        AdaptiveBoundedRom.trace} /\
      AdaptiveBoundedRom.pad{2} = !AdaptiveBoundedRom.pad{1})].
proof.
  proc.
  auto; rewrite /pad_programmed_table; smt.
qed.

lemma adaptive_rom_init_invariants
  (base_table : rom_query -> rom_answer) (query_fuel : int)
  (hidden_query : rom_query) (hidden_pad : bool) :
  hoare[AdaptiveBoundedRom.init :
    arg = (base_table, query_fuel, hidden_query, hidden_pad) ==>
    0 <= AdaptiveBoundedRom.count /\
    AdaptiveBoundedRom.count <= AdaptiveBoundedRom.fuel /\
    AdaptiveBoundedRom.count = size AdaptiveBoundedRom.trace /\
    AdaptiveBoundedRom.bad =
      trace_queries AdaptiveBoundedRom.hidden AdaptiveBoundedRom.trace].
proof. by proc; auto; rewrite /trace_queries; smt(lez_maxl). qed.

lemma adaptive_rom_query_preserves_invariants :
  hoare[AdaptiveBoundedRom.query :
    0 <= AdaptiveBoundedRom.count /\
    AdaptiveBoundedRom.count <= AdaptiveBoundedRom.fuel /\
    AdaptiveBoundedRom.count = size AdaptiveBoundedRom.trace /\
    AdaptiveBoundedRom.bad =
      trace_queries AdaptiveBoundedRom.hidden AdaptiveBoundedRom.trace ==>
    0 <= AdaptiveBoundedRom.count /\
    AdaptiveBoundedRom.count <= AdaptiveBoundedRom.fuel /\
    AdaptiveBoundedRom.count = size AdaptiveBoundedRom.trace /\
    AdaptiveBoundedRom.bad =
      trace_queries AdaptiveBoundedRom.hidden AdaptiveBoundedRom.trace].
proof.
  proc; auto.
  rewrite /trace_queries /=.
  smt.
qed.

section AdaptiveSecurity.

declare module A <: ClassicalRomAdversary {-AdaptiveBoundedRom}.

(** EasyCrypt permits abstract adversaries to diverge.  The bounded protocol
    game, like SSProve's finite-distribution semantics, considers lossless
    adversaries. *)
declare axiom assumption_adaptive_adversary_run_lossless
  (O <: ClassicalRomOracle {-A}) :
  islossless O.query => islossless A(O).run.

lemma adaptive_bounded_rom_query_ll :
  islossless AdaptiveBoundedRom.query.
proof. by proc; auto. qed.

lemma adaptive_rom_games_identical_until_bad :
  equiv[AdaptiveRomGame(A).main ~ AdaptiveRomGame(A).main :
    ={glob A, base, fuel, hidden} /\
    challenge{1} = false /\ challenge{2} = true ==>
    res{1}.`2 = res{2}.`2 /\
    (!res{1}.`2 => res{1}.`1 = res{2}.`1)].
proof.
  proc.
  call (_ : AdaptiveBoundedRom.bad,
    ={AdaptiveBoundedRom.bad, AdaptiveBoundedRom.base,
      AdaptiveBoundedRom.hidden, AdaptiveBoundedRom.fuel,
      AdaptiveBoundedRom.count, AdaptiveBoundedRom.trace} /\
      AdaptiveBoundedRom.pad{2} = !AdaptiveBoundedRom.pad{1},
    ={AdaptiveBoundedRom.bad});
    1: apply assumption_adaptive_adversary_run_lossless.
  + proc.
    auto; rewrite /pad_programmed_table; smt.
  + move=> &m bad_m.
    proc; auto; smt.
  + move=> &m.
    proc; auto; smt.
  + inline AdaptiveBoundedRom.init.
    wp.
    rnd (fun b => !b).
    auto; smt.
qed.

(** The public bad flag is not a loose over-approximation: it is exactly the
    event that the accepted bounded trace contains the hidden query.  The
    same invariant also exposes the query-count budget. *)
lemma adaptive_rom_trace_and_bad_exact :
  hoare[AdaptiveRomGame(A).main :
    true ==>
    0 <= AdaptiveBoundedRom.count /\
    AdaptiveBoundedRom.count <= AdaptiveBoundedRom.fuel /\
    AdaptiveBoundedRom.count = size AdaptiveBoundedRom.trace /\
    AdaptiveBoundedRom.bad =
      trace_queries AdaptiveBoundedRom.hidden AdaptiveBoundedRom.trace].
proof.
  proc.
  call (_ :
    0 <= AdaptiveBoundedRom.count /\
    AdaptiveBoundedRom.count <= AdaptiveBoundedRom.fuel /\
    AdaptiveBoundedRom.count = size AdaptiveBoundedRom.trace /\
    AdaptiveBoundedRom.bad =
      trace_queries AdaptiveBoundedRom.hidden AdaptiveBoundedRom.trace).
  + exact adaptive_rom_query_preserves_invariants.
  + inline AdaptiveBoundedRom.init.
    auto; rewrite /trace_queries; smt(lez_maxl).
qed.

(** Fundamental-lemma capstone for an arbitrary bounded classical-ROM
    adversary: changing the hidden challenge bit can alter its decision only
    with probability at most that of querying the exact hidden input. *)
lemma adaptive_rom_advantage_bad_query_bound
  (base : rom_query -> rom_answer) (fuel : int) (hidden : rom_query) &m :
  `|Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m : res.`1] -
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m : res.`1]| <=
  Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m : res.`2].
proof.
  have -> :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m : res.`1] =
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m : res.`1] =
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m :
      res.`1 /\ !res.`2] =
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m :
      res.`1 /\ !res.`2].
  + byequiv adaptive_rom_games_identical_until_bad => /#.
  have bad_left :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m :
      res.`1 /\ res.`2] <=
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m : res.`2].
  + by rewrite Pr [mu_sub].
  have bad_right :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m :
      res.`1 /\ res.`2] <=
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m : res.`2].
  + by rewrite Pr [mu_sub].
  have bad_equal :
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, false) @ &m : res.`2] =
    Pr[AdaptiveRomGame(A).main(base, fuel, hidden, true) @ &m : res.`2].
  + byequiv adaptive_rom_games_identical_until_bad => /#.
  smt(mu_bounded).
qed.

(** The bounded protocol wrapper makes the four SSProve-supported cases
    explicit.  Active-quantum replacement is deliberately absent: its exact
    advantage-one game is [PqxdhGames.active_quantum_advantage_one]. *)
type protocol_supported_scenario = [
  ActiveClassicalForwardScenario |
  ActiveClassicalReplaceScenario |
  PassiveClassicalForwardScenario |
  PassiveQuantumForwardScenario
].

op protocol_supported_model (scenario : protocol_supported_scenario) :
  attacker_mode =
  with scenario = ActiveClassicalForwardScenario => active_classical
  with scenario = ActiveClassicalReplaceScenario => active_classical
  with scenario = PassiveClassicalForwardScenario => passive_classical
  with scenario = PassiveQuantumForwardScenario => passive_quantum.

op protocol_supported_action (scenario : protocol_supported_scenario) :
  network_action =
  with scenario = ActiveClassicalForwardScenario => Forward
  with scenario = ActiveClassicalReplaceScenario => Replace
  with scenario = PassiveClassicalForwardScenario => Forward
  with scenario = PassiveQuantumForwardScenario => Forward.

op protocol_scenario_accepted (scenario : protocol_supported_scenario) : bool =
  scenario <> ActiveClassicalReplaceScenario.

op active_classical_supported_scenario (action : network_action) :
  protocol_supported_scenario =
  with action = Forward => ActiveClassicalForwardScenario
  with action = Replace => ActiveClassicalReplaceScenario.

lemma protocol_supported_scenario_root_hidden
  (scenario : protocol_supported_scenario) :
  !accepted_input_recomputable (protocol_supported_model scenario)
    (protocol_supported_action scenario).
proof. by case: scenario. qed.

module ProtocolScenarioAdaptiveGame = {
  proc main(scenario : protocol_supported_scenario,
            base : rom_query -> rom_answer, fuel : int,
            initial_chain : bool, challenge : bool) : bool * bool = {
    var pad, challenge_ciphertext, decision, result;
    result <- (false, false);
    if (protocol_scenario_accepted scenario) {
      pad <$ dbool;
      challenge_ciphertext <- challenge <> pad;
      AdaptiveBoundedRom.init(base, fuel,
        protocol_hidden_pad_query initial_chain, pad);
      decision <@ A(AdaptiveBoundedRom).run(challenge_ciphertext);
      result <- (decision, AdaptiveBoundedRom.bad);
    }
    return result;
  }
}.

lemma protocol_forward_scenario_is_adaptive
  (scenario : protocol_supported_scenario)
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain challenge : bool) :
  protocol_scenario_accepted scenario =>
  equiv[ProtocolScenarioAdaptiveGame.main ~ AdaptiveRomGame(A).main :
    ={glob A} /\
    arg{1} = (scenario, base, fuel, initial_chain, challenge) /\
    arg{2} = (base, fuel, protocol_hidden_pad_query initial_chain, challenge)
    ==> ={res}].
proof.
  move=> accepted.
  proc.
  rcondt{1} 2; first auto.
  wp; sim.
  inline AdaptiveBoundedRom.init.
  auto.
qed.

lemma protocol_forward_scenario_probability
  (scenario : protocol_supported_scenario)
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain challenge : bool) (event : bool * bool -> bool) &m :
  protocol_scenario_accepted scenario =>
  Pr[ProtocolScenarioAdaptiveGame.main(
      scenario, base, fuel, initial_chain, challenge) @ &m : event res] =
  Pr[AdaptiveRomGame(A).main(
      base, fuel, protocol_hidden_pad_query initial_chain, challenge) @ &m :
      event res].
proof.
  move=> accepted.
  byequiv (protocol_forward_scenario_is_adaptive scenario base fuel
    initial_chain challenge accepted) => //.
qed.

lemma protocol_forward_scenario_adaptive_rom_bound
  (scenario : protocol_supported_scenario)
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  protocol_scenario_accepted scenario =>
  `|Pr[ProtocolScenarioAdaptiveGame.main(
        scenario, base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(
        scenario, base, fuel, initial_chain, true) @ &m : res.`1]| <=
  Pr[ProtocolScenarioAdaptiveGame.main(
      scenario, base, fuel, initial_chain, false) @ &m : res.`2].
proof.
  move=> accepted.
  have false_decision :
    Pr[ProtocolScenarioAdaptiveGame.main(
        scenario, base, fuel, initial_chain, false) @ &m : res.`1] =
    Pr[AdaptiveRomGame(A).main(base, fuel,
        protocol_hidden_pad_query initial_chain, false) @ &m : res.`1].
  + exact (protocol_forward_scenario_probability scenario base fuel
      initial_chain false (fun (r : bool * bool) => r.`1) &m accepted).
  have true_decision :
    Pr[ProtocolScenarioAdaptiveGame.main(
        scenario, base, fuel, initial_chain, true) @ &m : res.`1] =
    Pr[AdaptiveRomGame(A).main(base, fuel,
        protocol_hidden_pad_query initial_chain, true) @ &m : res.`1].
  + exact (protocol_forward_scenario_probability scenario base fuel
      initial_chain true (fun (r : bool * bool) => r.`1) &m accepted).
  have false_bad :
    Pr[ProtocolScenarioAdaptiveGame.main(
        scenario, base, fuel, initial_chain, false) @ &m : res.`2] =
    Pr[AdaptiveRomGame(A).main(base, fuel,
        protocol_hidden_pad_query initial_chain, false) @ &m : res.`2].
  + exact (protocol_forward_scenario_probability scenario base fuel
      initial_chain false (fun (r : bool * bool) => r.`2) &m accepted).
  rewrite false_decision true_decision false_bad.
  exact (adaptive_rom_advantage_bad_query_bound base fuel
    (protocol_hidden_pad_query initial_chain) &m).
qed.

lemma active_classical_forward_bounded_rom_confidentiality
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  `|Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalForwardScenario,
        base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalForwardScenario,
        base, fuel, initial_chain, true) @ &m : res.`1]| <=
  Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalForwardScenario,
      base, fuel, initial_chain, false) @ &m : res.`2].
proof.
  exact (protocol_forward_scenario_adaptive_rom_bound
    ActiveClassicalForwardScenario base fuel initial_chain &m _).
qed.

lemma passive_classical_forward_bounded_rom_confidentiality
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  `|Pr[ProtocolScenarioAdaptiveGame.main(PassiveClassicalForwardScenario,
        base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(PassiveClassicalForwardScenario,
        base, fuel, initial_chain, true) @ &m : res.`1]| <=
  Pr[ProtocolScenarioAdaptiveGame.main(PassiveClassicalForwardScenario,
      base, fuel, initial_chain, false) @ &m : res.`2].
proof.
  exact (protocol_forward_scenario_adaptive_rom_bound
    PassiveClassicalForwardScenario base fuel initial_chain &m _).
qed.

(** This is a passive-quantum capability label with classical oracle calls;
    it is not a QROM or QPT theorem. *)
lemma passive_quantum_classical_query_forward_confidentiality
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  `|Pr[ProtocolScenarioAdaptiveGame.main(PassiveQuantumForwardScenario,
        base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(PassiveQuantumForwardScenario,
        base, fuel, initial_chain, true) @ &m : res.`1]| <=
  Pr[ProtocolScenarioAdaptiveGame.main(PassiveQuantumForwardScenario,
      base, fuel, initial_chain, false) @ &m : res.`2].
proof.
  exact (protocol_forward_scenario_adaptive_rom_bound
    PassiveQuantumForwardScenario base fuel initial_chain &m _).
qed.

lemma active_classical_replace_fixed_failure_confidentiality
  (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  `|Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalReplaceScenario,
        base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalReplaceScenario,
        base, fuel, initial_chain, true) @ &m : res.`1]| = 0%r.
proof.
  have false_world :
    Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalReplaceScenario,
      base, fuel, initial_chain, false) @ &m : res.`1] = 0%r.
  + byphoare (_ :
      arg = (ActiveClassicalReplaceScenario, base, fuel,
        initial_chain, false) ==> _) => //=.
    hoare.
    proc.
    rcondf 2; auto; rewrite /protocol_scenario_accepted.
  have true_world :
    Pr[ProtocolScenarioAdaptiveGame.main(ActiveClassicalReplaceScenario,
      base, fuel, initial_chain, true) @ &m : res.`1] = 0%r.
  + byphoare (_ :
      arg = (ActiveClassicalReplaceScenario, base, fuel,
        initial_chain, true) ==> _) => //=.
    hoare.
    proc.
    rcondf 2; auto; rewrite /protocol_scenario_accepted.
  by rewrite false_world true_world; smt.
qed.

lemma active_classical_all_actions_bounded_rom_confidentiality
  (action : network_action) (base : rom_query -> rom_answer) (fuel : int)
  (initial_chain : bool) &m :
  `|Pr[ProtocolScenarioAdaptiveGame.main(
        active_classical_supported_scenario action,
        base, fuel, initial_chain, false) @ &m : res.`1] -
    Pr[ProtocolScenarioAdaptiveGame.main(
        active_classical_supported_scenario action,
        base, fuel, initial_chain, true) @ &m : res.`1]| <=
  Pr[ProtocolScenarioAdaptiveGame.main(
      active_classical_supported_scenario action,
      base, fuel, initial_chain, false) @ &m : res.`2].
proof.
  case: action.
  + exact (active_classical_forward_bounded_rom_confidentiality
      base fuel initial_chain &m).
  + rewrite active_classical_replace_fixed_failure_confidentiality.
    smt(mu_bounded).
qed.

end section AdaptiveSecurity.
