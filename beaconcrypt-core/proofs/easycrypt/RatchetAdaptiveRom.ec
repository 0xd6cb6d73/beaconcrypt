(* SPDX-License-Identifier: 0BSD *)

(** Fuel-bounded adaptive classical-ROM game for one erased ratchet hop.

    The adversary receives the complete public view
    [(next_chain, ciphertext, nonce)] and may adaptively query a classical ROM.
    The programmed point is the domain-separated erased-chain input.  This is
    not a QROM theorem and does not establish implementation memory erasure. *)

require import AllCore Bool Int List Real Distr DBool.
require import RatchetForward.

type ratchet_rom_query = bool * bool.
type ratchet_rom_trace = ratchet_rom_query list.

op ratchet_rom_domain : bool = ratchet_step_domain.
op unrelated_rom_domain : bool = ratchet_other_domain.

lemma ratchet_rom_domain_separated :
  ratchet_rom_domain <> unrelated_rom_domain.
proof.
  rewrite /ratchet_rom_domain /unrelated_rom_domain.
  exact ratchet_domains_are_disjoint.
qed.

op erased_chain_query (erased_chain : bool) : ratchet_rom_query =
  (ratchet_rom_domain, erased_chain).

op ratchet_trace_queries (hidden : ratchet_rom_query)
    (trace : ratchet_rom_trace) : bool = hidden \in trace.

op ratchet_programmed_table (base : ratchet_rom_query -> bool)
    (hidden : ratchet_rom_query) (pad : bool)
    (q : ratchet_rom_query) : bool =
  if q = hidden then pad else base q.

lemma ratchet_programmed_table_away base hidden pad q :
  q <> hidden => ratchet_programmed_table base hidden pad q = base q.
proof. by move=> ne; rewrite /ratchet_programmed_table ne. qed.

lemma ratchet_programmed_table_at_hidden base hidden pad :
  ratchet_programmed_table base hidden pad hidden = pad.
proof. by rewrite /ratchet_programmed_table. qed.

module type RatchetClassicalRomOracle = {
  proc query(q : ratchet_rom_query) : bool
}.

module type RatchetAdaptiveAdversary(O : RatchetClassicalRomOracle) = {
  proc run(view : ratchet_public_view) : bool
}.

module RatchetBoundedRom = {
  var base : ratchet_rom_query -> bool
  var hidden : ratchet_rom_query
  var pad : bool
  var fuel : int
  var count : int
  var trace : ratchet_rom_trace
  var bad : bool

  proc init(base_table : ratchet_rom_query -> bool, query_fuel : int,
            hidden_query : ratchet_rom_query, hidden_pad : bool) : unit = {
    base <- base_table;
    hidden <- hidden_query;
    pad <- hidden_pad;
    fuel <- max 0 query_fuel;
    count <- 0;
    trace <- [];
    bad <- false;
  }

  proc query(q : ratchet_rom_query) : bool = {
    var answer;
    answer <- false;
    if (count < fuel) {
      bad <- bad \/ q = hidden;
      answer <- ratchet_programmed_table base hidden pad q;
      trace <- q :: trace;
      count <- count + 1;
    }
    return answer;
  }
}.

type ratchet_adaptive_result = bool * bool * int * ratchet_rom_trace.

module RatchetAdaptiveRomGame(A : RatchetAdaptiveAdversary) = {
  proc main(base : ratchet_rom_query -> bool, fuel : int,
            erased_chain : bool, challenge : bool) : ratchet_adaptive_result = {
    var pad, next_chain, nonce, view, decision;
    nonce <$ dbool;
    next_chain <$ dbool;
    pad <$ dbool;
    view <- (next_chain, bit_xor challenge pad, nonce);
    RatchetBoundedRom.init(base, fuel, erased_chain_query erased_chain, pad);
    decision <@ A(RatchetBoundedRom).run(view);
    return (decision, RatchetBoundedRom.bad, RatchetBoundedRom.count,
            RatchetBoundedRom.trace);
  }
}.

lemma ratchet_bounded_query_identical_until_bad :
  equiv[RatchetBoundedRom.query ~ RatchetBoundedRom.query :
    RatchetBoundedRom.bad{1} = RatchetBoundedRom.bad{2} /\
    (!RatchetBoundedRom.bad{1} =>
      ={q, RatchetBoundedRom.base, RatchetBoundedRom.hidden,
        RatchetBoundedRom.fuel, RatchetBoundedRom.count,
        RatchetBoundedRom.trace} /\
      RatchetBoundedRom.pad{2} = !RatchetBoundedRom.pad{1}) ==>
    RatchetBoundedRom.bad{1} = RatchetBoundedRom.bad{2} /\
    (!RatchetBoundedRom.bad{1} =>
      ={res, RatchetBoundedRom.base, RatchetBoundedRom.hidden,
        RatchetBoundedRom.fuel, RatchetBoundedRom.count,
        RatchetBoundedRom.trace} /\
      RatchetBoundedRom.pad{2} = !RatchetBoundedRom.pad{1})].
proof.
  proc.
  auto; rewrite /ratchet_programmed_table; smt.
qed.

lemma ratchet_bounded_rom_init_invariants base fuel hidden pad :
  hoare[RatchetBoundedRom.init : arg = (base, fuel, hidden, pad) ==>
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace].
proof. by proc; auto; rewrite /ratchet_trace_queries; smt(lez_maxl). qed.

lemma ratchet_bounded_rom_query_preserves_invariants :
  hoare[RatchetBoundedRom.query :
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace ==>
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace].
proof.
  proc; auto.
  rewrite /ratchet_trace_queries /=.
  smt.
qed.

lemma ratchet_bounded_rom_bad_is_sticky :
  hoare[RatchetBoundedRom.query : RatchetBoundedRom.bad ==>
    RatchetBoundedRom.bad].
proof. by proc; auto; smt. qed.

section RatchetAdaptiveSecurity.

declare module A <: RatchetAdaptiveAdversary {-RatchetBoundedRom}.

(** Abstract EasyCrypt modules may diverge, so the arbitrary adaptive
    adversary is explicitly restricted to be lossless when its oracle is. *)
declare axiom assumption_ratchet_adversary_run_lossless
  (O <: RatchetClassicalRomOracle {-A}) :
  islossless O.query => islossless A(O).run.

lemma ratchet_bounded_rom_query_lossless :
  islossless RatchetBoundedRom.query.
proof. by proc; auto. qed.

lemma ratchet_adaptive_games_identical_until_bad :
  equiv[RatchetAdaptiveRomGame(A).main ~ RatchetAdaptiveRomGame(A).main :
    ={glob A, base, fuel, erased_chain} /\
    challenge{1} = false /\ challenge{2} = true ==>
    res{1}.`2 = res{2}.`2 /\
    (!res{1}.`2 => res{1}.`1 = res{2}.`1)].
proof.
  proc.
  call (_ : RatchetBoundedRom.bad,
    ={RatchetBoundedRom.bad, RatchetBoundedRom.base,
      RatchetBoundedRom.hidden, RatchetBoundedRom.fuel,
      RatchetBoundedRom.count, RatchetBoundedRom.trace} /\
      RatchetBoundedRom.pad{2} = !RatchetBoundedRom.pad{1},
    ={RatchetBoundedRom.bad});
    1: apply assumption_ratchet_adversary_run_lossless.
  + proc.
    auto; rewrite /ratchet_programmed_table; smt.
  + move=> &m bad_m.
    proc; auto; smt.
  + move=> &m.
    proc; auto; smt.
  + inline RatchetBoundedRom.init.
    wp.
    rnd (fun b => !b).
    rnd; rnd.
    auto; rewrite /bit_xor; smt.
qed.

(** The bad flag is exactly membership of the hidden, domain-separated erased
    chain query in the accepted trace; count is exact and fuel-bounded. *)
lemma ratchet_adaptive_trace_count_and_bad_exact :
  hoare[RatchetAdaptiveRomGame(A).main : true ==>
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace /\
    res.`2 = RatchetBoundedRom.bad /\ res.`3 = RatchetBoundedRom.count /\
    res.`4 = RatchetBoundedRom.trace].
proof.
  proc.
  call (_ :
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace).
  + exact ratchet_bounded_rom_query_preserves_invariants.
  + inline RatchetBoundedRom.init.
    auto; rewrite /ratchet_trace_queries; smt(lez_maxl).
qed.

(** Returned audit data states the exact hidden-query event and the exact
    accepted-query budget without exposing the oracle table or erased pad. *)
lemma ratchet_adaptive_returned_trace_bound
  (base_table : ratchet_rom_query -> bool) (query_fuel : int)
  (erased_chain : bool) (challenge : bool) :
  hoare[RatchetAdaptiveRomGame(A).main :
    arg = (base_table, query_fuel, erased_chain, challenge) ==>
    0 <= res.`3 /\ res.`3 <= max 0 query_fuel /\
    res.`3 = size res.`4 /\
    res.`2 = ratchet_trace_queries
      (erased_chain_query erased_chain) res.`4].
proof.
  proc.
  call (_ :
    0 <= RatchetBoundedRom.count /\
    RatchetBoundedRom.count <= RatchetBoundedRom.fuel /\
    RatchetBoundedRom.count = size RatchetBoundedRom.trace /\
    RatchetBoundedRom.bad =
      ratchet_trace_queries RatchetBoundedRom.hidden RatchetBoundedRom.trace).
  + exact ratchet_bounded_rom_query_preserves_invariants.
  + inline RatchetBoundedRom.init.
    auto; rewrite /ratchet_trace_queries; smt(lez_maxl).
qed.

(** Absolute distinguishing advantage is bounded by the exact probability of
    querying the hidden erased-chain point in the false-challenge execution. *)
lemma ratchet_adaptive_advantage_hidden_query_bound
  (base : ratchet_rom_query -> bool) (fuel : int)
  (erased_chain : bool) &m :
  `|Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
       res.`1] -
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
       res.`1]| <=
  Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
       res.`2].
proof.
  have -> :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      res.`1] =
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      res.`1] =
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr [mu_eq] => /#.
  rewrite Pr [mu_or].
  have -> /= :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      res.`1 /\ !res.`2] =
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      res.`1 /\ !res.`2].
  + byequiv ratchet_adaptive_games_identical_until_bad => /#.
  have bad_left :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      res.`1 /\ res.`2] <=
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      res.`2].
  + by rewrite Pr [mu_sub].
  have bad_right :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      res.`1 /\ res.`2] <=
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      res.`2].
  + by rewrite Pr [mu_sub].
  have bad_equal :
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, false) @ &m :
      res.`2] =
    Pr[RatchetAdaptiveRomGame(A).main(base, fuel, erased_chain, true) @ &m :
      res.`2].
  + byequiv ratchet_adaptive_games_identical_until_bad => /#.
  smt(mu_bounded).
qed.

end section RatchetAdaptiveSecurity.

(** Scope boundary: one erased transition, bounded classical ROM queries, and
    abstract lossless adversaries only; no QROM/QPT or physical-erasure claim. *)
