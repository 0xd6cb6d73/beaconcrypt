(* SPDX-License-Identifier: 0BSD *)

(** Full-transcript, fuel-bounded adaptive classical-ROM CTX privacy hop.

    Queries contain all six Boolean transcript coordinates.  Only the hidden
    point fixes the public five-field tuple; an adversary may query every other
    transcript.  The base table is arbitrary, while [old] and [fresh] are iid
    uniform bits.  This is neither a QROM theorem nor an implementation proof. *)

require import AllCore Bool Int List Real Distr DBool.

type ctx_full_public = bool * bool * bool * bool * bool.
type ctx_full_query = bool * bool * bool * bool * bool * bool.
type ctx_full_table = ctx_full_query -> bool.
type ctx_full_trace = ctx_full_query list.

op ctx_full_secret (key : bool) (public : ctx_full_public) : ctx_full_query =
  (key, public.`1, public.`2, public.`3, public.`4, public.`5).

op ctx_full_table_set (base : ctx_full_table) (secret : ctx_full_query)
    (value : bool) (query : ctx_full_query) : bool =
  if query = secret then value else base query.

lemma ctx_full_table_set_at_secret base secret value :
  ctx_full_table_set base secret value secret = value.
proof. by rewrite /ctx_full_table_set. qed.

lemma ctx_full_table_set_away base secret value query :
  query <> secret =>
  ctx_full_table_set base secret value query = base query.
proof. by move=> ne; rewrite /ctx_full_table_set ne. qed.

op ctx_full_trace_queries (secret : ctx_full_query)
    (trace : ctx_full_trace) : bool = secret \in trace.

module type CtxFullClassicalOracle = {
  proc query(input : ctx_full_query) : bool
}.

module type CtxFullAdaptiveAdversary(O : CtxFullClassicalOracle) = {
  proc run(public : ctx_full_public, digest : bool) : bool
}.

module CtxFullBoundedOracle = {
  var base : ctx_full_table
  var hidden : ctx_full_query
  var hidden_answer : bool
  var fuel : int
  var count : int
  var trace : ctx_full_trace
  var bad : bool

  proc init(base_table : ctx_full_table, hidden_query : ctx_full_query,
            answer_at_hidden : bool, query_fuel : int) : unit = {
    base <- base_table;
    hidden <- hidden_query;
    hidden_answer <- answer_at_hidden;
    fuel <- max 0 query_fuel;
    count <- 0;
    trace <- [];
    bad <- false;
  }

  proc query(input : ctx_full_query) : bool = {
    var answer;
    answer <- false;
    if (count < fuel) {
      bad <- bad \/ input = hidden;
      answer <- ctx_full_table_set base hidden hidden_answer input;
      trace <- input :: trace;
      count <- count + 1;
    }
    return answer;
  }
}.

type ctx_full_world = [ TrueReal | ProgrammedReal | FreshIdeal ].
type ctx_full_result = bool * bool * int * ctx_full_trace.

op ctx_full_swap_coins (coins : bool * bool) : bool * bool =
  (coins.`2, coins.`1).

lemma ctx_full_swap_coins_involutive (coins : bool * bool) :
  ctx_full_swap_coins (ctx_full_swap_coins coins) = coins.
proof. by case coins=> coin1 coin2. qed.

module CtxFullAdaptiveGame(A : CtxFullAdaptiveAdversary) = {
  proc main(base : ctx_full_table, fuel : int, key : bool,
            public : ctx_full_public, world : ctx_full_world)
      : ctx_full_result = {
    var left_coin, right_coin, old, fresh, secret, public_digest;
    var answer_at_hidden, decision;
    left_coin <$ dbool;
    right_coin <$ dbool;
    old <- if world = TrueReal then right_coin else left_coin;
    fresh <- if world = TrueReal then left_coin else right_coin;
    secret <- ctx_full_secret key public;
    public_digest <- if world = TrueReal then old else fresh;
    answer_at_hidden <- if world = ProgrammedReal then fresh else old;
    CtxFullBoundedOracle.init(base, secret, answer_at_hidden, fuel);
    decision <@ A(CtxFullBoundedOracle).run(public, public_digest);
    return (decision, CtxFullBoundedOracle.bad, CtxFullBoundedOracle.count,
            CtxFullBoundedOracle.trace);
  }
}.

lemma ctx_full_query_preserves_exact_invariants :
  hoare[CtxFullBoundedOracle.query :
    0 <= CtxFullBoundedOracle.count /\
    CtxFullBoundedOracle.count <= CtxFullBoundedOracle.fuel /\
    CtxFullBoundedOracle.count = size CtxFullBoundedOracle.trace /\
    CtxFullBoundedOracle.bad = ctx_full_trace_queries
      CtxFullBoundedOracle.hidden CtxFullBoundedOracle.trace ==>
    0 <= CtxFullBoundedOracle.count /\
    CtxFullBoundedOracle.count <= CtxFullBoundedOracle.fuel /\
    CtxFullBoundedOracle.count = size CtxFullBoundedOracle.trace /\
    CtxFullBoundedOracle.bad = ctx_full_trace_queries
      CtxFullBoundedOracle.hidden CtxFullBoundedOracle.trace].
proof.
  proc; auto.
  rewrite /ctx_full_trace_queries /=.
  smt.
qed.

lemma ctx_full_query_identical_until_bad :
  equiv[CtxFullBoundedOracle.query ~ CtxFullBoundedOracle.query :
    CtxFullBoundedOracle.bad{1} = CtxFullBoundedOracle.bad{2} /\
    (!CtxFullBoundedOracle.bad{1} =>
      ={input, CtxFullBoundedOracle.base, CtxFullBoundedOracle.hidden,
        CtxFullBoundedOracle.fuel, CtxFullBoundedOracle.count,
        CtxFullBoundedOracle.trace}) ==>
    CtxFullBoundedOracle.bad{1} = CtxFullBoundedOracle.bad{2} /\
    (!CtxFullBoundedOracle.bad{1} =>
      ={res, CtxFullBoundedOracle.base, CtxFullBoundedOracle.hidden,
        CtxFullBoundedOracle.fuel, CtxFullBoundedOracle.count,
        CtxFullBoundedOracle.trace})].
proof.
  proc.
  auto; rewrite /ctx_full_table_set; smt.
qed.

section CtxFullAdaptivePrivacy.

declare module A <: CtxFullAdaptiveAdversary {-CtxFullBoundedOracle}.

declare axiom assumption_ctx_full_adversary_run_lossless
  (O <: CtxFullClassicalOracle {-A}) :
  islossless O.query => islossless A(O).run.

lemma ctx_full_bounded_query_lossless :
  islossless CtxFullBoundedOracle.query.
proof. by proc; auto. qed.

lemma ctx_full_programmed_ideal_identical_until_bad :
  equiv[CtxFullAdaptiveGame(A).main ~ CtxFullAdaptiveGame(A).main :
    ={glob A, base, fuel, key, public} /\
    world{1} = ProgrammedReal /\ world{2} = FreshIdeal ==>
    res{1}.`2 = res{2}.`2 /\
    (!res{1}.`2 => res{1}.`1 = res{2}.`1)].
proof.
  proc.
  call (_ : CtxFullBoundedOracle.bad,
    ={CtxFullBoundedOracle.bad, CtxFullBoundedOracle.base,
      CtxFullBoundedOracle.hidden, CtxFullBoundedOracle.fuel,
      CtxFullBoundedOracle.count, CtxFullBoundedOracle.trace},
    ={CtxFullBoundedOracle.bad});
    1: apply assumption_ctx_full_adversary_run_lossless.
  + proc.
    auto; rewrite /ctx_full_table_set; smt.
  + move=> &m bad_m; proc; auto; smt.
  + move=> &m; proc; auto; smt.
  + inline CtxFullBoundedOracle.init.
    wp.
    rnd; rnd.
    auto; smt.
qed.

lemma ctx_full_trace_count_bad_exact
  (base_table : ctx_full_table) (query_fuel : int) (key : bool)
  (public : ctx_full_public) (world : ctx_full_world) :
  hoare[CtxFullAdaptiveGame(A).main :
    arg = (base_table, query_fuel, key, public, world) ==>
    0 <= res.`3 /\ res.`3 <= max 0 query_fuel /\
    res.`3 = size res.`4 /\
    res.`2 = ctx_full_trace_queries (ctx_full_secret key public) res.`4].
proof.
  proc.
  call (_ :
    0 <= CtxFullBoundedOracle.count /\
    CtxFullBoundedOracle.count <= CtxFullBoundedOracle.fuel /\
    CtxFullBoundedOracle.count = size CtxFullBoundedOracle.trace /\
    CtxFullBoundedOracle.bad = ctx_full_trace_queries
      CtxFullBoundedOracle.hidden CtxFullBoundedOracle.trace).
  + exact ctx_full_query_preserves_exact_invariants.
  + inline CtxFullBoundedOracle.init.
    auto; rewrite /ctx_full_trace_queries; smt(lez_maxl).
qed.

lemma ctx_full_programmed_ideal_absolute_gap
  (base : ctx_full_table) (fuel : int) (key : bool)
  (public : ctx_full_public) &m :
  `|Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
       ProgrammedReal) @ &m : res.`1] -
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
       FreshIdeal) @ &m : res.`1]| <=
  Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
       FreshIdeal) @ &m : res.`2].
proof.
  have -> :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m : res.`1] =
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr[mu_eq] => /#.
  rewrite Pr[mu_or].
  have -> /= :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m : res.`1] =
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr[mu_eq] => /#.
  rewrite Pr[mu_or].
  have -> /= :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m : res.`1 /\ !res.`2] =
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m : res.`1 /\ !res.`2].
  + byequiv ctx_full_programmed_ideal_identical_until_bad => /#.
  have bad_left :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m : res.`1 /\ res.`2] <=
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m : res.`2]
    by rewrite Pr[mu_sub].
  have bad_right :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m : res.`1 /\ res.`2] <=
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m : res.`2]
    by rewrite Pr[mu_sub].
  have bad_equal :
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      ProgrammedReal) @ &m : res.`2] =
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
      FreshIdeal) @ &m : res.`2].
  + byequiv ctx_full_programmed_ideal_identical_until_bad => /#.
  smt(mu_bounded).
qed.

(** Swapping the iid [old] and [fresh] draws maps the true table/digest pair
    exactly to the programmed table/digest pair. *)
lemma ctx_full_true_programmed_distribution :
  equiv[CtxFullAdaptiveGame(A).main ~ CtxFullAdaptiveGame(A).main :
    ={glob A, base, fuel, key, public} /\
    world{1} = TrueReal /\ world{2} = ProgrammedReal ==> ={res}].
proof.
  proc.
  call (_ :
    ={CtxFullBoundedOracle.bad, CtxFullBoundedOracle.base,
      CtxFullBoundedOracle.hidden, CtxFullBoundedOracle.hidden_answer,
      CtxFullBoundedOracle.fuel, CtxFullBoundedOracle.count,
      CtxFullBoundedOracle.trace}).
  + proc; auto.
  inline CtxFullBoundedOracle.init.
  wp.
  rnd; rnd.
  auto.
qed.

lemma ctx_full_true_programmed_probability
  (base : ctx_full_table) (fuel : int) (key : bool)
  (public : ctx_full_public) &m :
  Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public, TrueReal) @ &m :
       res.`1] =
  Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public,
       ProgrammedReal) @ &m : res.`1].
proof. byequiv ctx_full_true_programmed_distribution => //. qed.

lemma ctx_full_true_ideal_absolute_gap
  (base : ctx_full_table) (fuel : int) (key : bool)
  (public : ctx_full_public) &m :
  `|Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public, TrueReal) @ &m :
       res.`1] -
    Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public, FreshIdeal) @ &m :
       res.`1]| <=
  Pr[CtxFullAdaptiveGame(A).main(base, fuel, key, public, FreshIdeal) @ &m :
       res.`2].
proof.
  rewrite (ctx_full_true_programmed_probability base fuel key public &m).
  exact (ctx_full_programmed_ideal_absolute_gap base fuel key public &m).
qed.

(** The parity-facing wrapper samples the hidden key internally.  The key is
    used only to form the six-coordinate hidden query and is not passed to A. *)
module CtxHiddenUniformKeyGame(A : CtxFullAdaptiveAdversary) = {
  proc main(base : ctx_full_table, fuel : int, public : ctx_full_public,
            world : ctx_full_world) : ctx_full_result = {
    var key, result;
    key <$ dbool;
    result <@ CtxFullAdaptiveGame(A).main(base, fuel, key, public, world);
    return result;
  }
}.

lemma ctx_hidden_programmed_ideal_identical_until_bad :
  equiv[CtxHiddenUniformKeyGame(A).main ~
        CtxHiddenUniformKeyGame(A).main :
    ={glob A, base, fuel, public} /\
    world{1} = ProgrammedReal /\ world{2} = FreshIdeal ==>
    res{1}.`2 = res{2}.`2 /\
    (!res{1}.`2 => res{1}.`1 = res{2}.`1)].
proof.
  proc.
  call ctx_full_programmed_ideal_identical_until_bad.
  rnd.
  auto.
qed.

lemma ctx_hidden_true_programmed_distribution :
  equiv[CtxHiddenUniformKeyGame(A).main ~
        CtxHiddenUniformKeyGame(A).main :
    ={glob A, base, fuel, public} /\
    world{1} = TrueReal /\ world{2} = ProgrammedReal ==> ={res}].
proof.
  proc.
  call ctx_full_true_programmed_distribution.
  rnd.
  auto.
qed.

lemma ctx_hidden_programmed_ideal_absolute_gap
  (base : ctx_full_table) (fuel : int) (public : ctx_full_public) &m :
  `|Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
       ProgrammedReal) @ &m : res.`1] -
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
       FreshIdeal) @ &m : res.`1]| <=
  Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
       FreshIdeal) @ &m : res.`2].
proof.
  have -> :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m : res.`1] =
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr[mu_eq] => /#.
  rewrite Pr[mu_or].
  have -> /= :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m : res.`1] =
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m :
      (res.`1 /\ res.`2) \/ (res.`1 /\ !res.`2)].
  + by rewrite Pr[mu_eq] => /#.
  rewrite Pr[mu_or].
  have -> /= :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m :
      (res.`1 /\ res.`2) /\ res.`1 /\ !res.`2] = 0%r.
  + byphoare (_ : _ ==> false) => // /#.
  have -> :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m : res.`1 /\ !res.`2] =
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m : res.`1 /\ !res.`2].
  + byequiv ctx_hidden_programmed_ideal_identical_until_bad => /#.
  have bad_left :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m : res.`1 /\ res.`2] <=
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m : res.`2]
    by rewrite Pr[mu_sub].
  have bad_right :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m : res.`1 /\ res.`2] <=
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m : res.`2]
    by rewrite Pr[mu_sub].
  have bad_equal :
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      ProgrammedReal) @ &m : res.`2] =
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
      FreshIdeal) @ &m : res.`2].
  + byequiv ctx_hidden_programmed_ideal_identical_until_bad => /#.
  smt(mu_bounded).
qed.

lemma ctx_hidden_true_programmed_probability
  (base : ctx_full_table) (fuel : int) (public : ctx_full_public) &m :
  Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public, TrueReal) @ &m :
       res.`1] =
  Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public,
       ProgrammedReal) @ &m : res.`1].
proof. byequiv ctx_hidden_true_programmed_distribution => //. qed.

(** End-to-end hidden-uniform-key classical-ROM CTX privacy hop. *)
lemma ctx_hidden_uniform_key_true_real_privacy_bound
  (base : ctx_full_table) (fuel : int) (public : ctx_full_public) &m :
  `|Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public, TrueReal) @ &m :
       res.`1] -
    Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public, FreshIdeal) @ &m :
       res.`1]| <=
  Pr[CtxHiddenUniformKeyGame(A).main(base, fuel, public, FreshIdeal) @ &m :
       res.`2].
proof.
  rewrite (ctx_hidden_true_programmed_probability base fuel public &m).
  exact (ctx_hidden_programmed_ideal_absolute_gap base fuel public &m).
qed.

end section CtxFullAdaptivePrivacy.

(** Scope: one finite CTX programming hop with adaptive classical queries and
    an explicit fuel bound; no QROM/QPT or production-width claim. *)
