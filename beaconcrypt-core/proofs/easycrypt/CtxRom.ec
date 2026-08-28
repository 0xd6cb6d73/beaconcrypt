(* SPDX-License-Identifier: 0BSD *)

(** Bounded classical-ROM capstones for CTX.

    A trace contains only public oracle-query inputs.  The hidden table remains
    a function and is never returned.  These are deterministic same-run
    reductions; numerical ROM collision bounds and QROM lifting are separate. *)

require import AllCore Int List Real Distr StdOrder.
require import Ctx.

import RealOrder.

type ctx_rom = transcript -> digest.
type ctx_query_trace = transcript list.

op ctx_trace_queries (secret : transcript) (trace : ctx_query_trace) : bool =
  secret \in trace.

op ctx_programmed_answer (table : ctx_rom) (secret : transcript)
                         (fresh : digest) (query : transcript) : digest =
  if query = secret then fresh else table query.

lemma ctx_programmed_answer_at_secret
  (table : ctx_rom) (secret : transcript) (fresh : digest) :
  ctx_programmed_answer table secret fresh secret = fresh.
proof. by rewrite /ctx_programmed_answer. qed.

lemma ctx_programmed_answer_away_from_secret
  (table : ctx_rom) (secret query : transcript) (fresh : digest) :
  query <> secret =>
  ctx_programmed_answer table secret fresh query = table query.
proof. by move=> differs; rewrite /ctx_programmed_answer differs. qed.

(** A same-run answer mismatch is possible only at the programmed query. *)
lemma ctx_privacy_answer_mismatch_implies_bad_query
  (table : ctx_rom) (secret query : transcript) (fresh : digest) :
  ctx_programmed_answer table secret fresh query <> table query =>
  query = secret.
proof.
  move=> mismatch.
  case (query = secret)=> // differs.
  move: mismatch.
  by rewrite (ctx_programmed_answer_away_from_secret
    table secret query fresh differs).
qed.

(** Pointwise classical-ROM privacy hop.  If one of the answers visible in a
    bounded execution differs between programmed-real and fresh-ideal worlds,
    that execution contains the hidden transcript query. *)
lemma ctx_privacy_game_hop_bad_query_bound
  (table : ctx_rom) (secret : transcript) (fresh : digest)
  (trace : ctx_query_trace) :
  (exists query,
    query \in trace /\
    ctx_programmed_answer table secret fresh query <> table query) =>
  ctx_trace_queries secret trace.
proof.
  move=> [query [in_trace mismatch]].
  rewrite /ctx_trace_queries.
  have equal_query : query = secret.
  + exact (ctx_privacy_answer_mismatch_implies_bad_query
      table secret query fresh mismatch).
  by rewrite -equal_query.
qed.

type ctx_verified_binding =
  (protected_payload * explanation * explanation) * ctx_query_trace.

op ctx_binding_outcome (verified : ctx_verified_binding) = verified.`1.
op ctx_binding_trace (verified : ctx_verified_binding) = verified.`2.

op ctx_extract_binding_collision (verified : ctx_verified_binding) : bool =
  ctx_collision_event (ctx_binding_outcome verified).

(** Hidden-ROM binding extraction: the public observation supplies only the
    returned attempt and trace; the extracted collision uses the two concrete
    verifier transcripts already determined by that attempt. *)
lemma ctx_hidden_rom_binding_extraction
  (verified : ctx_verified_binding) :
  ctx_binding_event (ctx_binding_outcome verified) =>
  ctx_extract_binding_collision verified.
proof.
  rewrite /ctx_extract_binding_collision.
  exact (ctx_binding_event_implies_collision_event
    (ctx_binding_outcome verified)).
qed.

op ctx_verifier_trace (outcome : protected_payload * explanation * explanation)
                      (adversary_trace : ctx_query_trace) : ctx_query_trace =
  adversary_trace ++
    [ctx_transcript (payload_tag outcome.`1) outcome.`2;
     ctx_transcript (payload_tag outcome.`1) outcome.`3].

(** The verifier appends exactly two ROM queries. *)
lemma ctx_hidden_binding_trace_size_bound
  (fuel : int) (outcome : protected_payload * explanation * explanation)
  (adversary_trace : ctx_query_trace) :
  0 <= fuel =>
  size adversary_trace <= fuel =>
  size (ctx_verifier_trace outcome adversary_trace) <= fuel + 2.
proof.
  move=> ge0 bounded.
  rewrite /ctx_verifier_trace size_cat /=.
  smt.
qed.

module type CtxRomBinder = {
  proc run() : ctx_verified_binding
}.

module CtxRomBindingEvents(A : CtxRomBinder) = {
  proc main() : bool * bool = {
    var verified, binding, collision;
    verified <@ A.run();
    binding <- ctx_binding_event (ctx_binding_outcome verified);
    collision <- ctx_extract_binding_collision verified;
    return (binding, collision);
  }
}.

(** Probability lift of the same-run extractor for an arbitrary randomized
    binder.  Both events are computed from one call and one observation. *)
lemma ctx_hidden_rom_binding_probability_bound
  (A <: CtxRomBinder) &m :
  Pr[CtxRomBindingEvents(A).main() @ &m : res.`1] <=
  Pr[CtxRomBindingEvents(A).main() @ &m : res.`2].
proof.
  byequiv (_ : ={glob A} ==> res{1}.`1 => res{2}.`2) => //.
  proc; wp.
  call (_ : true).
  auto; smt(ctx_hidden_rom_binding_extraction).
qed.

type ctx_privacy_strategy = transcript * (digest -> bool).

module type CtxPrivacyAdversary = {
  proc run() : ctx_privacy_strategy
}.

(** A randomized one-query adversary chooses its query and decision function
    before seeing the answer.  The game evaluates that same strategy in the
    programmed-real and fresh-ideal worlds and records the bad query. *)
module CtxPrivacyEvents(A : CtxPrivacyAdversary) = {
  proc main(table : ctx_rom, secret : transcript, fresh : digest)
      : bool * bool * bool = {
    var strategy, query, decide, real_answer, ideal_answer;
    strategy <@ A.run();
    query <- strategy.`1;
    decide <- strategy.`2;
    real_answer <- ctx_programmed_answer table secret fresh query;
    ideal_answer <- table query;
    return (decide real_answer, decide ideal_answer, query = secret);
  }
}.

(** Coupled probability form of the classical fundamental lemma.  No
    identical-until-bad premise is assumed: away from the secret query the two
    answers reduce to the same value. *)
lemma ctx_privacy_mismatch_probability_bound
  (A <: CtxPrivacyAdversary) (table : ctx_rom)
  (secret : transcript) (fresh : digest) &m :
  Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
       res.`1 <> res.`2] <=
  Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`3].
proof.
  byequiv (_ : ={glob A, table, secret, fresh} ==>
    (res{1}.`1 <> res{1}.`2) => res{2}.`3) => //.
  proc; wp.
  call (_ : true).
  auto; smt(ctx_privacy_answer_mismatch_implies_bad_query).
qed.

(** For two decisions returned by the same randomized execution, their
    marginal probability gap is bounded by the probability that they differ.
    This is probability algebra only and does not require losslessness. *)
lemma ctx_privacy_decision_gap_le_mismatch
  (A <: CtxPrivacyAdversary) (table : ctx_rom)
  (secret : transcript) (fresh : digest) &m :
  `|Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`1] -
     Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`2]| <=
  Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
       res.`1 <> res.`2].
proof.
  have left_split :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`1] =
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ res.`1 <> res.`2] +
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ !(res.`1 <> res.`2)]
    by rewrite Pr[mu_split (res.`1 <> res.`2)].
  have right_split :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`2] =
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ res.`1 <> res.`2] +
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ !(res.`1 <> res.`2)]
    by rewrite Pr[mu_split (res.`1 <> res.`2)].
  have common_part :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ !(res.`1 <> res.`2)] =
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ !(res.`1 <> res.`2)]
    by rewrite Pr[mu_eq]; smt.
  have left_nonnegative : 0%r <=
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ res.`1 <> res.`2]
    by smt(mu_bounded).
  have right_nonnegative : 0%r <=
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ res.`1 <> res.`2]
    by smt(mu_bounded).
  have gap_identity :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`1] -
      Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`2] =
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ res.`1 <> res.`2] -
      Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ res.`1 <> res.`2]
    by rewrite left_split right_split common_part; ring.
  rewrite gap_identity.
  apply (ler_trans
    (maxr
      Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
           res.`1 /\ res.`1 <> res.`2]
      Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
           res.`2 /\ res.`1 <> res.`2])).
  + exact (ler_norm_maxr
      (Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
           res.`1 /\ res.`1 <> res.`2])
      (Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
           res.`2 /\ res.`1 <> res.`2])
      left_nonnegative right_nonnegative).
  have left_sub :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 /\ res.`1 <> res.`2] <=
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 <> res.`2]
    by rewrite Pr[mu_sub].
  have right_sub :
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`2 /\ res.`1 <> res.`2] <=
    Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m :
         res.`1 <> res.`2]
    by rewrite Pr[mu_sub].
  by rewrite ler_maxrP left_sub right_sub.
qed.

(** Absolute privacy advantage of the single coupled execution.  The only
    possible contribution to the marginal gap is the secret-query event. *)
lemma ctx_privacy_absolute_advantage_bound
  (A <: CtxPrivacyAdversary) (table : ctx_rom)
  (secret : transcript) (fresh : digest) &m :
  `|Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`1] -
     Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`2]| <=
  Pr[CtxPrivacyEvents(A).main(table, secret, fresh) @ &m : res.`3].
proof.
  exact (ler_trans _ _ _
    (ctx_privacy_decision_gap_le_mismatch A table secret fresh &m)
    (ctx_privacy_mismatch_probability_bound A table secret fresh &m)).
qed.
