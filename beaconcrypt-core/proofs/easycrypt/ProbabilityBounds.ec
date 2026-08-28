(* SPDX-License-Identifier: 0BSD *)

(** Generic same-run probability algebra.  An experiment returns its left and
    right decisions together with a bad-event flag.  The experiment may be
    randomized and stateful; these lemmas use no losslessness assumption. *)

require import AllCore Real Distr StdOrder.
import RealOrder.

type paired_result = bool * bool * bool.

module type PairedExperiment = {
  proc run() : paired_result
}.

op decisions_mismatch (r : paired_result) : bool = (r.`1 <> r.`2).
op result_bad (r : paired_result) : bool = r.`3.

section SameRunBounds.
  declare module E <: PairedExperiment.

  lemma paired_decision_gap_le_mismatch_parts &m :
    `|Pr[E.run() @ &m : res.`1] - Pr[E.run() @ &m : res.`2]| <=
    maxr Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res]
         Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res].
  proof.
    have left_split : Pr[E.run() @ &m : res.`1] =
        Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res] +
        Pr[E.run() @ &m : res.`1 /\ !decisions_mismatch res]
      by rewrite Pr[mu_split (decisions_mismatch res)].
    have right_split : Pr[E.run() @ &m : res.`2] =
        Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res] +
        Pr[E.run() @ &m : res.`2 /\ !decisions_mismatch res]
      by rewrite Pr[mu_split (decisions_mismatch res)].
    have common_part : Pr[E.run() @ &m : res.`1 /\ !decisions_mismatch res] =
        Pr[E.run() @ &m : res.`2 /\ !decisions_mismatch res]
      by rewrite Pr[mu_eq] /decisions_mismatch; smt.
    have left_nonnegative :
      0%r <= Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res]
      by smt(mu_bounded).
    have right_nonnegative :
      0%r <= Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res]
      by smt(mu_bounded).
    have gap_identity :
      Pr[E.run() @ &m : res.`1] - Pr[E.run() @ &m : res.`2] =
      Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res] -
        Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res]
      by rewrite left_split right_split common_part; ring.
    rewrite gap_identity.
    exact (ler_norm_maxr
      (Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res])
      (Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res])
      left_nonnegative right_nonnegative).
  qed.

  lemma paired_decision_gap_le_mismatch &m :
    `|Pr[E.run() @ &m : res.`1] - Pr[E.run() @ &m : res.`2]| <=
    Pr[E.run() @ &m : decisions_mismatch res].
  proof.
    have parts := paired_decision_gap_le_mismatch_parts &m.
    have left_sub : Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res] <=
      Pr[E.run() @ &m : decisions_mismatch res] by rewrite Pr[mu_sub].
    have right_sub : Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res] <=
      Pr[E.run() @ &m : decisions_mismatch res] by rewrite Pr[mu_sub].
    have max_bound :
      maxr Pr[E.run() @ &m : res.`1 /\ decisions_mismatch res]
           Pr[E.run() @ &m : res.`2 /\ decisions_mismatch res] <=
      Pr[E.run() @ &m : decisions_mismatch res]
      by rewrite ler_maxrP left_sub right_sub.
    exact (ler_trans _ _ _ parts max_bound).
  qed.

  lemma paired_decision_gap_le_bad &m :
    (forall r, decisions_mismatch r => result_bad r) =>
    `|Pr[E.run() @ &m : res.`1] - Pr[E.run() @ &m : res.`2]| <=
    Pr[E.run() @ &m : result_bad res].
  proof.
    move=> mismatch_implies_bad.
    have mismatch_bound := paired_decision_gap_le_mismatch &m.
    have bad_sub :
      Pr[E.run() @ &m : decisions_mismatch res] <=
      Pr[E.run() @ &m : result_bad res]
      by rewrite Pr[mu_sub]; progress;
         apply mismatch_implies_bad; assumption.
    exact (ler_trans _ _ _ mismatch_bound bad_sub).
  qed.
end section SameRunBounds.
