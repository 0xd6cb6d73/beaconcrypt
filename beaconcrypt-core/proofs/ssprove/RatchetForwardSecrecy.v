(* SPDX-License-Identifier: 0BSD *)

(** A finite, bounded classical-ROM forward-secrecy hop for one erased symmetric-ratchet step.

    The challenger retains a hidden prior chain atom and a complete ideal-oracle table. It derives the prior record key, the compromised next chain, and the nonce from distinct output slots of the symmetric-ratchet answer, encrypts one challenge bit with the prior record key, and erases the prior chain and record key from the attacker view. A deterministic adaptive attacker receives only the next chain, ciphertext, and nonce plus bounded classical oracle access.

    The proof couples the two challenge games by flipping only the prior record-key slot. The next-chain and nonce slots, including the compromised current chain, remain unchanged. Any distinguishing mismatch therefore implies that the attacker queried the exact erased prior-chain input. One-bit atoms make this a structural bad-event theorem rather than a numerical production bound. It is not a QROM theorem, does not cover superposition queries, and deliberately says nothing about persistence, rollback, primitive correctness, or implementation correctness. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum order eqtype choice fintype finfun seq all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom.

Import Num.Theory.
Import Order.POrderTheory.
Import GRing.Theory.

Local Open Scope ring_scope.

(** The first query bit is handwritten domain bookkeeping. [false] models the symmetric-ratchet label and [true] represents only a genuinely distinct production label, such as the PQXDH root label. It must not be read as separating initial from per-record symmetric expansion, which use the same production label. *)
Definition ratchet_rom_query := (bool * bool)%type.
Definition ratchet_rom_answer := (bool * (bool * bool))%type.
Definition ratchet_rom_table := rom_table ratchet_rom_query ratchet_rom_answer.
Definition ratchet_rom_trace := rom_trace ratchet_rom_query ratchet_rom_answer.

Definition ratchet_step_query (chain : bool) : ratchet_rom_query :=
  (false, chain).

Definition ratchet_other_domain_query (input : bool) : ratchet_rom_query :=
  (true, input).

Lemma ratchet_domains_are_disjoint (chain input : bool) :
  ratchet_step_query chain != ratchet_other_domain_query input.
Proof. reflexivity. Qed.

(** These three projections mirror the record-key, next-chain, and nonce slots of one symmetric-ratchet expansion. *)
Definition ratchet_message_key
    (table : ratchet_rom_table) (chain : bool) : bool :=
  (table (ratchet_step_query chain)).1.

Definition ratchet_next_chain
    (table : ratchet_rom_table) (chain : bool) : bool :=
  (table (ratchet_step_query chain)).2.1.

Definition ratchet_nonce
    (table : ratchet_rom_table) (chain : bool) : bool :=
  (table (ratchet_step_query chain)).2.2.

Definition ratchet_flip_message_answer
    (answer : ratchet_rom_answer) : ratchet_rom_answer :=
  (negb answer.1, answer.2).

Definition ratchet_flip_erased_message_key
    (erased_chain : bool)
    (table : ratchet_rom_table) : ratchet_rom_table :=
  [ffun query =>
    if query == ratchet_step_query erased_chain
    then ratchet_flip_message_answer (table query)
    else table query].

Lemma ratchet_flip_at_erased_query
    (erased_chain : bool) (table : ratchet_rom_table) :
  ratchet_flip_erased_message_key erased_chain table
      (ratchet_step_query erased_chain) =
  ratchet_flip_message_answer (table (ratchet_step_query erased_chain)).
Proof. by rewrite /ratchet_flip_erased_message_key ffunE eqxx. Qed.

Lemma ratchet_flip_away
    (erased_chain : bool) (table : ratchet_rom_table)
    (query : ratchet_rom_query) :
  query != ratchet_step_query erased_chain ->
  ratchet_flip_erased_message_key erased_chain table query = table query.
Proof.
  move=> differs.
  by rewrite /ratchet_flip_erased_message_key ffunE (negbTE differs).
Qed.

Lemma ratchet_flip_changes_only_message_slot
    (erased_chain : bool) (table : ratchet_rom_table) :
  ratchet_message_key
      (ratchet_flip_erased_message_key erased_chain table) erased_chain =
      negb (ratchet_message_key table erased_chain) /\
  ratchet_next_chain
      (ratchet_flip_erased_message_key erased_chain table) erased_chain =
      ratchet_next_chain table erased_chain /\
  ratchet_nonce
      (ratchet_flip_erased_message_key erased_chain table) erased_chain =
      ratchet_nonce table erased_chain.
Proof.
  rewrite /ratchet_message_key /ratchet_next_chain /ratchet_nonce
    ratchet_flip_at_erased_query /ratchet_flip_message_answer /=.
  by repeat split.
Qed.

(** The record-key coupling leaves every query in the disjoint domain exactly unchanged. *)
Theorem ratchet_other_domain_separation
    (erased_chain input : bool) (table : ratchet_rom_table) :
  ratchet_flip_erased_message_key erased_chain table
      (ratchet_other_domain_query input) =
  table (ratchet_other_domain_query input).
Proof.
  apply: ratchet_flip_away.
  exact: ratchet_domains_are_disjoint.
Qed.

Lemma ratchet_flip_erased_message_key_involutive
    (erased_chain : bool) :
  cancel (ratchet_flip_erased_message_key erased_chain)
    (ratchet_flip_erased_message_key erased_chain).
Proof.
  move=> table.
  apply/ffunP=> query.
  rewrite /ratchet_flip_erased_message_key !ffunE.
  case query_is_erased: (query == ratchet_step_query erased_chain) => /=.
  - rewrite /ratchet_flip_message_answer.
    case table_answer: (table query) => [message [next nonce]] /=.
    by rewrite negbK.
  - reflexivity.
Qed.

Lemma ratchet_flip_erased_message_key_bijective
    (erased_chain : bool) :
  bijective (ratchet_flip_erased_message_key erased_chain).
Proof.
  exists (ratchet_flip_erased_message_key erased_chain).
  - exact: ratchet_flip_erased_message_key_involutive.
  - exact: ratchet_flip_erased_message_key_involutive.
Qed.

Definition ratchet_hidden_source := (bool * ratchet_rom_table)%type.

Definition ratchet_default_table : ratchet_rom_table :=
  [ffun _ => (false, (false, false))].

Definition ratchet_default_source : ratchet_hidden_source :=
  (false, ratchet_default_table).

Definition ratchet_uniform_hidden_source :
    {distr ratchet_hidden_source / R} :=
  @uniform_F _ ratchet_default_source.

Definition ratchet_flip_hidden_source
    (source : ratchet_hidden_source) : ratchet_hidden_source :=
  (source.1, ratchet_flip_erased_message_key source.1 source.2).

Lemma ratchet_flip_hidden_source_involutive :
  cancel ratchet_flip_hidden_source ratchet_flip_hidden_source.
Proof.
  move=> [erased_chain table].
  rewrite /ratchet_flip_hidden_source /=
    ratchet_flip_erased_message_key_involutive.
  reflexivity.
Qed.

Lemma ratchet_flip_hidden_source_bijective :
  bijective ratchet_flip_hidden_source.
Proof.
  exists ratchet_flip_hidden_source.
  - exact ratchet_flip_hidden_source_involutive.
  - exact ratchet_flip_hidden_source_involutive.
Qed.

Lemma ratchet_uniform_source_event_reindex
    (event : pred ratchet_hidden_source) :
  \P_[ratchet_uniform_hidden_source] event =
  \P_[ratchet_uniform_hidden_source]
    (fun source => event (ratchet_flip_hidden_source source)).
Proof.
  rewrite /pr.
  have flip_reindex :
    psum (fun source : ratchet_hidden_source =>
      ((nat_of_bool (event source))%:R *
        ratchet_uniform_hidden_source source : R)) =
    psum (fun source : ratchet_hidden_source =>
      ((nat_of_bool (event (ratchet_flip_hidden_source source)))%:R *
        ratchet_uniform_hidden_source
          (ratchet_flip_hidden_source source) : R)).
  {
    apply: reindex_psum.
    - by move=> source _.
    - exists ratchet_flip_hidden_source.
      + by move=> source _; apply: ratchet_flip_hidden_source_involutive.
      + by move=> source _; apply: ratchet_flip_hidden_source_involutive.
  }
  rewrite flip_reindex.
  apply: eq_psum=> source.
  congr (_ * _).
Qed.

(** This is the entire post-erasure public input: the compromised current chain, the prior ciphertext, and the prior nonce. *)
Definition ratchet_public_challenge := (bool * (bool * bool))%type.

Definition ratchet_public_view
    (challenge : bool)
    (source : ratchet_hidden_source) : ratchet_public_challenge :=
  let erased_chain := source.1 in
  let table := source.2 in
  (ratchet_next_chain table erased_chain,
    (xorb challenge (ratchet_message_key table erased_chain),
      ratchet_nonce table erased_chain)).

Lemma ratchet_public_view_flip_coupling
    (source : ratchet_hidden_source) :
  ratchet_public_view false source =
  ratchet_public_view true (ratchet_flip_hidden_source source).
Proof.
  case: source=> erased_chain table.
  rewrite /ratchet_public_view /ratchet_flip_hidden_source /=.
  move: (ratchet_flip_changes_only_message_slot erased_chain table) =>
    [message_flips [chain_preserved nonce_preserved]].
  rewrite message_flips chain_preserved nonce_preserved.
  by case: (ratchet_message_key table erased_chain).
Qed.

Definition ratchet_trace_queries_erased_chain
    (source : ratchet_hidden_source)
    (trace : ratchet_rom_trace) : bool :=
  has (fun entry => entry.1 == ratchet_step_query source.1) trace.

Section BoundedForwardSecrecyAttacker.

  Variable result : choiceType.

  Definition ratchet_attacker_view :=
    (ratchet_public_challenge *
      rom_observation ratchet_rom_query ratchet_rom_answer result)%type.

  Definition ratchet_bounded_attacker_view
      (fuel : nat)
      (challenge : bool)
      (source : ratchet_hidden_source)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result) :
      ratchet_attacker_view :=
    let public := ratchet_public_view challenge source in
    (public,
      run_bounded_rom ratchet_rom_query ratchet_rom_answer fuel source.2
        (program public)).

  Definition ratchet_bad_query_event
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (source : ratchet_hidden_source) : bool :=
    ratchet_trace_queries_erased_chain source
      (ratchet_bounded_attacker_view fuel false source program).2.2.

  Lemma ratchet_bounded_runs_agree_without_erased_query
      (fuel : nat)
      (source : ratchet_hidden_source)
      (program : rom_tree ratchet_rom_query ratchet_rom_answer result) :
    ~~ ratchet_trace_queries_erased_chain source
      (run_bounded_rom ratchet_rom_query ratchet_rom_answer fuel source.2
        program).2 ->
    run_bounded_rom ratchet_rom_query ratchet_rom_answer fuel
      (ratchet_flip_hidden_source source).2 program =
    run_bounded_rom ratchet_rom_query ratchet_rom_answer fuel source.2
      program.
  Proof.
    case: source=> erased_chain table /=.
    revert program.
    induction fuel as [| fuel induction_hypothesis];
      intros [value | query next]; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite /ratchet_trace_queries_erased_chain /=.
      move=> /norP [query_differs tail_avoids_erased].
      rewrite (ratchet_flip_away erased_chain table query query_differs).
      rewrite (induction_hypothesis
        (next (table query)) tail_avoids_erased).
      reflexivity.
  Qed.

  Lemma ratchet_coupled_views_agree_without_bad_query
      (fuel : nat)
      (source : ratchet_hidden_source)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result) :
    ~~ ratchet_bad_query_event fuel program source ->
    ratchet_bounded_attacker_view fuel false source program =
    ratchet_bounded_attacker_view fuel true
      (ratchet_flip_hidden_source source) program.
  Proof.
    move=> avoids_erased.
    have public_equal := ratchet_public_view_flip_coupling source.
    rewrite /ratchet_bounded_attacker_view -public_equal.
    congr (_, _).
    symmetry.
    apply: ratchet_bounded_runs_agree_without_erased_query.
    move: avoids_erased.
    by rewrite /ratchet_bad_query_event /ratchet_bounded_attacker_view.
  Qed.

  Definition ratchet_decision_event
      (fuel : nat)
      (challenge : bool)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (distinguisher : ratchet_attacker_view -> bool)
      (source : ratchet_hidden_source) : bool :=
    distinguisher
      (ratchet_bounded_attacker_view fuel challenge source program).

  Definition ratchet_coupled_mismatch_event
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (distinguisher : ratchet_attacker_view -> bool)
      (source : ratchet_hidden_source) : bool :=
    ratchet_decision_event fuel false program distinguisher source !=
    ratchet_decision_event fuel true program distinguisher
      (ratchet_flip_hidden_source source).

  Lemma ratchet_mismatch_implies_erased_chain_query
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (distinguisher : ratchet_attacker_view -> bool) :
    {subset ratchet_coupled_mismatch_event fuel program distinguisher <=
      ratchet_bad_query_event fuel program}.
  Proof.
    move=> source decisions_differ.
    case bad_query: (ratchet_bad_query_event fuel program source) => //.
    have avoids_bad : ~~ ratchet_bad_query_event fuel program source.
    { by rewrite bad_query. }
    have views_equal := ratchet_coupled_views_agree_without_bad_query
      fuel source program avoids_bad.
    have decisions_equal :
      ratchet_decision_event fuel false program distinguisher source =
      ratchet_decision_event fuel true program distinguisher
        (ratchet_flip_hidden_source source).
    {
      rewrite /ratchet_decision_event.
      exact (f_equal distinguisher views_equal).
    }
    rewrite /ratchet_coupled_mismatch_event in decisions_differ.
    move/negP: decisions_differ=> decisions_not_equal.
    have decisions_same :
      ratchet_decision_event fuel false program distinguisher source ==
      ratchet_decision_event fuel true program distinguisher
        (ratchet_flip_hidden_source source).
    { exact/eqP. }
    have impossible : False := decisions_not_equal decisions_same.
    by case: impossible.
  Qed.

  Definition ratchet_forward_secrecy_advantage
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (distinguisher : ratchet_attacker_view -> bool) : R :=
    `| \P_[ratchet_uniform_hidden_source]
          (ratchet_decision_event fuel false program distinguisher) -
        \P_[ratchet_uniform_hidden_source]
          (ratchet_decision_event fuel true program distinguisher) |.

  Definition ratchet_bad_query_probability
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result) : R :=
    \P_[ratchet_uniform_hidden_source]
      (ratchet_bad_query_event fuel program).

  Lemma ratchet_same_source_decision_difference_bound
      (left_decision right_decision : pred ratchet_hidden_source) :
    `| \P_[ratchet_uniform_hidden_source] left_decision -
        \P_[ratchet_uniform_hidden_source] right_decision | <=
    \P_[ratchet_uniform_hidden_source]
      (fun source => left_decision source != right_decision source).
  Proof.
    pose mismatch :=
      (fun source => left_decision source != right_decision source).
    have left_in_union :
        {subset left_decision <= [predU right_decision & mismatch]}.
    {
      move=> source.
      rewrite -!topredE /= /mismatch.
      move=> left_true.
      rewrite -!topredE /= /mismatch.
      by rewrite left_true; case: (right_decision source).
    }
    have right_in_union :
        {subset right_decision <= [predU left_decision & mismatch]}.
    {
      move=> source.
      rewrite -!topredE /= /mismatch.
      move=> right_true.
      rewrite -!topredE /= /mismatch.
      by rewrite right_true; case: (left_decision source).
    }
    have left_le :
        \P_[ratchet_uniform_hidden_source] left_decision <=
        \P_[ratchet_uniform_hidden_source] right_decision +
        \P_[ratchet_uniform_hidden_source] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ratchet_uniform_hidden_source]
          [predU right_decision & mismatch])).
      exact: subset_pr left_in_union.
      exact: ler_pr_or.
    }
    have right_le :
        \P_[ratchet_uniform_hidden_source] right_decision <=
        \P_[ratchet_uniform_hidden_source] left_decision +
        \P_[ratchet_uniform_hidden_source] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ratchet_uniform_hidden_source]
          [predU left_decision & mismatch])).
      exact: subset_pr right_in_union.
      exact: ler_pr_or.
    }
    rewrite ler_norml.
    apply/andP; split.
    - rewrite lerBrDr.
      rewrite [(- \P_[ratchet_uniform_hidden_source] mismatch +
        \P_[ratchet_uniform_hidden_source] right_decision)]addrC.
      by rewrite lerBlDr.
    - rewrite lerBlDr
        [\P_[ratchet_uniform_hidden_source] mismatch + _]addrC.
      exact: left_le.
  Qed.

  (** Conditional one-step forward secrecy after erasure: every bounded adaptive classical-ROM distinguisher has advantage at most the probability that its challenge-zero execution queries the exact erased prior-chain input. *)
  Theorem ratchet_erasure_forward_secrecy_bad_query_bound
      (fuel : nat)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result)
      (distinguisher : ratchet_attacker_view -> bool) :
    ratchet_forward_secrecy_advantage fuel program distinguisher <=
    ratchet_bad_query_probability fuel program.
  Proof.
    rewrite /ratchet_forward_secrecy_advantage.
    rewrite (ratchet_uniform_source_event_reindex
      (ratchet_decision_event fuel true program distinguisher)).
    apply/(@le_trans _ _
      (\P_[ratchet_uniform_hidden_source]
        (ratchet_coupled_mismatch_event fuel program distinguisher))).
    - exact: ratchet_same_source_decision_difference_bound.
    - rewrite /ratchet_bad_query_probability.
      exact: subset_pr
        (ratchet_mismatch_implies_erased_chain_query
          fuel program distinguisher).
  Qed.

  Theorem ratchet_attacker_trace_query_count_bound
      (fuel : nat)
      (challenge : bool)
      (source : ratchet_hidden_source)
      (program : ratchet_public_challenge ->
        rom_tree ratchet_rom_query ratchet_rom_answer result) :
    Nat.le
      (size (ratchet_bounded_attacker_view
        fuel challenge source program).2.2) fuel.
  Proof.
    rewrite /ratchet_bounded_attacker_view.
    exact: run_bounded_rom_query_count_bound.
  Qed.

End BoundedForwardSecrecyAttacker.

Print Assumptions ratchet_other_domain_separation.
Print Assumptions ratchet_flip_erased_message_key_involutive.
Print Assumptions ratchet_mismatch_implies_erased_chain_query.
Print Assumptions ratchet_erasure_forward_secrecy_bad_query_bound.
Print Assumptions ratchet_attacker_trace_query_count_bound.
