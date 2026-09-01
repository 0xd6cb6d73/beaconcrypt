(* SPDX-License-Identifier: 0BSD *)

(** A finite active-record-integrity game for beaconcrypt under an assumed ideal deterministic combined-record-authenticator abstraction.

    The hidden finite table represents the combined acceptance decision made by the direction-specific AEAD key and the CTX commitment check. Its input contains the key direction, associated data, CTX sender identifier, nonce, sequence, and ciphertext. This does not claim that the production AEAD tag alone binds the sender identifier or sequence. A deterministic adaptive adversary receives one honestly authenticated ciphertext, may make bounded classical authenticator-oracle queries, and returns one candidate context and payload. The verifier appends exactly one hidden-table query for that candidate.

    The broad active-modification classification partitions candidates according to whether their exact authentication input was already queried. The fresh-input event and fresh-guess event are the same event by definition; this bookkeeping is not itself a reduction to an independently defined AEAD or CTX primitive game. Reusing the honest ciphertext and tag in a distinct context, or at a distinct sequence, yields an explicit unequal-input/equal-tag collision in the same sampled table. One-bit atoms make the games finite but provide no production forgery or collision bound. Replay of the identical context, rollback, persistence, state publication, AEAD/CTX composition, and primitive or implementation correctness are outside this file. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum eqtype choice fintype finfun seq reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom.

Local Open Scope ring_scope.

(** Semantic public context: direction-specific key selector, CTX sender identifier, associated data, nonce, and sequence. The ideal table represents the combined AEAD-tag and CTX-check result. *)
Definition record_context :=
  (bool * (bool * (bool * (bool * bool))))%type.

Definition record_direction (context : record_context) : bool := context.1.
Definition record_sender_id (context : record_context) : bool := context.2.1.
Definition record_associated_data (context : record_context) : bool :=
  context.2.2.1.
Definition record_nonce (context : record_context) : bool :=
  context.2.2.2.1.
Definition record_sequence (context : record_context) : bool :=
  context.2.2.2.2.

Definition record_auth_input := (record_context * bool)%type.
Definition record_tag_table := rom_table record_auth_input bool.
Definition record_tag_trace := rom_trace record_auth_input bool.

(** A protected payload is ciphertext plus tag. *)
Definition record_payload := (bool * bool)%type.
Definition record_ciphertext (payload : record_payload) : bool := payload.1.
Definition record_tag (payload : record_payload) : bool := payload.2.

Definition record_auth_input_of
    (context : record_context)
    (payload : record_payload) : record_auth_input :=
  (context, record_ciphertext payload).

Definition record_honest_payload
    (table : record_tag_table)
    (context : record_context)
    (ciphertext : bool) : record_payload :=
  (ciphertext, table (context, ciphertext)).

(** The adversary returns a candidate context and protected payload. *)
Definition record_attempt := (record_context * record_payload)%type.
Definition record_attempt_context (attempt : record_attempt) : record_context :=
  attempt.1.
Definition record_attempt_payload (attempt : record_attempt) : record_payload :=
  attempt.2.
Definition record_attempt_input (attempt : record_attempt) : record_auth_input :=
  record_auth_input_of
    (record_attempt_context attempt) (record_attempt_payload attempt).

(** The verifier exposes the original honest payload, the candidate, and the one tag-table answer used to check it. *)
Definition record_verified_attempt :=
  (record_payload * (record_attempt * bool))%type.

Definition record_verified_honest_payload
    (verified : record_verified_attempt) : record_payload := verified.1.
Definition record_verified_raw_attempt
    (verified : record_verified_attempt) : record_attempt := verified.2.1.
Definition record_verified_candidate_answer
    (verified : record_verified_attempt) : bool := verified.2.2.

Fixpoint record_attach_verifier
    (honest_payload : record_payload)
    (adversary : rom_tree record_auth_input bool record_attempt) :
    rom_tree record_auth_input bool record_verified_attempt :=
  match adversary with
  | RomReturn attempt =>
      RomQuery record_auth_input bool record_verified_attempt
        (record_attempt_input attempt)
        (fun candidate_answer =>
          RomReturn record_auth_input bool record_verified_attempt
            (honest_payload, (attempt, candidate_answer)))
  | RomQuery input next =>
      RomQuery record_auth_input bool record_verified_attempt input
        (fun output => record_attach_verifier honest_payload (next output))
  end.

Definition record_integrity_observation :=
  rom_observation record_auth_input bool record_verified_attempt.

Definition record_candidate_accepted
    (verified : record_verified_attempt) : bool :=
  record_verified_candidate_answer verified ==
  record_tag (record_attempt_payload (record_verified_raw_attempt verified)).

Definition record_candidate_differs_from_honest
    (honest_context : record_context)
    (verified : record_verified_attempt) : bool :=
  record_attempt_input (record_verified_raw_attempt verified) !=
  record_auth_input_of honest_context
    (record_verified_honest_payload verified).

Definition record_active_modification_verified
    (honest_context : record_context)
    (verified : record_verified_attempt) : bool :=
  record_candidate_accepted verified &&
  record_candidate_differs_from_honest honest_context verified.

Definition record_active_modification_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  match observation.1 with
  | Some verified => record_active_modification_verified honest_context verified
  | None => false
  end.

(** On a completed run the final trace entry is the verifier query. This prefix therefore contains exactly the adversary's completed queries. *)
Definition record_adversary_trace
    (observation : record_integrity_observation) : record_tag_trace :=
  take (size observation.2).-1 observation.2.

Definition record_candidate_was_queried
    (observation : record_integrity_observation) : bool :=
  match observation.1 with
  | Some verified =>
      has (fun entry =>
        entry.1 == record_attempt_input
          (record_verified_raw_attempt verified))
        (record_adversary_trace observation)
  | None => false
  end.

Definition record_known_input_attempt_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  record_active_modification_event honest_context observation &&
  record_candidate_was_queried observation.

Definition record_fresh_tag_guess_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  record_active_modification_event honest_context observation &&
  ~~ record_candidate_was_queried observation.

Lemma record_active_modification_splits_into_bad_events
    (honest_context : record_context) :
  {subset record_active_modification_event honest_context <=
    [predU record_known_input_attempt_event honest_context &
      record_fresh_tag_guess_event honest_context]}.
Proof.
  move=> observation forgery.
  rewrite !inE /record_known_input_attempt_event
    /record_fresh_tag_guess_event.
  apply/orP.
  case queried: (record_candidate_was_queried observation).
  - left. by apply/andP; split.
  - right. apply/andP; split=> //.
    by rewrite queried.
Qed.

Lemma record_partition_events_imply_active_modification
    (honest_context : record_context) :
  {subset
    [predU record_known_input_attempt_event honest_context &
      record_fresh_tag_guess_event honest_context] <=
    record_active_modification_event honest_context}.
Proof.
  move=> observation.
  rewrite !inE /record_known_input_attempt_event
    /record_fresh_tag_guess_event.
  move/orP=> [/andP [active _] | /andP [active _]]; exact active.
Qed.

(** Standard fresh-input integrity excludes both the honestly generated input and every exact input previously submitted to the authenticator oracle. *)
Definition record_fresh_input_integrity_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  record_active_modification_event honest_context observation &&
  ~~ record_candidate_was_queried observation.

Lemma record_fresh_input_integrity_is_fresh_guess
    (honest_context : record_context) :
  {subset record_fresh_input_integrity_event honest_context <=
    record_fresh_tag_guess_event honest_context}.
Proof.
  by move=> observation; rewrite /record_fresh_input_integrity_event
    /record_fresh_tag_guess_event.
Qed.

Definition record_hidden_integrity_game
    (table_distribution : {distr record_tag_table / R})
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
    {distr record_integrity_observation / R} :=
  @dlet R record_tag_table record_integrity_observation
    (fun table =>
      let honest_payload :=
        record_honest_payload table honest_context honest_ciphertext in
      @dunit R record_integrity_observation
        (run_bounded_rom record_auth_input bool (Nat.add adversary_fuel 1)
          table
          (record_attach_verifier honest_payload
            (adversary honest_payload))))
    table_distribution.

Definition record_default_tag_table : record_tag_table :=
  [ffun _ => false].

Definition record_uniform_hidden_integrity_game
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
    {distr record_integrity_observation / R} :=
  record_hidden_integrity_game
    (uniform_hidden_rom_table record_auth_input bool false)
    adversary_fuel honest_context honest_ciphertext adversary.

(** Exact event partition: a successful distinct accepted candidate either repeats an exact tag-oracle input or is fresh. This theorem is bookkeeping inside the combined-authenticator game, not a primitive-security reduction. *)
Theorem record_active_modification_query_or_guess_classification_bound
    (table_distribution : {distr record_tag_table / R})
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_active_modification_event honest_context) <=
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      [predU record_known_input_attempt_event honest_context &
        record_fresh_tag_guess_event honest_context].
Proof.
  exact: subset_pr
    (record_active_modification_splits_into_bad_events honest_context).
Qed.

Corollary record_uniform_active_modification_query_or_guess_classification_bound
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
  \P_[ record_uniform_hidden_integrity_game adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_active_modification_event honest_context) <=
  \P_[ record_uniform_hidden_integrity_game adversary_fuel
          honest_context honest_ciphertext adversary ]
      [predU record_known_input_attempt_event honest_context &
        record_fresh_tag_guess_event honest_context].
Proof.
  exact: record_active_modification_query_or_guess_classification_bound.
Qed.

(** The fresh-input and fresh-guess predicates are definitionally identical. Keeping the equality explicit prevents this classification from being mistaken for a separate primitive reduction. *)
Theorem record_fresh_input_integrity_probability_is_fresh_guess
    (table_distribution : {distr record_tag_table / R})
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_fresh_input_integrity_event honest_context) =
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_fresh_tag_guess_event honest_context).
Proof.
  reflexivity.
Qed.

Definition record_collision_pair :=
  ((record_auth_input * bool) * (record_auth_input * bool))%type.
Definition record_collision_witness := option record_collision_pair.

Definition record_collision_witness_valid
    (witness : record_collision_witness) : bool :=
  match witness with
  | Some (lhs, rhs) =>
      (lhs.1 != rhs.1) && (lhs.2 == rhs.2)
  | None => false
  end.

Definition record_extract_collision
    (honest_context : record_context)
    (observation : record_integrity_observation) : record_collision_witness :=
  match observation.1 with
  | Some verified =>
      let honest_payload := record_verified_honest_payload verified in
      let attempt := record_verified_raw_attempt verified in
      Some
        ((record_auth_input_of honest_context honest_payload,
           record_tag honest_payload),
         (record_attempt_input attempt,
           record_verified_candidate_answer verified))
  | None => None
  end.

Definition record_same_payload_cross_context_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  match observation.1 with
  | Some verified =>
      let attempt := record_verified_raw_attempt verified in
      record_candidate_accepted verified &&
      (record_attempt_payload attempt ==
        record_verified_honest_payload verified) &&
      (record_attempt_context attempt != honest_context)
  | None => false
  end.

Definition record_same_payload_cross_sequence_event
    (honest_context : record_context)
    (observation : record_integrity_observation) : bool :=
  match observation.1 with
  | Some verified =>
      let attempt := record_verified_raw_attempt verified in
      record_candidate_accepted verified &&
      (record_attempt_payload attempt ==
        record_verified_honest_payload verified) &&
      (record_sequence (record_attempt_context attempt) !=
        record_sequence honest_context)
  | None => false
  end.

Lemma record_cross_context_reuse_implies_collision
    (honest_context : record_context)
    (observation : record_integrity_observation) :
  record_same_payload_cross_context_event honest_context observation ->
  record_collision_witness_valid
    (record_extract_collision honest_context observation).
Proof.
  case: observation=> [[verified |] trace] //=.
  rewrite /record_same_payload_cross_context_event
    /record_collision_witness_valid /record_extract_collision /=.
  move=> /andP [/andP [accepted /eqP payload_equal] context_differs].
  rewrite /record_candidate_accepted in accepted.
  have tag_equal := congr1 record_tag payload_equal.
  apply/andP; split.
  - have honest_context_differs :
        honest_context !=
          record_attempt_context (record_verified_raw_attempt verified).
    { by rewrite eq_sym. }
    rewrite /record_auth_input_of /record_attempt_input xpair_eqE.
    by rewrite (negbTE honest_context_differs).
  - move/eqP: accepted=> accepted.
    apply/eqP.
    rewrite -tag_equal.
    exact: esym accepted.
Qed.

Lemma record_cross_sequence_reuse_implies_cross_context
    (honest_context : record_context)
    (observation : record_integrity_observation) :
  record_same_payload_cross_sequence_event honest_context observation ->
  record_same_payload_cross_context_event honest_context observation.
Proof.
  case: observation=> [[verified |] trace] //=.
  rewrite /record_same_payload_cross_sequence_event
    /record_same_payload_cross_context_event /=.
  move=> /andP [/andP [accepted same_payload] sequence_differs].
  apply/andP; split; first exact/andP.
  apply/negP=> /eqP context_equal.
  move/negP: sequence_differs=> sequence_differs.
  apply: sequence_differs.
  by rewrite context_equal eqxx.
Qed.

Lemma record_cross_sequence_reuse_implies_collision
    (honest_context : record_context)
    (observation : record_integrity_observation) :
  record_same_payload_cross_sequence_event honest_context observation ->
  record_collision_witness_valid
    (record_extract_collision honest_context observation).
Proof.
  move=> cross_sequence.
  apply: (record_cross_context_reuse_implies_collision honest_context
    observation).
  exact: (record_cross_sequence_reuse_implies_cross_context honest_context
    observation cross_sequence).
Qed.

Theorem record_cross_context_reuse_reduces_to_collision
    (table_distribution : {distr record_tag_table / R})
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_same_payload_cross_context_event honest_context) <=
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (fun observation =>
        record_collision_witness_valid
          (record_extract_collision honest_context observation)).
Proof.
  apply: subset_pr.
  exact: record_cross_context_reuse_implies_collision.
Qed.

Theorem record_cross_sequence_reuse_reduces_to_collision
    (table_distribution : {distr record_tag_table / R})
    (adversary_fuel : nat)
    (honest_context : record_context)
    (honest_ciphertext : bool)
    (adversary : record_payload ->
      rom_tree record_auth_input bool record_attempt) :
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (record_same_payload_cross_sequence_event honest_context) <=
  \P_[ record_hidden_integrity_game table_distribution adversary_fuel
          honest_context honest_ciphertext adversary ]
      (fun observation =>
        record_collision_witness_valid
          (record_extract_collision honest_context observation)).
Proof.
  apply: subset_pr.
  exact: record_cross_sequence_reuse_implies_collision.
Qed.

(** Every public trace contains at most the adversary budget plus the one verifier query. *)
Theorem record_integrity_trace_size_bound
    (adversary_fuel : nat)
    (table : record_tag_table)
    (honest_payload : record_payload)
    (adversary : rom_tree record_auth_input bool record_attempt) :
  Nat.le
    (size
      (run_bounded_rom record_auth_input bool (Nat.add adversary_fuel 1)
        table (record_attach_verifier honest_payload adversary)).2)
    (Nat.add adversary_fuel 1).
Proof.
  exact: run_bounded_rom_query_count_bound.
Qed.

Print Assumptions record_active_modification_query_or_guess_classification_bound.
Print Assumptions record_uniform_active_modification_query_or_guess_classification_bound.
Print Assumptions record_fresh_input_integrity_probability_is_fresh_guess.
Print Assumptions record_cross_context_reuse_reduces_to_collision.
Print Assumptions record_cross_sequence_reuse_reduces_to_collision.
Print Assumptions record_integrity_trace_size_bound.
