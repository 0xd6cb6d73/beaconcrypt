(* SPDX-License-Identifier: 0BSD *)

(** A finite, executable hidden-ROM game for the binding part of beaconcrypt's modified CTX transform.

    Every semantic field is represented by one bit.
    This makes the random oracle a finite object that SSProve can sample uniformly, while retaining the protocol-level separation between the AEAD ciphertext/tag and the CTX commitment.
    The complete oracle table is held only by [run_bounded_rom].
    The adversary and the game event see only query answers and the public trace.

    The theorem proved here is a same-run extractor reduction: two accepted, distinct explanations for one payload yield two distinct CTX transcripts with the same returned digest.
    It neither proves a numerical birthday bound nor assumes any correctness or security property of the AEAD. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnum eqtype choice
  fintype finfun seq reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom.

Local Open Scope ring_scope.

(** Five semantic fields supplied by an explanation: [K, N, A, S, I]. *)
Definition ctx_open_context :=
  (bool * (bool * (bool * (bool * bool))))%type.

Definition ctx_key (context : ctx_open_context) : bool := context.1.
Definition ctx_nonce (context : ctx_open_context) : bool := context.2.1.
Definition ctx_associated_data (context : ctx_open_context) : bool :=
  context.2.2.1.
Definition ctx_sequence (context : ctx_open_context) : bool :=
  context.2.2.2.1.
Definition ctx_sender_id (context : ctx_open_context) : bool :=
  context.2.2.2.2.

(** The transcript is [((K, N, A, S, I), T)].
    Product nesting acts as an injective encoding of the six fixed-width production fields. *)
Definition ctx_transcript :=
  (ctx_open_context * bool)%type.

(** A protected payload is [(C, (T, U))], where [U] is the CTX commitment. *)
Definition ctx_payload :=
  (bool * (bool * bool))%type.

Definition ctx_ciphertext (payload : ctx_payload) : bool := payload.1.
Definition ctx_tag (payload : ctx_payload) : bool := payload.2.1.
Definition ctx_commitment (payload : ctx_payload) : bool := payload.2.2.

(** An explanation is [((K, N, A, S, I), M)]. *)
Definition ctx_explanation :=
  (ctx_open_context * bool)%type.

Definition ctx_explanation_context
    (explanation : ctx_explanation) : ctx_open_context :=
  explanation.1.

Definition ctx_plaintext (explanation : ctx_explanation) : bool :=
  explanation.2.

Definition ctx_transcript_of
    (payload : ctx_payload)
    (explanation : ctx_explanation) : ctx_transcript :=
  (ctx_explanation_context explanation, ctx_tag payload).

(** The base AEAD opening relation is deterministic but otherwise unconstrained.
    In particular, the reduction does not assume AEAD key commitment, privacy, or ciphertext integrity. *)
Definition ctx_aead_open :=
  bool -> bool -> bool -> bool -> bool -> option bool.

(** The adversary returns one payload and two candidate explanations. *)
Definition ctx_attempt :=
  (ctx_payload * (ctx_explanation * ctx_explanation))%type.

Definition ctx_attempt_payload (attempt : ctx_attempt) : ctx_payload :=
  attempt.1.
Definition ctx_attempt_left (attempt : ctx_attempt) : ctx_explanation :=
  attempt.2.1.
Definition ctx_attempt_right (attempt : ctx_attempt) : ctx_explanation :=
  attempt.2.2.

(** The verifier extends a returned attempt with exactly the two ROM answers needed to check its explanations.
    This value, rather than the hidden table, is exposed to the game event. *)
Definition ctx_verified_attempt :=
  (ctx_attempt * (bool * bool))%type.

Definition ctx_verified_raw_attempt
    (verified : ctx_verified_attempt) : ctx_attempt :=
  verified.1.
Definition ctx_verified_left_digest
    (verified : ctx_verified_attempt) : bool :=
  verified.2.1.
Definition ctx_verified_right_digest
    (verified : ctx_verified_attempt) : bool :=
  verified.2.2.

Fixpoint ctx_attach_verifier
    (adversary : rom_tree ctx_transcript bool ctx_attempt)
    : rom_tree ctx_transcript bool ctx_verified_attempt :=
  match adversary with
  | RomReturn attempt =>
      RomQuery ctx_transcript bool ctx_verified_attempt
        (ctx_transcript_of
           (ctx_attempt_payload attempt) (ctx_attempt_left attempt))
        (fun left_digest =>
           RomQuery ctx_transcript bool ctx_verified_attempt
             (ctx_transcript_of
                (ctx_attempt_payload attempt) (ctx_attempt_right attempt))
             (fun right_digest =>
                RomReturn ctx_transcript bool ctx_verified_attempt
                  (attempt, (left_digest, right_digest))))
  | RomQuery input next =>
      RomQuery ctx_transcript bool ctx_verified_attempt input
        (fun output => ctx_attach_verifier (next output))
  end.

(** The return branch makes the two-query verifier suffix explicit. *)
Lemma ctx_attach_verifier_return_shape (attempt : ctx_attempt) :
  ctx_attach_verifier
    (RomReturn ctx_transcript bool ctx_attempt attempt) =
  RomQuery ctx_transcript bool ctx_verified_attempt
    (ctx_transcript_of
       (ctx_attempt_payload attempt) (ctx_attempt_left attempt))
    (fun left_digest =>
       RomQuery ctx_transcript bool ctx_verified_attempt
         (ctx_transcript_of
            (ctx_attempt_payload attempt) (ctx_attempt_right attempt))
         (fun right_digest =>
            RomReturn ctx_transcript bool ctx_verified_attempt
              (attempt, (left_digest, right_digest)))).
Proof. reflexivity. Qed.

Definition ctx_verified_opening_accepted
    (aead_open : ctx_aead_open)
    (payload : ctx_payload)
    (explanation : ctx_explanation)
    (digest : bool) : bool :=
  let context := ctx_explanation_context explanation in
  (digest == ctx_commitment payload) &&
  (aead_open
     (ctx_key context)
     (ctx_nonce context)
     (ctx_associated_data context)
     (ctx_ciphertext payload)
     (ctx_tag payload) == Some (ctx_plaintext explanation)).

Definition ctx_verified_misattribution
    (aead_open : ctx_aead_open)
    (verified : ctx_verified_attempt) : bool :=
  let attempt := ctx_verified_raw_attempt verified in
  (ctx_verified_opening_accepted aead_open
       (ctx_attempt_payload attempt) (ctx_attempt_left attempt)
       (ctx_verified_left_digest verified) &&
   ctx_verified_opening_accepted aead_open
       (ctx_attempt_payload attempt) (ctx_attempt_right attempt)
       (ctx_verified_right_digest verified)) &&
  (ctx_attempt_left attempt != ctx_attempt_right attempt).

(** If two accepted explanations have the same transcript, deterministic AEAD opening forces the same plaintext and hence the same explanation. *)
Lemma ctx_same_transcript_verified_explanations_equal
    (aead_open : ctx_aead_open)
    (payload : ctx_payload)
    (left right : ctx_explanation)
    (left_digest right_digest : bool) :
  ctx_transcript_of payload left = ctx_transcript_of payload right ->
  ctx_verified_opening_accepted
    aead_open payload left left_digest ->
  ctx_verified_opening_accepted
    aead_open payload right right_digest ->
  left = right.
Proof.
  destruct left as [left_context left_plaintext].
  destruct right as [right_context right_plaintext].
  rewrite /ctx_transcript_of /ctx_explanation_context /=.
  move=> transcript_equal.
  have context_equal : left_context = right_context :=
    congr1 fst transcript_equal.
  rewrite /ctx_verified_opening_accepted /ctx_explanation_context
    /ctx_plaintext /=.
  move=> /andP [_ /eqP left_open] /andP [_ /eqP right_open].
  have plaintext_equal : left_plaintext = right_plaintext.
  {
    have some_equal : Some left_plaintext = Some right_plaintext.
    {
      rewrite -left_open -right_open context_equal.
      reflexivity.
    }
    injection some_equal.
    by move=> ->.
  }
  by rewrite context_equal plaintext_equal.
Qed.

(** A collision witness consists only of the two queried transcripts and their returned answers. *)
Definition ctx_collision_pair :=
  ((ctx_transcript * bool) * (ctx_transcript * bool))%type.
Definition ctx_collision_witness := option ctx_collision_pair.

Definition ctx_collision_of_verified
    (verified : ctx_verified_attempt) : ctx_collision_pair :=
  let attempt := ctx_verified_raw_attempt verified in
  ((ctx_transcript_of
      (ctx_attempt_payload attempt) (ctx_attempt_left attempt),
    ctx_verified_left_digest verified),
   (ctx_transcript_of
      (ctx_attempt_payload attempt) (ctx_attempt_right attempt),
    ctx_verified_right_digest verified)).

Definition ctx_collision_witness_valid
    (witness : ctx_collision_witness) : bool :=
  match witness with
  | Some (first_entry, second_entry) =>
      (first_entry.1 != second_entry.1) &&
      (first_entry.2 == second_entry.2)
  | None => false
  end.

Lemma ctx_verified_misattribution_implies_collision
    (aead_open : ctx_aead_open)
    (verified : ctx_verified_attempt) :
  ctx_verified_misattribution aead_open verified ->
  ctx_collision_witness_valid (Some (ctx_collision_of_verified verified)).
Proof.
  rewrite /ctx_verified_misattribution /ctx_collision_witness_valid
    /ctx_collision_of_verified /=.
  move=> /andP [/andP [left_accepted right_accepted]
                    explanations_differ].
  apply/andP; split.
  - apply/negP.
    move/eqP=> transcripts_equal.
    have explanations_equal :=
      ctx_same_transcript_verified_explanations_equal
        aead_open
        (ctx_attempt_payload (ctx_verified_raw_attempt verified))
        (ctx_attempt_left (ctx_verified_raw_attempt verified))
        (ctx_attempt_right (ctx_verified_raw_attempt verified))
        (ctx_verified_left_digest verified)
        (ctx_verified_right_digest verified)
        transcripts_equal left_accepted right_accepted.
    move/negP: explanations_differ => explanations_differ.
    apply: explanations_differ.
    exact/eqP.
  - move/andP: left_accepted => [/eqP left_hash _].
    move/andP: right_accepted => [/eqP right_hash _].
    apply/eqP.
    by rewrite left_hash right_hash.
Qed.

Definition ctx_binding_observation :=
  rom_observation ctx_transcript bool ctx_verified_attempt.

Definition ctx_hidden_misattribution_event
    (aead_open : ctx_aead_open)
    (observation : ctx_binding_observation) : bool :=
  match observation.1 with
  | Some verified => ctx_verified_misattribution aead_open verified
  | None => false
  end.

Definition ctx_extract_collision
    (observation : ctx_binding_observation) : ctx_collision_witness :=
  match observation.1 with
  | Some verified => Some (ctx_collision_of_verified verified)
  | None => None
  end.

Lemma ctx_hidden_extractor_sound
    (aead_open : ctx_aead_open)
    (observation : ctx_binding_observation) :
  ctx_hidden_misattribution_event aead_open observation ->
  ctx_collision_witness_valid (ctx_extract_collision observation).
Proof.
  destruct observation as [[verified |] trace] => //=.
  exact: ctx_verified_misattribution_implies_collision.
Qed.

(** The hidden table is sampled first, then consumed by the bounded runner.
    The total budget is [adversary_fuel + 2], so any successful checked run spends at most [adversary_fuel] queries before reaching the two-query verifier suffix. *)
Definition ctx_hidden_binding_game
    (table_distribution :
       {distr (rom_table ctx_transcript bool) / R})
    (adversary_fuel : nat)
    (adversary : rom_tree ctx_transcript bool ctx_attempt) :=
  bounded_rom_game ctx_transcript bool ctx_verified_attempt
    table_distribution (Nat.add adversary_fuel 2)
    (ctx_attach_verifier adversary).

Definition ctx_uniform_hidden_binding_game
    (adversary_fuel : nat)
    (adversary : rom_tree ctx_transcript bool ctx_attempt) :=
  uniform_bounded_rom_game ctx_transcript bool false ctx_verified_attempt
    (Nat.add adversary_fuel 2) (ctx_attach_verifier adversary).

(** Capstone CTX reduction.
    Its right side is deliberately the primitive same-run ROM collision event; deriving a numerical birthday bound is a separate ideal-ROM assumption and is outside this development. *)
Theorem ctx_hidden_rom_extractor_reduction
    (aead_open : ctx_aead_open)
    (table_distribution :
       {distr (rom_table ctx_transcript bool) / R})
    (adversary_fuel : nat)
    (adversary : rom_tree ctx_transcript bool ctx_attempt) :
  \P_[ ctx_hidden_binding_game
          table_distribution adversary_fuel adversary ]
      (ctx_hidden_misattribution_event aead_open) <=
  \P_[ ctx_hidden_binding_game
          table_distribution adversary_fuel adversary ]
      (fun observation =>
         ctx_collision_witness_valid (ctx_extract_collision observation)).
Proof.
  exact:
    (bounded_rom_same_run_extractor_reduction
       ctx_transcript bool ctx_verified_attempt ctx_collision_witness
       table_distribution (Nat.add adversary_fuel 2)
       (ctx_attach_verifier adversary)
       (ctx_hidden_misattribution_event aead_open)
       ctx_extract_collision ctx_collision_witness_valid
       (ctx_hidden_extractor_sound aead_open)).
Qed.

(** Specialization to a uniformly sampled finite random function. *)
Corollary ctx_uniform_hidden_rom_extractor_reduction
    (aead_open : ctx_aead_open)
    (adversary_fuel : nat)
    (adversary : rom_tree ctx_transcript bool ctx_attempt) :
  \P_[ ctx_uniform_hidden_binding_game adversary_fuel adversary ]
      (ctx_hidden_misattribution_event aead_open) <=
  \P_[ ctx_uniform_hidden_binding_game adversary_fuel adversary ]
      (fun observation =>
         ctx_collision_witness_valid (ctx_extract_collision observation)).
Proof.
  exact:
    (ctx_hidden_rom_extractor_reduction aead_open
       (uniform_hidden_rom_table ctx_transcript bool false)
       adversary_fuel adversary).
Qed.

(** Every public trace contains at most the adversary budget plus the two verifier queries. *)
Theorem ctx_hidden_binding_trace_size_bound
    (adversary_fuel : nat)
    (table : rom_table ctx_transcript bool)
    (adversary : rom_tree ctx_transcript bool ctx_attempt) :
  Nat.le
    (size
       (run_bounded_rom ctx_transcript bool
          (Nat.add adversary_fuel 2) table
          (ctx_attach_verifier adversary)).2)
    (Nat.add adversary_fuel 2).
Proof.
  exact: run_bounded_rom_query_count_bound.
Qed.

(** More precisely, whenever the adversary itself returns within its budget, the attached run preserves its trace and appends exactly the two verifier query/answer entries. *)
Theorem ctx_attach_verifier_completed_run
    (adversary_fuel : nat)
    (table : rom_table ctx_transcript bool)
    (adversary : rom_tree ctx_transcript bool ctx_attempt)
    (attempt : ctx_attempt)
    (trace : rom_trace ctx_transcript bool) :
  run_bounded_rom ctx_transcript bool adversary_fuel table adversary =
    (Some attempt, trace) ->
  run_bounded_rom ctx_transcript bool (Nat.add adversary_fuel 2) table
      (ctx_attach_verifier adversary) =
    (Some
       (attempt,
        (table
           (ctx_transcript_of
              (ctx_attempt_payload attempt) (ctx_attempt_left attempt)),
         table
           (ctx_transcript_of
              (ctx_attempt_payload attempt) (ctx_attempt_right attempt)))),
     trace ++
       [:: (ctx_transcript_of
              (ctx_attempt_payload attempt) (ctx_attempt_left attempt),
             table
               (ctx_transcript_of
                  (ctx_attempt_payload attempt) (ctx_attempt_left attempt)));
           (ctx_transcript_of
              (ctx_attempt_payload attempt) (ctx_attempt_right attempt),
             table
               (ctx_transcript_of
                  (ctx_attempt_payload attempt) (ctx_attempt_right attempt))) ]).
Proof.
  revert adversary attempt trace.
  induction adversary_fuel as [| adversary_fuel induction_hypothesis];
    intros [returned | input next] attempt trace completed.
  - simpl in completed.
    inversion completed; subst.
    rewrite Nat.add_comm.
    reflexivity.
  - discriminate completed.
  - simpl in completed.
    inversion completed; subst.
    rewrite Nat.add_comm.
    reflexivity.
  - change
      ((let execution :=
          run_bounded_rom ctx_transcript bool adversary_fuel table
            (next (table input)) in
        (execution.1, (input, table input) :: execution.2)) =
       (Some attempt, trace)) in completed.
    destruct
      (run_bounded_rom ctx_transcript bool adversary_fuel table
         (next (table input))) as [status suffix] eqn:recursive_run.
    simpl in completed.
    inversion completed; subst.
    simpl.
    rewrite
      (induction_hypothesis
         (next (table input)) attempt suffix recursive_run).
    reflexivity.
Qed.

(** A small executable challenge shows that the event is not vacuous.
    The toy AEAD returns its key as plaintext and the constant-zero oracle makes the two distinct verifier transcripts collide. *)
Definition ctx_constant_zero_rom : rom_table ctx_transcript bool :=
  [ffun _ => false].

Definition ctx_multi_open_aead : ctx_aead_open :=
  fun key _nonce _associated_data _ciphertext _tag => Some key.

Definition ctx_left_context : ctx_open_context :=
  (false, (false, (false, (false, false)))).

Definition ctx_right_context : ctx_open_context :=
  (true, (false, (false, (false, false)))).

Definition ctx_challenge_payload : ctx_payload :=
  (false, (false, false)).

Definition ctx_challenge_attempt : ctx_attempt :=
  (ctx_challenge_payload,
    ((ctx_left_context, false), (ctx_right_context, true))).

Definition ctx_challenge_adversary :
    rom_tree ctx_transcript bool ctx_attempt :=
  RomReturn ctx_transcript bool ctx_attempt ctx_challenge_attempt.

Lemma ctx_constant_zero_rom_lookup (input : ctx_transcript) :
  ctx_constant_zero_rom input = false.
Proof.
  by rewrite /ctx_constant_zero_rom ffunE.
Qed.

Lemma ctx_challenge_verified_misattribution :
  ctx_verified_misattribution ctx_multi_open_aead
    (ctx_challenge_attempt, (false, false)).
Proof.
  reflexivity.
Qed.

Lemma ctx_hidden_misattribution_challenge_reachable :
  ctx_hidden_misattribution_event ctx_multi_open_aead
    (run_bounded_rom ctx_transcript bool 2 ctx_constant_zero_rom
       (ctx_attach_verifier ctx_challenge_adversary)).
Proof.
  have adversary_completed :
      run_bounded_rom ctx_transcript bool 0 ctx_constant_zero_rom
        ctx_challenge_adversary = (Some ctx_challenge_attempt, [::]) :=
    erefl.
  have verifier_completed :=
    ctx_attach_verifier_completed_run 0 ctx_constant_zero_rom
      ctx_challenge_adversary ctx_challenge_attempt [::]
      adversary_completed.
  rewrite verifier_completed /= !ctx_constant_zero_rom_lookup.
  exact: ctx_challenge_verified_misattribution.
Qed.

Print Assumptions ctx_hidden_rom_extractor_reduction.
Print Assumptions ctx_uniform_hidden_rom_extractor_reduction.
Print Assumptions ctx_hidden_binding_trace_size_bound.
Print Assumptions ctx_attach_verifier_completed_run.
