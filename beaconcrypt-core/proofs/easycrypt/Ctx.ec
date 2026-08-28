(* SPDX-License-Identifier: 0BSD *)

(** Computational skeleton for beaconcrypt's modified CTX transform.

    Production protects [C || T || U], where

      U = H(K || N || AD || T || LE64(seq) || LE64(sender_id)).

    The extracted Rust/F*/Lean boundary is responsible for proving that [ctx_transcript] is exactly that injective 229-byte encoding. This file proves the game-independent collision-extraction step from that contract. It assumes neither AEAD key commitment nor primitive implementation correctness. *)

require import AllCore List.

type key.
type nonce.
type associated_data.
type aead_tag.
type ciphertext_core.
type digest.
type plaintext.
type transcript.

type sequence_number.
type sender_id.

(** An explanation names exactly the semantic values that production may use when opening a protected payload. In particular, the expected plaintext is data compared with the result of opening; it is not passed to AEAD. *)
type explanation =
  key * nonce * associated_data * sequence_number * sender_id * plaintext.

(** The protected wire payload is exactly [C || T || U] at this abstraction boundary. *)
type protected_payload = ciphertext_core * aead_tag * digest.

op payload_ciphertext (payload : protected_payload) : ciphertext_core = payload.`1.
op payload_tag (payload : protected_payload) : aead_tag = payload.`2.
op payload_commitment (payload : protected_payload) : digest = payload.`3.

op explanation_key (opening : explanation) : key = opening.`1.
op explanation_nonce (opening : explanation) : nonce = opening.`2.
op explanation_ad (opening : explanation) : associated_data = opening.`3.
op explanation_sequence (opening : explanation) : sequence_number = opening.`4.
op explanation_sender (opening : explanation) : sender_id = opening.`5.
op explanation_plaintext (opening : explanation) : plaintext = opening.`6.

(** [ctx_encode] is the sole cross-prover representation boundary. *)
op ctx_encode :
  key -> nonce -> associated_data -> aead_tag ->
  sequence_number -> sender_id -> transcript.

op ctx_transcript (tag : aead_tag) (opening : explanation) : transcript =
  ctx_encode (explanation_key opening) (explanation_nonce opening)
    (explanation_ad opening) tag (explanation_sequence opening)
    (explanation_sender opening).
op ctx_hash : transcript -> digest.
op aead_open :
  key -> nonce -> associated_data -> ciphertext_core -> aead_tag ->
  plaintext option.

op ctx_valid_opening (payload : protected_payload)
                     (opening : explanation) : bool =
  ctx_hash (ctx_transcript (payload_tag payload) opening) =
    payload_commitment payload /\
  aead_open (explanation_key opening) (explanation_nonce opening)
    (explanation_ad opening) (payload_ciphertext payload)
    (payload_tag payload) =
    Some (explanation_plaintext opening).

(** Pending representation/refinement contract: the abstract encoder preserves all six fields in production order. The cited F* theorem proves this fact for the concrete 229-byte builder; connecting that theorem to [ctx_encode] remains a reviewed cross-prover bridge. AEAD determinism needs no axiom: [aead_open] is an EasyCrypt pure function over exactly K, N, AD, C, and T. *)
axiom assumption_ctx_encoding_is_injective
  (key1 key2 : key) (nonce1 nonce2 : nonce)
  (ad1 ad2 : associated_data) (tag1 tag2 : aead_tag)
  (sequence1 sequence2 : sequence_number) (sender1 sender2 : sender_id) :
  ctx_encode key1 nonce1 ad1 tag1 sequence1 sender1 =
    ctx_encode key2 nonce2 ad2 tag2 sequence2 sender2 =>
  key1 = key2 /\ nonce1 = nonce2 /\ ad1 = ad2 /\ tag1 = tag2 /\
  sequence1 = sequence2 /\ sender1 = sender2.

lemma distinct_valid_openings_have_distinct_transcripts
  (payload : protected_payload) (opening1 opening2 : explanation) :
  ctx_valid_opening payload opening1 =>
  ctx_valid_opening payload opening2 =>
  opening1 <> opening2 =>
  ctx_transcript (payload_tag payload) opening1 <>
    ctx_transcript (payload_tag payload) opening2.
proof.
  case: opening1 => key1 nonce1 ad1 sequence1 sender1 plaintext1.
  case: opening2 => key2 nonce2 ad2 sequence2 sender2 plaintext2.
  move=> opening1_valid.
  move=> opening2_valid.
  move=> different.
  apply/negP.
  move=> same_input.
  move: opening1_valid opening2_valid.
  rewrite /ctx_valid_opening /ctx_transcript /explanation_key
    /explanation_nonce /explanation_ad /explanation_sequence
    /explanation_sender /explanation_plaintext.
  move=> [_ open1] [_ open2].
  have fields := assumption_ctx_encoding_is_injective
    key1 key2 nonce1 nonce2 ad1 ad2
    (payload_tag payload) (payload_tag payload)
    sequence1 sequence2 sender1 sender2 same_input.
  move: fields => [same_key [same_nonce [same_ad [_ [same_sequence same_sender]]]]].
  apply different.
  congr.
  move: open1 open2.
  rewrite same_key same_nonce same_ad.
  move=> open1 open2.
  by rewrite open1 in open2.
qed.

op ctx_collision (input1 input2 : transcript) : bool =
  input1 <> input2 /\ ctx_hash input1 = ctx_hash input2.

lemma accepted_distinct_openings_imply_collision
  (payload : protected_payload) (opening1 opening2 : explanation) :
  ctx_valid_opening payload opening1 =>
  ctx_valid_opening payload opening2 =>
  opening1 <> opening2 =>
  ctx_collision
    (ctx_transcript (payload_tag payload) opening1)
    (ctx_transcript (payload_tag payload) opening2).
proof.
  move=> opening1_valid opening2_valid different.
  rewrite /ctx_collision.
  split.
  + exact (distinct_valid_openings_have_distinct_transcripts
      payload opening1 opening2 opening1_valid opening2_valid different).
  move: opening1_valid opening2_valid.
  rewrite /ctx_valid_opening.
  move=> [hash1 _] [hash2 _].
  by rewrite hash1 hash2.
qed.

module type CtxBinder = {
  proc bind() : protected_payload * explanation * explanation
}.

op ctx_binding_event
  (outcome : protected_payload * explanation * explanation) : bool =
  ctx_valid_opening outcome.`1 outcome.`2 /\
  ctx_valid_opening outcome.`1 outcome.`3 /\ outcome.`2 <> outcome.`3.

op ctx_collision_event
  (outcome : protected_payload * explanation * explanation) : bool =
  ctx_collision
    (ctx_transcript (payload_tag outcome.`1) outcome.`2)
    (ctx_transcript (payload_tag outcome.`1) outcome.`3).

lemma ctx_binding_event_implies_collision_event
  (outcome : protected_payload * explanation * explanation) :
  ctx_binding_event outcome => ctx_collision_event outcome.
proof.
  rewrite /ctx_binding_event /ctx_collision_event.
  move=> [opening1_valid [opening2_valid different]].
  exact (accepted_distinct_openings_imply_collision
    outcome.`1 outcome.`2 outcome.`3
    opening1_valid opening2_valid different).
qed.

module CtxBindingGame(B : CtxBinder) = {
  proc main() : bool = {
    var outcome;
    outcome <@ B.bind();
    return ctx_binding_event outcome;
  }
}.

(** The reduction calls the binder once and emits the two concrete hash inputs. [main] checks the collision locally so no table or secret state is leaked. *)
module CtxCollisionReduction(B : CtxBinder) = {
  proc main() : bool = {
    var outcome;
    outcome <@ B.bind();
    return ctx_collision_event outcome;
  }
}.

(** A single-run foundational reduction. The eventual probability theorem additionally needs losslessness of [B.bind] and the standard collision experiment/complexity wrapper. *)
module CtxReductionSoundness(B : CtxBinder) = {
  proc main() : bool = {
    var payload, opening1, opening2, binding_success, collision_success;
    (payload, opening1, opening2) <@ B.bind();
    binding_success <- ctx_valid_opening payload opening1 /\
                       ctx_valid_opening payload opening2 /\ opening1 <> opening2;
    collision_success <- ctx_collision
      (ctx_transcript (payload_tag payload) opening1)
      (ctx_transcript (payload_tag payload) opening2);
    return binding_success => collision_success;
  }
}.

lemma ctx_collision_reduction_is_pointwise_sound(B <: CtxBinder) :
  hoare[CtxReductionSoundness(B).main : true ==> res].
proof.
  proc.
  wp.
  call (_ : true).
  auto=> /> outcome hash1 open1 hash2 open2 different.
  apply (accepted_distinct_openings_imply_collision
    outcome.`1 outcome.`2 outcome.`3).
  + by rewrite /ctx_valid_opening hash1 open1.
  + by rewrite /ctx_valid_opening hash2 open2.
  exact different.
qed.

(** Privacy target (not claimed proved here): in a ROM game that replaces [H(secret transcript)] by a fresh digest, the distinguishing gap is bounded by the probability/amplitude of querying that hidden transcript. A QROM version must use a quantum-sound rule; a classical query log is insufficient.

    Integrity target (not claimed proved here): accepted modification either reuses a previously authenticated exact input, finds a CTX collision, or wins the base AEAD integrity game. CTX does not authenticate modifications of [ciphertext_core] by itself because that field is not hashed. *)

op integrity_partition (accepted previously_authenticated
                        ctx_collision_found base_aead_forgery : bool) : bool =
  accepted =>
    previously_authenticated \/ ctx_collision_found \/ base_aead_forgery.

lemma integrity_partition_from_cases
  (accepted previously_authenticated ctx_collision_found
   base_aead_forgery : bool) :
  (!accepted \/ previously_authenticated \/ ctx_collision_found \/
   base_aead_forgery) =>
  integrity_partition accepted previously_authenticated
    ctx_collision_found base_aead_forgery.
proof.
  rewrite /integrity_partition.
  by case accepted; case previously_authenticated;
     case ctx_collision_found; case base_aead_forgery.
qed.
