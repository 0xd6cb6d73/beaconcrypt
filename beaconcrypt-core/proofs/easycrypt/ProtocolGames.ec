(* SPDX-License-Identifier: 0BSD *)

(** Abstract state and attacker interfaces.

    The state is keyed by an unbounded [session_id], rather than unrolling one fixed session. The concrete primitive module is deliberately abstract: primitive implementation correctness is outside this computational proof. Security assumptions about the primitives are not introduced in this file. *)

require import AllCore Int FMap FSet.
require import Common.

(** EasyCrypt represents session identifiers and sequence numbers as mathematical integers. The send theorem below restricts a live counter to the production [u64] interval; session identifiers remain unbounded abstract map keys. A send at the maximum current counter is rejected, matching the production exhaustion policy. *)
op max_sequence : sequence_number = 18446744073709551615.

module type PrimitiveSuite = {
  proc establish(sid : session_id, bundle : public_bundle) : session_secret option
  proc seal(secret : session_secret, counter : sequence_number,
            plaintext : message) : frame
  proc unseal(secret : session_secret, counter : sequence_number,
              ciphertext : frame) : message option
}.

(** This API is the intended hax/Lean/F* refinement boundary. A refinement proof must relate the extracted Rust state transitions to these operations; this EasyCrypt file does not assert that correspondence. *)
module type StatefulProtocolAPI = {
  proc init() : unit
  proc register(sid : session_id, bundle : public_bundle) : bool
  proc send(sid : session_id, plaintext : message) : frame option
  proc receive(sid : session_id, counter : sequence_number,
               ciphertext : frame) : message option
  proc corrupt(sid : session_id) : session_secret option
}.

module StatefulProtocol(P : PrimitiveSuite) : StatefulProtocolAPI = {
  var secrets : (session_id, session_secret) fmap
  var send_sequence : (session_id, sequence_number) fmap
  var receive_sequence : (session_id, sequence_number) fmap
  var compromised : session_id fset

  proc init() : unit = {
    secrets <- empty;
    send_sequence <- empty;
    receive_sequence <- empty;
    compromised <- fset0;
  }

  proc register(sid : session_id, bundle : public_bundle) : bool = {
    var secret;
    secret <- None;
    if (!(sid \in secrets)) {
      secret <@ P.establish(sid, bundle);
      if (secret <> None) {
        secrets.[sid] <- oget secret;
        send_sequence.[sid] <- 0;
        receive_sequence.[sid] <- 0;
      }
    }
    return secret <> None;
  }

  proc send(sid : session_id, plaintext : message) : frame option = {
    var ciphertext, sealed, counter;
    ciphertext <- None;
    if (sid \in secrets /\ oget send_sequence.[sid] < max_sequence) {
      counter <- oget send_sequence.[sid];
      sealed <@ P.seal(oget secrets.[sid], counter, plaintext);
      send_sequence.[sid] <- counter + 1;
      ciphertext <- Some sealed;
    }
    return ciphertext;
  }

  proc receive(sid : session_id, counter : sequence_number,
               ciphertext : frame) : message option = {
    var plaintext;
    plaintext <- None;
    if (sid \in secrets /\ counter = oget receive_sequence.[sid]) {
      plaintext <@ P.unseal(oget secrets.[sid], counter, ciphertext);
      if (plaintext <> None) {
        receive_sequence.[sid] <- counter + 1;
      }
    }
    return plaintext;
  }

  proc corrupt(sid : session_id) : session_secret option = {
    var secret;
    secret <- secrets.[sid];
    if (secret <> None) {
      compromised <- compromised `|` fset1 sid;
    }
    return secret;
  }
}.

lemma stateful_protocol_init(P <: PrimitiveSuite) :
  hoare[StatefulProtocol(P).init : true ==>
    StatefulProtocol.secrets = empty /\
    StatefulProtocol.send_sequence = empty /\
    StatefulProtocol.receive_sequence = empty /\
    StatefulProtocol.compromised = fset0].
proof. by proc; auto. qed.

(** The selected session's send counter advances exactly once after a call to the abstract sealing primitive. This is a partial-correctness statement: it needs no losslessness or security assumption about [P.seal]. *)
lemma stateful_protocol_send_existing_session
  (P <: PrimitiveSuite {-StatefulProtocol})
  (sid : session_id) (plaintext : message)
  (counter : sequence_number) :
  hoare[StatefulProtocol(P).send :
    arg = (sid, plaintext) /\
    sid \in StatefulProtocol.secrets /\
    StatefulProtocol.send_sequence.[sid] = Some counter /\
    0 <= counter /\
    counter < max_sequence ==>
    res <> None /\
    StatefulProtocol.send_sequence.[sid] = Some (counter + 1)].
proof.
  proc.
  sp.
  if.
  + wp; call (_ : true); auto; smt(get_set_sameE).
  auto; smt.
qed.

(** Passive adversaries choose registration identifiers, public bundles, and plaintext inputs, and receive the resulting honest outputs. This is a chosen-input transcript interface; it exposes no delivery/decryption or corruption procedure. *)
module type PassiveProtocolAPI = {
  proc honest_register(sid : session_id, bundle : public_bundle) : bool
  proc honest_send(sid : session_id, plaintext : message) : frame option
}.

(** Active adversaries additionally control delivery and may request modeled corruptions. [deliver] is a decryption oracle returning the plaintext option from [receive]. Replay, replacement, reordering, and cross-session delivery are expressible as inputs, but the state machine has only an exact-next receive counter: it does not model skipped-key caching, bounded receive gaps, or rollback. *)
module type ActiveProtocolAPI = {
  proc honest_register(sid : session_id, bundle : public_bundle) : bool
  proc honest_send(sid : session_id, plaintext : message) : frame option
  proc deliver(sid : session_id, counter : sequence_number,
               ciphertext : frame) : message option
  proc corrupt(sid : session_id) : session_secret option
}.

module PassiveView(S : StatefulProtocolAPI) : PassiveProtocolAPI = {
  proc honest_register = S.register
  proc honest_send = S.send
}.

module ActiveView(S : StatefulProtocolAPI) : ActiveProtocolAPI = {
  proc honest_register = S.register
  proc honest_send = S.send
  proc deliver = S.receive
  proc corrupt = S.corrupt
}.

module type PassiveAdversary(O : PassiveProtocolAPI) = {
  proc run() : bool
}.

module type ActiveAdversary(O : ActiveProtocolAPI) = {
  proc run() : bool
}.

module PassiveClassicalGame
  (S : StatefulProtocolAPI) (A : PassiveAdversary) = {
  proc main() : bool = {
    var result;
    S.init();
    result <@ A(PassiveView(S)).run();
    return result;
  }
}.

module ActiveClassicalGame
  (S : StatefulProtocolAPI) (A : ActiveAdversary) = {
  proc main() : bool = {
    var result;
    S.init();
    result <@ A(ActiveView(S)).run();
    return result;
  }
}.

(** This wrapper is intentionally identical to the passive classical game at the EasyCrypt level. Its eventual post-quantum theorem requires a quantum-sound interpretation (for example, a reviewed EasyPQC toolchain) and QPT/QROM primitive assumptions. Mainline EasyCrypt alone cannot prove that theorem. *)
module PassiveQuantumClassicalInterfaceGame
  (S : StatefulProtocolAPI) (A : PassiveAdversary) = {
  proc main() : bool = {
    var result;
    S.init();
    result <@ A(PassiveView(S)).run();
    return result;
  }
}.
