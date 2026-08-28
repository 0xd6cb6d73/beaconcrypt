(* SPDX-License-Identifier: 0BSD *)

(** Active-quantum bundle-substitution game.

    The recovery equations are threat-model contracts, not implementations of quantum algorithms. The adversary uses the recovered classical secrets to submit an attacker-selected ML-KEM bundle through the active protocol API. The break event is the protocol's acceptance of that bundle. *)

require import AllCore FMap.
require import Common ProtocolGames.

type ed25519_secret.
type ed25519_public.
type x25519_secret.
type x25519_public.
type mlkem_secret.

op ed25519_public_of : ed25519_secret -> ed25519_public.
op x25519_public_of : x25519_secret -> x25519_public.
op quantum_recover_ed25519 : ed25519_public -> ed25519_secret.
op quantum_recover_x25519 : x25519_public -> x25519_secret.

axiom assumption_quantum_recovers_ed25519 (sk : ed25519_secret) :
  quantum_recover_ed25519 (ed25519_public_of sk) = sk.

axiom assumption_quantum_recovers_x25519 (sk : x25519_secret) :
  quantum_recover_x25519 (x25519_public_of sk) = sk.

op honest_ed25519_secret : ed25519_secret.
op honest_x25519_secret : x25519_secret.
op attacker_selected_mlkem_secret : mlkem_secret.
op substituted_bundle : ed25519_secret -> x25519_secret -> mlkem_secret -> public_bundle.
op attacker_session_secret : session_secret.
op attacker_frame : frame.
op attack_session : session_id = 0.

(** Game-world validation policy. This is not a claim about the Rust primitive implementation. It accepts precisely the forged bundle containing both recovered classical secrets and the attacker-selected KEM contribution, and installs a secret known by the attacker. *)
module QuantumSubstitutionPrimitives : PrimitiveSuite = {
  proc establish(sid : session_id, bundle : public_bundle)
      : session_secret option = {
    var secret;
    secret <- None;
    if (sid = attack_session /\
        bundle = substituted_bundle honest_ed25519_secret
          honest_x25519_secret attacker_selected_mlkem_secret) {
      secret <- Some attacker_session_secret;
    }
    return secret;
  }

  proc seal(secret : session_secret, counter : sequence_number,
            plaintext : message) : frame = {
    return attacker_frame;
  }

  proc unseal(secret : session_secret, counter : sequence_number,
              ciphertext : frame) : message option = {
    return None;
  }
}.

module ActiveQuantumSubstitutionAdversary(O : ActiveProtocolAPI) = {
  proc run() : bool = {
    var recovered_ed, recovered_x, accepted;
    recovered_ed <- quantum_recover_ed25519
      (ed25519_public_of honest_ed25519_secret);
    recovered_x <- quantum_recover_x25519
      (x25519_public_of honest_x25519_secret);
    accepted <@ O.honest_register(
      attack_session,
      substituted_bundle recovered_ed recovered_x
        attacker_selected_mlkem_secret
    );
    return recovered_ed = honest_ed25519_secret /\
           recovered_x = honest_x25519_secret /\
           accepted;
  }
}.

module ActiveQuantumBundleSubstitutionGame =
  ActiveClassicalGame(
    StatefulProtocol(QuantumSubstitutionPrimitives),
    ActiveQuantumSubstitutionAdversary
  ).

(** Under the two recovery contracts, the active game reaches the meaningful break event: the protocol accepts the attacker-selected bundle and installs [attacker_session_secret]. *)
lemma active_quantum_bundle_substitution_break :
  hoare[ActiveQuantumBundleSubstitutionGame.main : true ==>
    res /\
    StatefulProtocol.secrets.[attack_session] =
      Some attacker_session_secret].
proof.
  proc; inline *; auto.
  smt(assumption_quantum_recovers_ed25519
      assumption_quantum_recovers_x25519 get_set_sameE).
qed.
