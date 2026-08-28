(* SPDX-License-Identifier: 0BSD *)

(** Finite classical coupling for one erased symmetric-ratchet hop.  This file
    models only the distributional argument; it makes no quantum claim. *)

require import AllCore Bool Distr DBool.

type ratchet_answer = bool * bool * bool.
type ratchet_public_view = bool * bool * bool.

op ratchet_step_domain : bool = false.
op ratchet_other_domain : bool = true.

lemma ratchet_domains_are_disjoint :
  ratchet_step_domain <> ratchet_other_domain.
proof. by rewrite /ratchet_step_domain /ratchet_other_domain. qed.

op bit_xor (x y : bool) : bool = (x <> y).

op ratchet_flip_message_slot (a : ratchet_answer) : ratchet_answer =
  (!a.`1, a.`2, a.`3).

lemma ratchet_flip_message_slot_involutive (a : ratchet_answer) :
  ratchet_flip_message_slot (ratchet_flip_message_slot a) = a.
proof. by rewrite /ratchet_flip_message_slot; case a=> x y z /=. qed.

lemma ratchet_flip_preserves_chain_and_nonce (a : ratchet_answer) :
  (ratchet_flip_message_slot a).`2 = a.`2 /\
  (ratchet_flip_message_slot a).`3 = a.`3.
proof. by rewrite /ratchet_flip_message_slot; case a=> x y z. qed.

op ratchet_public (challenge : bool) (a : ratchet_answer) : ratchet_public_view =
  (a.`2, bit_xor challenge a.`1, a.`3).

lemma ratchet_public_flip_coupling (a : ratchet_answer) :
  ratchet_public false a = ratchet_public true (ratchet_flip_message_slot a).
proof.
  rewrite /ratchet_public /ratchet_flip_message_slot /bit_xor.
  by case a=> x y z; case x.
qed.

module RatchetForwardGame = {
  proc main(challenge : bool) : ratchet_public_view = {
    var message_key, next_chain, nonce;
    nonce <$ dbool;
    next_chain <$ dbool;
    message_key <$ dbool;
    return (next_chain, bit_xor challenge message_key, nonce);
  }
}.

(** Exact finite reindexing: complementing the uniform erased message key
    couples the two games; the compromised next chain and nonce are identical. *)
lemma ratchet_erased_message_key_exact_distribution :
  equiv[RatchetForwardGame.main ~ RatchetForwardGame.main :
    arg{1} = false /\ arg{2} = true ==> ={res}].
proof.
  proc.
  rnd (fun x => !x).
  + rnd; rnd; auto=> />; rewrite /bit_xor; smt.
qed.

module type RatchetViewDistinguisher = {
  proc distinguish(view : ratchet_public_view) : bool
}.

module RatchetDistinguisherGame(A : RatchetViewDistinguisher) = {
  proc main(challenge : bool) : bool = {
    var view, decision;
    view <@ RatchetForwardGame.main(challenge);
    decision <@ A.distinguish(view);
    return decision;
  }
}.

section GenericRatchetDistinguisher.

declare module A <: RatchetViewDistinguisher {-RatchetDistinguisherGame, -RatchetForwardGame}.

lemma ratchet_arbitrary_distinguisher_exact_distribution :
  equiv[RatchetDistinguisherGame(A).main ~ RatchetDistinguisherGame(A).main :
    ={glob A} /\ arg{1} = false /\ arg{2} = true ==> ={res}].
proof.
  proc.
  call (_ : ={glob A, arg} ==> ={glob A, res}).
  + sim.
  call ratchet_erased_message_key_exact_distribution.
  auto.
qed.

lemma ratchet_erasure_forward_secrecy_exact &m :
  Pr[RatchetDistinguisherGame(A).main(false) @ &m : res] =
  Pr[RatchetDistinguisherGame(A).main(true) @ &m : res].
proof. byequiv ratchet_arbitrary_distinguisher_exact_distribution => //. qed.

end section GenericRatchetDistinguisher.

(** The key used for the old record is absent from [ratchet_public_view].  This
    is the formal erasure boundary in this finite hop, not an implementation
    claim about memory zeroization or persistence. *)
lemma ratchet_public_view_contains_only_chain_ciphertext_nonce
  (challenge : bool) (a : ratchet_answer) :
  ratchet_public challenge a = (a.`2, bit_xor challenge a.`1, a.`3).
proof. by rewrite /ratchet_public. qed.
