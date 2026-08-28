(* SPDX-License-Identifier: 0BSD *)

(** Shared, implementation-independent vocabulary for the EasyCrypt computational games.

    The first component of [attacker_mode] records network control and the second records quantum computation. Quantum computation here is only a capability label. Mainline EasyCrypt does not interpret arbitrary modules as quantum programs. *)

require import AllCore Int.

type session_id = int.
type sequence_number = int.

type message.
type frame.
type public_bundle.
type session_secret.

type attacker_mode = bool * bool.

op passive_classical : attacker_mode = (false, false).
op active_classical  : attacker_mode = (true,  false).
op passive_quantum   : attacker_mode = (false, true ).
op active_quantum    : attacker_mode = (true,  true ).

op has_active_network (m : attacker_mode) : bool = m.`1.
op has_quantum_computation (m : attacker_mode) : bool = m.`2.

lemma passive_classical_capabilities :
  !has_active_network passive_classical /\
  !has_quantum_computation passive_classical.
proof. by rewrite /has_active_network /has_quantum_computation
                  /passive_classical. qed.

lemma active_classical_capabilities :
  has_active_network active_classical /\
  !has_quantum_computation active_classical.
proof. by rewrite /has_active_network /has_quantum_computation
                  /active_classical. qed.

lemma passive_quantum_capabilities :
  !has_active_network passive_quantum /\
  has_quantum_computation passive_quantum.
proof. by rewrite /has_active_network /has_quantum_computation
                  /passive_quantum. qed.

lemma active_quantum_capabilities :
  has_active_network active_quantum /\
  has_quantum_computation active_quantum.
proof. by rewrite /has_active_network /has_quantum_computation
                  /active_quantum. qed.
