(* SPDX-License-Identifier: 0BSD *)

(** Bounded classical probability games for one ideal PQXDH establishment followed by one record. The "quantum" modes below are capability labels only: every adversary and distribution in this file has ordinary classical EasyCrypt semantics. *)

require import AllCore Distr DBool Real.
require import Common.

type network_action = [ Forward | Replace ].

op accepted_input_recomputable (mode : attacker_mode) (action : network_action) : bool = has_quantum_computation mode /\ action = Replace /\ has_active_network mode.

lemma active_classical_root_hidden (action : network_action) : !accepted_input_recomputable active_classical action.
proof. by case: action. qed.

lemma passive_classical_root_hidden : !accepted_input_recomputable passive_classical Forward.
proof. by rewrite /accepted_input_recomputable /passive_classical /has_quantum_computation. qed.

lemma passive_quantum_capability_root_hidden : !accepted_input_recomputable passive_quantum Forward.
proof. by rewrite /accepted_input_recomputable /passive_quantum /has_active_network. qed.

lemma active_quantum_replacement_recomputable : accepted_input_recomputable active_quantum Replace.
proof. by rewrite /accepted_input_recomputable /active_quantum /has_active_network /has_quantum_computation. qed.

module type ViewDistinguisher = {
  proc distinguish(view : bool) : bool
}.

(** In a supported forwarding game the sampled Boolean is the bounded ideal record pad. A classical replacement is rejected with a fixed observation, while in the active-quantum capability game the attacker recomputes the accepted substituted input, removes the pad, and receives the challenge. *)
module ProtocolViewGame(D : ViewDistinguisher) = {
  proc main(mode : attacker_mode, action : network_action, challenge : bool) : bool = {
    var pad, view, decision;
    pad <$ dbool;
    view <- if action = Replace /\ !accepted_input_recomputable mode action then false else if accepted_input_recomputable mode action then challenge else challenge = pad;
    decision <@ D.distinguish(view);
    return decision;
  }
}.

section GenericDistinguisher.

declare module D <: ViewDistinguisher {-ProtocolViewGame}.

lemma hidden_root_games_equivalent (mode : attacker_mode) (action : network_action) : !accepted_input_recomputable mode action => equiv[ProtocolViewGame(D).main ~ ProtocolViewGame(D).main : ={glob D} /\ arg{1} = (mode, action, false) /\ arg{2} = (mode, action, true) ==> ={res}].
proof.
  move=> hidden.
  proc.
  call (_ : ={glob D, arg} ==> ={glob D, res}).
  + sim.
  wp.
  rnd (fun b => !b); auto; smt.
qed.

lemma hidden_root_confidentiality (mode : attacker_mode) (action : network_action) &m : !accepted_input_recomputable mode action => `|Pr[ProtocolViewGame(D).main(mode, action, false) @ &m : res] - Pr[ProtocolViewGame(D).main(mode, action, true) @ &m : res]| = 0%r.
proof.
  move=> hidden.
  have games_equal : Pr[ProtocolViewGame(D).main(mode, action, false) @ &m : res] = Pr[ProtocolViewGame(D).main(mode, action, true) @ &m : res] by byequiv (hidden_root_games_equivalent mode action hidden).
  rewrite games_equal; smt.
qed.

lemma active_classical_confidentiality (action : network_action) &m : `|Pr[ProtocolViewGame(D).main(active_classical, action, false) @ &m : res] - Pr[ProtocolViewGame(D).main(active_classical, action, true) @ &m : res]| = 0%r.
proof. exact (hidden_root_confidentiality active_classical action &m (active_classical_root_hidden action)). qed.

lemma passive_classical_confidentiality &m : `|Pr[ProtocolViewGame(D).main(passive_classical, Forward, false) @ &m : res] - Pr[ProtocolViewGame(D).main(passive_classical, Forward, true) @ &m : res]| = 0%r.
proof. exact (hidden_root_confidentiality passive_classical Forward &m passive_classical_root_hidden). qed.

(** This is a classical-query capability theorem, not a QPT or QROM theorem. *)
lemma passive_quantum_capability_confidentiality &m : `|Pr[ProtocolViewGame(D).main(passive_quantum, Forward, false) @ &m : res] - Pr[ProtocolViewGame(D).main(passive_quantum, Forward, true) @ &m : res]| = 0%r.
proof. exact (hidden_root_confidentiality passive_quantum Forward &m passive_quantum_capability_root_hidden). qed.

end section GenericDistinguisher.

module RecoveredPlaintextDistinguisher : ViewDistinguisher = {
  proc distinguish(view : bool) : bool = {
    return view;
  }
}.

module ActiveQuantumRecoveryGame = {
  proc main(challenge : bool) : bool = {
    var decision;
    decision <@ RecoveredPlaintextDistinguisher.distinguish(challenge);
    return decision;
  }
}.

lemma active_quantum_protocol_is_recovery_game (challenge : bool) :
  equiv[ProtocolViewGame(RecoveredPlaintextDistinguisher).main ~
        ActiveQuantumRecoveryGame.main :
    arg{1} = (active_quantum, Replace, challenge) /\ arg{2} = challenge ==>
    ={res}].
proof.
  proc; inline *; wp.
  rnd{1}.
  auto.
qed.

lemma active_quantum_false_probability_zero &m : Pr[ActiveQuantumRecoveryGame.main(false) @ &m : res] = 0%r.
proof. byphoare (_ : arg = false ==> _) => //=; hoare; proc; inline *; auto. qed.

lemma active_quantum_true_probability_one &m : Pr[ActiveQuantumRecoveryGame.main(true) @ &m : res] = 1%r.
proof. byphoare (_ : arg = true ==> _) => //=; proc; inline *; auto. qed.

lemma active_quantum_protocol_probability (challenge : bool) &m : Pr[ProtocolViewGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, challenge) @ &m : res] = Pr[ActiveQuantumRecoveryGame.main(challenge) @ &m : res].
proof. byequiv (active_quantum_protocol_is_recovery_game challenge) => //. qed.

lemma active_quantum_advantage_one &m : `|Pr[ProtocolViewGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, false) @ &m : res] - Pr[ProtocolViewGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, true) @ &m : res]| = 1%r.
proof. rewrite !active_quantum_protocol_probability active_quantum_false_probability_zero active_quantum_true_probability_one; smt. qed.
