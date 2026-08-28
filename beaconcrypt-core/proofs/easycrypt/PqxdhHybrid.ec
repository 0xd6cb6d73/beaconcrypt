(* SPDX-License-Identifier: 0BSD *)

(** One-hidden-contribution hybrid counterparts for the bounded PQXDH game. The five coordinates preserve the production order DH1, DH2, DH3, DH4, ML-KEM only at the abstract semantic level; this file is not extracted and proves no HKDF implementation fact. *)

require import AllCore Distr DBool Real.
require import Common PqxdhGames.

type hybrid_component = [ HybridDh1 | HybridDh2 | HybridDh3 | HybridDh4 | HybridMlKem ].

op component_is_classical (component : hybrid_component) : bool = component <> HybridMlKem.

op component_remains_hidden (mode : attacker_mode) (action : network_action) (component : hybrid_component) : bool = if component_is_classical component then !has_quantum_computation mode else action = Forward.

lemma active_classical_forward_mlkem_remains_hidden : component_remains_hidden active_classical Forward HybridMlKem.
proof. by rewrite /component_remains_hidden /component_is_classical /active_classical /has_active_network /has_quantum_computation. qed.

lemma passive_classical_forward_mlkem_remains_hidden : component_remains_hidden passive_classical Forward HybridMlKem.
proof. by rewrite /component_remains_hidden /component_is_classical /passive_classical /has_active_network /has_quantum_computation. qed.

lemma passive_quantum_forward_mlkem_remains_hidden : component_remains_hidden passive_quantum Forward HybridMlKem.
proof. by rewrite /component_remains_hidden /component_is_classical /passive_quantum /has_active_network /has_quantum_computation. qed.

lemma passive_quantum_classical_components_exposed (component : hybrid_component) : component_is_classical component => !component_remains_hidden passive_quantum Forward component.
proof. by case: component. qed.

lemma active_quantum_replace_has_no_hidden_component (component : hybrid_component) : !component_remains_hidden active_quantum Replace component.
proof. by case: component. qed.

module HybridGame(D : ViewDistinguisher) = {
  proc main(mode : attacker_mode, action : network_action, component : hybrid_component, challenge : bool) : bool = {
    var hidden, pad, view, decision;
    hidden <- component_remains_hidden mode action component;
    pad <$ dbool;
    view <- if hidden then challenge = pad else challenge;
    decision <@ D.distinguish(view);
    return decision;
  }
}.

section GenericHybridDistinguisher.

declare module D <: ViewDistinguisher {-HybridGame}.

lemma one_hidden_contribution_games_equivalent (mode : attacker_mode) (action : network_action) (component : hybrid_component) : component_remains_hidden mode action component => equiv[HybridGame(D).main ~ HybridGame(D).main : ={glob D} /\ arg{1} = (mode, action, component, false) /\ arg{2} = (mode, action, component, true) ==> ={res}].
proof.
  move=> hidden.
  proc.
  call (_ : ={glob D, arg} ==> ={glob D, res}).
  + sim.
  wp.
  rnd (fun b => !b); auto; smt.
qed.

lemma one_hidden_contribution_confidentiality (mode : attacker_mode) (action : network_action) (component : hybrid_component) &m : component_remains_hidden mode action component => `|Pr[HybridGame(D).main(mode, action, component, false) @ &m : res] - Pr[HybridGame(D).main(mode, action, component, true) @ &m : res]| = 0%r.
proof.
  move=> hidden.
  have games_equal : Pr[HybridGame(D).main(mode, action, component, false) @ &m : res] = Pr[HybridGame(D).main(mode, action, component, true) @ &m : res] by byequiv (one_hidden_contribution_games_equivalent mode action component hidden).
  rewrite games_equal; smt.
qed.

lemma hybrid_active_classical_confidentiality &m : `|Pr[HybridGame(D).main(active_classical, Forward, HybridMlKem, false) @ &m : res] - Pr[HybridGame(D).main(active_classical, Forward, HybridMlKem, true) @ &m : res]| = 0%r.
proof. exact (one_hidden_contribution_confidentiality active_classical Forward HybridMlKem &m active_classical_forward_mlkem_remains_hidden). qed.

lemma hybrid_passive_classical_confidentiality &m : `|Pr[HybridGame(D).main(passive_classical, Forward, HybridMlKem, false) @ &m : res] - Pr[HybridGame(D).main(passive_classical, Forward, HybridMlKem, true) @ &m : res]| = 0%r.
proof. exact (one_hidden_contribution_confidentiality passive_classical Forward HybridMlKem &m passive_classical_forward_mlkem_remains_hidden). qed.

(** This is a classical-query capability theorem, not a QPT or QROM theorem. *)
lemma hybrid_passive_quantum_capability_confidentiality &m : `|Pr[HybridGame(D).main(passive_quantum, Forward, HybridMlKem, false) @ &m : res] - Pr[HybridGame(D).main(passive_quantum, Forward, HybridMlKem, true) @ &m : res]| = 0%r.
proof. exact (one_hidden_contribution_confidentiality passive_quantum Forward HybridMlKem &m passive_quantum_forward_mlkem_remains_hidden). qed.

end section GenericHybridDistinguisher.

lemma hybrid_active_quantum_is_recovery_game (challenge : bool) :
  equiv[HybridGame(RecoveredPlaintextDistinguisher).main ~
        ActiveQuantumRecoveryGame.main :
    arg{1} = (active_quantum, Replace, HybridMlKem, challenge) /\
    arg{2} = challenge ==> ={res}].
proof.
  proc; inline *; wp.
  rnd{1}.
  auto.
qed.

lemma hybrid_active_quantum_probability (challenge : bool) &m : Pr[HybridGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, HybridMlKem, challenge) @ &m : res] = Pr[ActiveQuantumRecoveryGame.main(challenge) @ &m : res].
proof. byequiv (hybrid_active_quantum_is_recovery_game challenge) => //. qed.

lemma hybrid_active_quantum_advantage_one &m : `|Pr[HybridGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, HybridMlKem, false) @ &m : res] - Pr[HybridGame(RecoveredPlaintextDistinguisher).main(active_quantum, Replace, HybridMlKem, true) @ &m : res]| = 1%r.
proof. rewrite !hybrid_active_quantum_probability active_quantum_false_probability_zero active_quantum_true_probability_one; smt. qed.
