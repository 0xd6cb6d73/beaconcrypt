(* SPDX-License-Identifier: 0BSD *)

(** An attacker-facing bounded classical-ROM hop for the ideal PQXDH plus symmetric-ratchet confidentiality game.

    The complete tagged random-oracle table and the honest ML-KEM contribution atom are sampled jointly and retained by the runner; the four classical-DH coordinates are conservatively fixed. A deterministic adaptive adversary receives only the public challenge ciphertext and bounded access to the combined root/symmetric oracle. The proof couples challenge zero with challenge one by flipping the record-pad component at the hidden ratchet query. Any distinguishing mismatch in that coupling implies that the public trace queried that exact hidden input.

    All atoms are finite one-bit abstractions. The result is a classical finite-ROM bad-event bound, not a numerical production-width estimate and not a QROM or superposition-query theorem. The handwritten game mirrors the named production root-input ordering and shared symmetric-label shapes recorded in [PqxdhRatchetGames], while importing its authentication capability split; it is not mechanically extracted from the implementation. Primitive and implementation correctness remain outside this file. *)

From Stdlib Require Import Utf8 Arith.PeanoNat btauto.Btauto.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum order eqtype choice fintype finfun seq all_algebra reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import ProtocolLabels BoundedRom PqxdhRatchetGames.

Import Num.Theory.
Import Order.POrderTheory.
Import GRing.Theory.

Local Open Scope ring_scope.

(** Five finite components stand for the complete ordered PQXDH root transcript. The extra leading bit in [protocol_rom_query] is the proved-injective encoding of the exact production info label from [ProtocolLabels]. A symmetric input occupies the first payload bit and has canonical zero padding. *)
Definition protocol_root_atom :=
  (bool * (bool * (bool * (bool * bool))))%type.

Definition protocol_root_atom_of_pqxdh
    (input : pqxdh_root_input) : protocol_root_atom :=
  (dh1_contribution input,
    (dh2_contribution input,
      (dh3_contribution input,
        (dh4_contribution input, mlkem_contribution input)))).

Lemma protocol_honest_root_atom_mapping :
  protocol_root_atom_of_pqxdh honest_pqxdh_input =
  (true, (false, (true, (false, true)))).
Proof. reflexivity. Qed.

Lemma protocol_substituted_root_atom_mapping :
  protocol_root_atom_of_pqxdh substituted_pqxdh_input =
  (false, (true, (false, (true, false)))).
Proof. reflexivity. Qed.

(** For the positive Forward games the four DH coordinates are conservatively fixed and therefore guessable, while the honest ML-KEM contribution remains the sole hidden finite atom. This makes the passive-quantum corollary rely only on the capability contract that honest ML-KEM decapsulation remains opaque. *)
Definition protocol_forward_root_atom
    (hidden_mlkem_contribution : bool) : protocol_root_atom :=
  (true, (false, (true, (false, hidden_mlkem_contribution)))).

Lemma protocol_forward_true_mlkem_is_honest_root_atom :
  protocol_forward_root_atom true =
  protocol_root_atom_of_pqxdh honest_pqxdh_input.
Proof. reflexivity. Qed.

Definition protocol_rom_query :=
  (bool * protocol_root_atom)%type.

(** One common answer type conservatively exposes three components at every tag. Root derivation consumes the first component; symmetric expansion consumes all three, with the first component serving as the record pad at the ratchet-step query. *)
Definition protocol_rom_answer :=
  (bool * (bool * bool))%type.

Definition protocol_rom_table :=
  rom_table protocol_rom_query protocol_rom_answer.

Definition protocol_rom_trace :=
  rom_trace protocol_rom_query protocol_rom_answer.

Definition protocol_root_query
    (input : protocol_root_atom) : protocol_rom_query :=
  (kdf_domain_tag PqxdhRootDomain, input).

Definition protocol_symmetric_query
    (input : bool) : protocol_rom_query :=
  (kdf_domain_tag SymmetricRatchetDomain,
    (input, (false, (false, (false, false))))).

Lemma protocol_root_query_differs_from_symmetric_query
    (root_input : protocol_root_atom)
    (symmetric_input : bool) :
  protocol_root_query root_input !=
  protocol_symmetric_query symmetric_input.
Proof. reflexivity. Qed.

Definition protocol_root_answer
    (table : protocol_rom_table)
    (root_input : protocol_root_atom) : bool :=
  (table (protocol_root_query root_input)).1.

Definition protocol_initial_chain
    (table : protocol_rom_table)
    (root_input : protocol_root_atom) : bool :=
  let root := protocol_root_answer table root_input in
  (table (protocol_symmetric_query root)).2.1.

Definition protocol_hidden_pad_query
    (table : protocol_rom_table)
    (root_input : protocol_root_atom) : protocol_rom_query :=
  protocol_symmetric_query (protocol_initial_chain table root_input).

Definition protocol_record_pad
    (table : protocol_rom_table)
    (root_input : protocol_root_atom) : bool :=
  (table (protocol_hidden_pad_query table root_input)).1.

Definition protocol_flip_answer
    (answer : protocol_rom_answer) : protocol_rom_answer :=
  (negb answer.1, answer.2).

(** The coupling changes one table entry only: the first component returned at the table-dependent ratchet-step query. It leaves the root answer and the second component used to derive that query unchanged. *)
Definition protocol_flip_pad_table
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) : protocol_rom_table :=
  [ffun query =>
    if query == protocol_hidden_pad_query table root_input
    then protocol_flip_answer (table query)
    else table query].

Lemma protocol_flip_pad_table_at_hidden_query
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) :
  protocol_flip_pad_table root_input table
      (protocol_hidden_pad_query table root_input) =
  protocol_flip_answer
      (table (protocol_hidden_pad_query table root_input)).
Proof.
  by rewrite /protocol_flip_pad_table ffunE eqxx.
Qed.

Lemma protocol_flip_pad_table_away
    (root_input : protocol_root_atom)
    (table : protocol_rom_table)
    (query : protocol_rom_query) :
  query != protocol_hidden_pad_query table root_input ->
  protocol_flip_pad_table root_input table query = table query.
Proof.
  move=> query_differs.
  by rewrite /protocol_flip_pad_table ffunE (negbTE query_differs).
Qed.

Lemma protocol_flip_pad_table_preserves_answer_tail
    (root_input : protocol_root_atom)
    (table : protocol_rom_table)
    (query : protocol_rom_query) :
  (protocol_flip_pad_table root_input table query).2 =
  (table query).2.
Proof.
  rewrite /protocol_flip_pad_table ffunE.
  by case: ifP.
Qed.

Lemma protocol_flip_pad_table_preserves_root_answer
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) :
  protocol_root_answer (protocol_flip_pad_table root_input table)
      root_input =
  protocol_root_answer table root_input.
Proof.
  rewrite /protocol_root_answer.
  rewrite (protocol_flip_pad_table_away root_input table
    (protocol_root_query root_input)).
  - reflexivity.
  - exact: protocol_root_query_differs_from_symmetric_query.
Qed.

Lemma protocol_flip_pad_table_preserves_initial_chain
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) :
  protocol_initial_chain (protocol_flip_pad_table root_input table)
      root_input =
  protocol_initial_chain table root_input.
Proof.
  rewrite /protocol_initial_chain
    protocol_flip_pad_table_preserves_root_answer.
  exact (f_equal (@fst bool bool)
    (protocol_flip_pad_table_preserves_answer_tail root_input table
      (protocol_symmetric_query (protocol_root_answer table root_input)))).
Qed.

Lemma protocol_flip_pad_table_preserves_hidden_query
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) :
  protocol_hidden_pad_query (protocol_flip_pad_table root_input table)
      root_input =
  protocol_hidden_pad_query table root_input.
Proof.
  by rewrite /protocol_hidden_pad_query
    protocol_flip_pad_table_preserves_initial_chain.
Qed.

Lemma protocol_flip_pad_table_flips_record_pad
    (root_input : protocol_root_atom)
    (table : protocol_rom_table) :
  protocol_record_pad (protocol_flip_pad_table root_input table)
      root_input =
  negb (protocol_record_pad table root_input).
Proof.
  rewrite /protocol_record_pad
    protocol_flip_pad_table_preserves_hidden_query
    protocol_flip_pad_table_at_hidden_query /protocol_flip_answer /=.
  reflexivity.
Qed.

Lemma protocol_flip_pad_table_involutive
    (root_input : protocol_root_atom) :
  cancel (protocol_flip_pad_table root_input)
    (protocol_flip_pad_table root_input).
Proof.
  move=> table.
  apply/ffunP=> query.
  rewrite /protocol_flip_pad_table ffunE
    protocol_flip_pad_table_preserves_hidden_query ffunE.
  case query_is_hidden:
    (query == protocol_hidden_pad_query table root_input) => /=.
  - rewrite /protocol_flip_answer.
    case table_answer: (table query) => [first [second suffix]] /=.
    by rewrite negbK.
  - reflexivity.
Qed.

Lemma protocol_flip_pad_table_bijective
    (root_input : protocol_root_atom) :
  bijective (protocol_flip_pad_table root_input).
Proof.
  exists (protocol_flip_pad_table root_input).
  - exact: protocol_flip_pad_table_involutive.
  - exact: protocol_flip_pad_table_involutive.
Qed.

(** The hidden source jointly samples the honest ML-KEM contribution atom and a complete oracle table. The four classical-DH coordinates are fixed in [protocol_forward_root_atom], so the passive-quantum theorem does not rely on hiding them. This uniform one-bit atom is only a finite proof vehicle; no claim is made that it quantifies production entropy. *)
Definition protocol_rom_source :=
  (bool * protocol_rom_table)%type.

Definition protocol_default_rom_table : protocol_rom_table :=
  [ffun _ => (false, (false, false))].

Definition protocol_default_rom_source : protocol_rom_source :=
  (false, protocol_default_rom_table).

Definition protocol_uniform_hidden_source :
    {distr protocol_rom_source / R} :=
  @uniform_F _ protocol_default_rom_source.

Definition protocol_flip_hidden_source
    (source : protocol_rom_source) : protocol_rom_source :=
  (source.1,
    protocol_flip_pad_table (protocol_forward_root_atom source.1) source.2).

Lemma protocol_flip_hidden_source_involutive :
  cancel protocol_flip_hidden_source protocol_flip_hidden_source.
Proof.
  move=> [hidden_mlkem_contribution table].
  rewrite /protocol_flip_hidden_source /=
    protocol_flip_pad_table_involutive.
  reflexivity.
Qed.

Lemma protocol_flip_hidden_source_bijective :
  bijective protocol_flip_hidden_source.
Proof.
  exists protocol_flip_hidden_source.
  - exact protocol_flip_hidden_source_involutive.
  - exact protocol_flip_hidden_source_involutive.
Qed.

Lemma protocol_uniform_hidden_source_event_reindex
    (event : pred protocol_rom_source) :
  \P_[ protocol_uniform_hidden_source ] event =
  \P_[ protocol_uniform_hidden_source ]
    (fun source => event (protocol_flip_hidden_source source)).
Proof.
  rewrite /pr.
  have flip_reindex :
    psum (fun source : protocol_rom_source =>
      ((nat_of_bool (event source))%:R *
        protocol_uniform_hidden_source source : R)) =
    psum (fun source : protocol_rom_source =>
      ((nat_of_bool (event (protocol_flip_hidden_source source)))%:R *
        protocol_uniform_hidden_source
          (protocol_flip_hidden_source source) : R)).
  {
    apply: reindex_psum.
    - by move=> source _.
    - exists protocol_flip_hidden_source.
      + by move=> source _; apply: protocol_flip_hidden_source_involutive.
      + by move=> source _; apply: protocol_flip_hidden_source_involutive.
  }
  rewrite flip_reindex.
  apply: eq_psum=> source.
  congr (_ * _).
Qed.

Definition protocol_challenge_ciphertext
    (challenge : bool)
    (source : protocol_rom_source) : bool :=
  xorb challenge
    (protocol_record_pad source.2 (protocol_forward_root_atom source.1)).

Lemma protocol_challenge_ciphertext_flip_coupling
    (source : protocol_rom_source) :
  protocol_challenge_ciphertext false source =
  protocol_challenge_ciphertext true
    (protocol_flip_hidden_source source).
Proof.
  case: source=> hidden_mlkem_contribution table.
  rewrite /protocol_challenge_ciphertext /protocol_flip_hidden_source /=
    protocol_flip_pad_table_flips_record_pad.
  by case: (protocol_record_pad table
    (protocol_forward_root_atom hidden_mlkem_contribution)).
Qed.

Definition protocol_trace_queries_hidden_pad
  (source : protocol_rom_source)
    (trace : protocol_rom_trace) : bool :=
  has (fun entry =>
    entry.1 == protocol_hidden_pad_query source.2
      (protocol_forward_root_atom source.1)) trace.

Section BoundedAttacker.

  Variable result : choiceType.

  Definition protocol_rom_view :=
    (bool * rom_observation protocol_rom_query protocol_rom_answer result)%type.

  Definition protocol_bounded_rom_view
      (fuel : nat)
      (challenge : bool)
      (source : protocol_rom_source)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result) :
      protocol_rom_view :=
    let ciphertext := protocol_challenge_ciphertext challenge source in
    (ciphertext,
      run_bounded_rom protocol_rom_query protocol_rom_answer fuel source.2
        (program ciphertext)).

  Definition protocol_rejected_view : protocol_rom_view :=
    (false, (None, [::])).

  Lemma protocol_bounded_runs_agree_without_pad_query
      (fuel : nat)
      (source : protocol_rom_source)
      (program : rom_tree protocol_rom_query protocol_rom_answer result) :
    ~~ protocol_trace_queries_hidden_pad source
      (run_bounded_rom protocol_rom_query protocol_rom_answer fuel source.2
        program).2 ->
    run_bounded_rom protocol_rom_query protocol_rom_answer fuel
      (protocol_flip_hidden_source source).2 program =
    run_bounded_rom protocol_rom_query protocol_rom_answer fuel source.2
      program.
  Proof.
    case: source=> hidden_mlkem_contribution table /=.
    revert program.
    induction fuel as [| fuel induction_hypothesis];
      intros [value | query next]; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite /protocol_trace_queries_hidden_pad /=.
      move=> /norP [query_differs tail_avoids_hidden].
      rewrite (protocol_flip_pad_table_away
        (protocol_forward_root_atom hidden_mlkem_contribution) table query
        query_differs).
      rewrite (induction_hypothesis
        (next (table query)) tail_avoids_hidden).
      reflexivity.
  Qed.

  Definition protocol_rom_bad_event
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (source : protocol_rom_source) : bool :=
    protocol_trace_queries_hidden_pad source
      (protocol_bounded_rom_view fuel false source program).2.2.

  Lemma protocol_coupled_views_agree_without_pad_query
      (fuel : nat)
      (source : protocol_rom_source)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result) :
    ~~ protocol_rom_bad_event fuel program source ->
    protocol_bounded_rom_view fuel false source program =
    protocol_bounded_rom_view fuel true
      (protocol_flip_hidden_source source) program.
  Proof.
    move=> avoids_hidden.
    have ciphertexts_equal :=
      protocol_challenge_ciphertext_flip_coupling source.
    rewrite /protocol_bounded_rom_view.
    rewrite -ciphertexts_equal.
    congr (_, _).
    symmetry.
    apply: protocol_bounded_runs_agree_without_pad_query.
    move: avoids_hidden.
    by rewrite /protocol_rom_bad_event /protocol_bounded_rom_view.
  Qed.

  Definition protocol_rom_decision_event
      (fuel : nat)
      (challenge : bool)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool)
      (source : protocol_rom_source) : bool :=
    distinguisher
      (protocol_bounded_rom_view fuel challenge source program).

  Definition protocol_rom_coupled_mismatch_event
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool)
      (source : protocol_rom_source) : bool :=
    protocol_rom_decision_event fuel false program distinguisher source !=
    protocol_rom_decision_event fuel true program distinguisher
      (protocol_flip_hidden_source source).

  Lemma protocol_rom_mismatch_implies_hidden_pad_query
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    {subset protocol_rom_coupled_mismatch_event fuel program distinguisher <=
      protocol_rom_bad_event fuel program}.
  Proof.
    move=> source decisions_differ.
    case bad_query: (protocol_rom_bad_event fuel program source) => //.
    have views_equal := protocol_coupled_views_agree_without_pad_query
      fuel source program.
    have avoids_hidden : ~~ protocol_rom_bad_event fuel program source.
    { by rewrite bad_query. }
    have decisions_equal :
      protocol_rom_decision_event fuel false program distinguisher source =
      protocol_rom_decision_event fuel true program distinguisher
        (protocol_flip_hidden_source source).
    {
      rewrite /protocol_rom_decision_event.
      exact (f_equal distinguisher (views_equal avoids_hidden)).
    }
    rewrite /protocol_rom_coupled_mismatch_event in decisions_differ.
    move/negP: decisions_differ=> decisions_not_equal.
    have decisions_same :
      protocol_rom_decision_event fuel false program distinguisher source ==
      protocol_rom_decision_event fuel true program distinguisher
        (protocol_flip_hidden_source source).
    { exact/eqP. }
    have impossible : False := decisions_not_equal decisions_same.
    by case: impossible.
  Qed.

  Definition protocol_rom_decision_probability
      (fuel : nat)
      (challenge : bool)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) : R :=
    \P_[ protocol_uniform_hidden_source ]
      (protocol_rom_decision_event fuel challenge program distinguisher).

  Definition protocol_rom_advantage
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) : R :=
    `| protocol_rom_decision_probability fuel false program distinguisher -
        protocol_rom_decision_probability fuel true program distinguisher |.

  Definition protocol_rom_bad_probability
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result) : R :=
    \P_[ protocol_uniform_hidden_source ]
      (protocol_rom_bad_event fuel program).

  Lemma protocol_same_source_decision_difference_bound
      (left_decision right_decision : pred protocol_rom_source) :
    `| \P_[ protocol_uniform_hidden_source ] left_decision -
        \P_[ protocol_uniform_hidden_source ] right_decision | <=
    \P_[ protocol_uniform_hidden_source ]
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
        \P_[ protocol_uniform_hidden_source ] left_decision <=
        \P_[ protocol_uniform_hidden_source ] right_decision +
        \P_[ protocol_uniform_hidden_source ] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ protocol_uniform_hidden_source ]
          [predU right_decision & mismatch])).
      exact: subset_pr left_in_union.
      exact: ler_pr_or.
    }
    have right_le :
        \P_[ protocol_uniform_hidden_source ] right_decision <=
        \P_[ protocol_uniform_hidden_source ] left_decision +
        \P_[ protocol_uniform_hidden_source ] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ protocol_uniform_hidden_source ]
          [predU left_decision & mismatch])).
      exact: subset_pr right_in_union.
      exact: ler_pr_or.
    }
    rewrite ler_norml.
    apply/andP; split.
    - rewrite lerBrDr.
      rewrite [(- \P_[ protocol_uniform_hidden_source ] mismatch +
        \P_[ protocol_uniform_hidden_source ] right_decision)]addrC.
      by rewrite lerBlDr.
    - rewrite lerBlDr
        [\P_[ protocol_uniform_hidden_source ] mismatch + _]addrC.
      exact: left_le.
  Qed.

  (** Main attacker-facing ROM theorem. It quantifies over every bounded adaptive classical query tree and every deterministic decision rule. The right-hand event names the exact table-dependent symmetric-ratchet query whose first answer component is the challenge pad. *)
  Theorem pqxdh_ratchet_bounded_rom_confidentiality_bound
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_rom_advantage fuel program distinguisher <=
    protocol_rom_bad_probability fuel program.
  Proof.
    rewrite /protocol_rom_advantage /protocol_rom_decision_probability.
    rewrite (protocol_uniform_hidden_source_event_reindex
      (protocol_rom_decision_event fuel true program distinguisher)).
    apply/(@le_trans _ _
      (\P_[ protocol_uniform_hidden_source ]
        (protocol_rom_coupled_mismatch_event fuel program distinguisher))).
    - exact: protocol_same_source_decision_difference_bound.
    - rewrite /protocol_rom_bad_probability.
      exact: subset_pr
        (protocol_rom_mismatch_implies_hidden_pad_query
          fuel program distinguisher).
  Qed.

  (** Only the three hidden-root forwarding scenarios and the rejected active-classical replacement inhabit this type. Active-quantum replacement is deliberately unrepresentable here; its known substituted input and advantage-one attack belong exclusively to [PqxdhRatchetGames]. *)
  Inductive protocol_supported_scenario : Type :=
  | ActiveClassicalForwardScenario
  | ActiveClassicalReplaceScenario
  | PassiveClassicalForwardScenario
  | PassiveQuantumForwardScenario.

  Definition protocol_supported_model
      (scenario : protocol_supported_scenario) : attacker_model :=
    match scenario with
    | ActiveClassicalForwardScenario => active_classical
    | ActiveClassicalReplaceScenario => active_classical
    | PassiveClassicalForwardScenario => passive_classical
    | PassiveQuantumForwardScenario => passive_quantum
    end.

  Definition protocol_supported_action
      (scenario : protocol_supported_scenario) : network_action :=
    match scenario with
    | ActiveClassicalForwardScenario => Forward
    | ActiveClassicalReplaceScenario => Replace
    | PassiveClassicalForwardScenario => Forward
    | PassiveQuantumForwardScenario => Forward
    end.

  Definition active_classical_supported_scenario
      (action : network_action) : protocol_supported_scenario :=
    match action with
    | Forward => ActiveClassicalForwardScenario
    | Replace => ActiveClassicalReplaceScenario
    end.

  (** This checked bridge records the hidden-root capability premise for every scenario supported by the wrapper. In the passive-quantum case it reduces to the ideal assumption that honest ML-KEM decapsulation remains opaque. *)
  Lemma protocol_supported_scenario_root_hidden
      (scenario : protocol_supported_scenario) :
    attacker_can_recompute_accepted_root_input
      (protocol_supported_model scenario)
      (protocol_supported_action scenario) = false.
  Proof. by case: scenario. Qed.

  (** Accepted supported actions expose the bounded ROM challenge; the one rejected replacement exposes a fixed failure view and makes no oracle query. *)
  Definition protocol_scenario_decision_event
      (scenario : protocol_supported_scenario)
      (fuel : nat)
      (challenge : bool)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool)
      (source : protocol_rom_source) : bool :=
    if ideal_bundle_authentication_accepts
         (protocol_supported_model scenario)
         (protocol_supported_action scenario)
    then protocol_rom_decision_event fuel challenge program distinguisher source
    else distinguisher protocol_rejected_view.

  Definition protocol_scenario_decision_probability
      (scenario : protocol_supported_scenario)
      (fuel : nat)
      (challenge : bool)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) : R :=
    \P_[ protocol_uniform_hidden_source ]
      (protocol_scenario_decision_event scenario fuel challenge program
        distinguisher).

  Definition protocol_scenario_advantage
      (scenario : protocol_supported_scenario)
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) : R :=
    `| protocol_scenario_decision_probability scenario fuel false program
          distinguisher -
        protocol_scenario_decision_probability scenario fuel true program
          distinguisher |.

  Theorem active_classical_forward_bounded_rom_confidentiality
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_scenario_advantage ActiveClassicalForwardScenario fuel program
      distinguisher <=
    protocol_rom_bad_probability fuel program.
  Proof.
    change (protocol_rom_advantage fuel program distinguisher <=
      protocol_rom_bad_probability fuel program).
    exact: pqxdh_ratchet_bounded_rom_confidentiality_bound.
  Qed.

  Theorem passive_classical_forward_bounded_rom_confidentiality
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_scenario_advantage PassiveClassicalForwardScenario fuel program
      distinguisher <=
    protocol_rom_bad_probability fuel program.
  Proof.
    change (protocol_rom_advantage fuel program distinguisher <=
      protocol_rom_bad_probability fuel program).
    exact: pqxdh_ratchet_bounded_rom_confidentiality_bound.
  Qed.

  (** "Quantum" here imports only the passive post-quantum capability split from [PqxdhRatchetGames]. Oracle interaction remains the classical query tree above. *)
  Theorem passive_quantum_classical_query_forward_confidentiality
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_scenario_advantage PassiveQuantumForwardScenario fuel program
      distinguisher <=
    protocol_rom_bad_probability fuel program.
  Proof.
    change (protocol_rom_advantage fuel program distinguisher <=
      protocol_rom_bad_probability fuel program).
    exact: pqxdh_ratchet_bounded_rom_confidentiality_bound.
  Qed.

  Theorem active_classical_replace_fixed_failure_confidentiality
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_scenario_advantage ActiveClassicalReplaceScenario fuel program
      distinguisher = 0.
  Proof.
    rewrite /protocol_scenario_advantage
      /protocol_scenario_decision_probability
      /protocol_scenario_decision_event /=.
    by rewrite GRing.subrr normr0.
  Qed.

  Theorem active_classical_all_actions_bounded_rom_confidentiality
      (action : network_action)
      (fuel : nat)
      (program : bool ->
        rom_tree protocol_rom_query protocol_rom_answer result)
      (distinguisher : protocol_rom_view -> bool) :
    protocol_scenario_advantage
      (active_classical_supported_scenario action) fuel program
      distinguisher <=
    protocol_rom_bad_probability fuel program.
  Proof.
    case: action.
    - exact: active_classical_forward_bounded_rom_confidentiality.
    - rewrite active_classical_replace_fixed_failure_confidentiality
        /protocol_rom_bad_probability.
      exact: ge0_pr.
  Qed.

End BoundedAttacker.

Print Assumptions protocol_flip_pad_table_involutive.
Print Assumptions protocol_uniform_hidden_source_event_reindex.
Print Assumptions protocol_bounded_runs_agree_without_pad_query.
Print Assumptions protocol_rom_mismatch_implies_hidden_pad_query.
Print Assumptions protocol_supported_scenario_root_hidden.
Print Assumptions pqxdh_ratchet_bounded_rom_confidentiality_bound.
Print Assumptions active_classical_forward_bounded_rom_confidentiality.
Print Assumptions passive_classical_forward_bounded_rom_confidentiality.
Print Assumptions passive_quantum_classical_query_forward_confidentiality.
Print Assumptions active_classical_replace_fixed_failure_confidentiality.
Print Assumptions active_classical_all_actions_bounded_rom_confidentiality.
