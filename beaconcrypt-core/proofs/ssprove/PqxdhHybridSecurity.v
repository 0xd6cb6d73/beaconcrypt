(* SPDX-License-Identifier: 0BSD *)

(** A finite classical-ROM robustness game for the ideal PQXDH hybrid combiner.

    One selected contribution to the ordered four-DH-plus-ML-KEM root input is sampled secretly, while every other contribution is fixed and may be known to the adversary. A bounded deterministic adversary receives one challenge bit masked by the ideal root-oracle output and adaptive access to the modeled oracle. Distinguishing the two challenge bits is reduced to querying the modeled five-coordinate input containing the hidden contribution.

    This is a protocol-core hybrid-combiner hop, not a real-or-random theorem for the production root key. It preserves the variable contribution order but collapses the fixed padding, HKDF-SHA-512 Extract/Expand calls, and [PQXDH_INFO] into constants and one ideal lookup. It assumes ideal random-oracle behavior and the capability classifications imported from [PqxdhRatchetGames]. It does not prove primitive correctness, a production-width guessing bound, persistence or rollback properties, multi-session composition, QPT security, or QROM security. *)

From Stdlib Require Import Utf8 Arith.PeanoNat btauto.Btauto.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum order eqtype choice fintype finfun seq all_algebra reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom PqxdhRatchetGames.

Import Num.Theory.
Import Order.POrderTheory.
Import GRing.Theory.

Local Open Scope ring_scope.

Inductive pqxdh_hybrid_component : Type :=
| HybridDh1
| HybridDh2
| HybridDh3
| HybridDh4
| HybridMlKem.

Definition pqxdh_hybrid_root_atom :=
  (bool * (bool * (bool * (bool * bool))))%type.

Definition pqxdh_hybrid_root_atom_of_input
    (input : pqxdh_root_input) : pqxdh_hybrid_root_atom :=
  (dh1_contribution input,
    (dh2_contribution input,
      (dh3_contribution input,
        (dh4_contribution input, mlkem_contribution input)))).

(** Replace exactly one coordinate and retain the production root-input order. The remaining coordinates are explicit public parameters of the game. *)
Definition pqxdh_hybrid_root_atom_with_hidden
    (component : pqxdh_hybrid_component)
    (hidden : bool)
    (public_input : pqxdh_root_input) : pqxdh_hybrid_root_atom :=
  match component with
  | HybridDh1 =>
      (hidden,
        (dh2_contribution public_input,
          (dh3_contribution public_input,
            (dh4_contribution public_input,
              mlkem_contribution public_input))))
  | HybridDh2 =>
      (dh1_contribution public_input,
        (hidden,
          (dh3_contribution public_input,
            (dh4_contribution public_input,
              mlkem_contribution public_input))))
  | HybridDh3 =>
      (dh1_contribution public_input,
        (dh2_contribution public_input,
          (hidden,
            (dh4_contribution public_input,
              mlkem_contribution public_input))))
  | HybridDh4 =>
      (dh1_contribution public_input,
        (dh2_contribution public_input,
          (dh3_contribution public_input,
            (hidden, mlkem_contribution public_input))))
  | HybridMlKem =>
      (dh1_contribution public_input,
        (dh2_contribution public_input,
          (dh3_contribution public_input,
            (dh4_contribution public_input, hidden))))
  end.

Lemma pqxdh_hybrid_hidden_coordinate_injective
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input) :
  pqxdh_hybrid_root_atom_with_hidden component false public_input !=
  pqxdh_hybrid_root_atom_with_hidden component true public_input.
Proof.
  case: component; case: public_input=> [] [] [] [] [] //.
Qed.

(** The first bit is a handwritten abstraction of the genuinely distinct [PQXDH_INFO] and [SYM_RATCHET_INFO] labels. It does not serialize those production strings or prove an extraction-linked domain-separation equality. Production session separation must arise from the root input itself, so this model adds no session tag. *)
Definition pqxdh_hybrid_rom_query :=
  (bool * pqxdh_hybrid_root_atom)%type.

Definition pqxdh_hybrid_rom_table :=
  rom_table pqxdh_hybrid_rom_query bool.

Definition pqxdh_hybrid_rom_trace :=
  rom_trace pqxdh_hybrid_rom_query bool.

Definition pqxdh_hybrid_root_query
    (input : pqxdh_hybrid_root_atom) : pqxdh_hybrid_rom_query :=
  (false, input).

Definition pqxdh_hybrid_ratchet_query
    (chain : bool) : pqxdh_hybrid_rom_query :=
  (true, (chain, (false, (false, (false, false))))).

Lemma pqxdh_hybrid_domains_are_separated
    (chain : bool)
    (root_input : pqxdh_hybrid_root_atom) :
  pqxdh_hybrid_root_query root_input !=
  pqxdh_hybrid_ratchet_query chain.
Proof. reflexivity. Qed.

Lemma pqxdh_hybrid_hidden_root_queries_are_distinct
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input) :
  pqxdh_hybrid_root_query
      (pqxdh_hybrid_root_atom_with_hidden component false public_input) !=
  pqxdh_hybrid_root_query
      (pqxdh_hybrid_root_atom_with_hidden component true public_input).
Proof.
  case: component; case: public_input=> [] [] [] [] [] //.
Qed.

(** Capability bookkeeping is deliberately separate from the ROM theorem. A classical compromise is represented by [quantum_recovers_classical_secrets]; honest and attacker-selected ML-KEM contributions use their corresponding decapsulation capabilities. *)
Definition pqxdh_hybrid_component_remains_hidden
    (model : attacker_model)
    (action : network_action)
    (component : pqxdh_hybrid_component) : bool :=
  match component with
  | HybridDh1 | HybridDh2 | HybridDh3 | HybridDh4 =>
      negb (quantum_recovers_classical_secrets model)
  | HybridMlKem =>
      match action with
      | Forward => negb (can_decapsulate_honest_mlkem model)
      | Replace => negb (can_decapsulate_selected_mlkem model action)
      end
  end.

Definition pqxdh_hybrid_component_is_classical
    (component : pqxdh_hybrid_component) : bool :=
  match component with
  | HybridDh1 | HybridDh2 | HybridDh3 | HybridDh4 => true
  | HybridMlKem => false
  end.

Lemma active_classical_forward_mlkem_remains_hidden :
  pqxdh_hybrid_component_remains_hidden active_classical Forward HybridMlKem =
  true.
Proof. reflexivity. Qed.

Lemma passive_classical_forward_mlkem_remains_hidden :
  pqxdh_hybrid_component_remains_hidden passive_classical Forward HybridMlKem =
  true.
Proof. reflexivity. Qed.

Lemma passive_quantum_forward_mlkem_remains_hidden :
  pqxdh_hybrid_component_remains_hidden passive_quantum Forward HybridMlKem =
  true.
Proof. reflexivity. Qed.

Lemma passive_quantum_classical_components_are_exposed
    (component : pqxdh_hybrid_component) :
  pqxdh_hybrid_component_is_classical component = true ->
  pqxdh_hybrid_component_remains_hidden passive_quantum Forward component =
  false.
Proof. by case: component. Qed.

Lemma active_quantum_replace_has_no_hidden_hybrid_component
    (component : pqxdh_hybrid_component) :
  pqxdh_hybrid_component_remains_hidden active_quantum Replace component =
  false.
Proof. by case: component. Qed.

Definition pqxdh_hybrid_source :=
  (bool * pqxdh_hybrid_rom_table)%type.

Definition pqxdh_hybrid_default_table : pqxdh_hybrid_rom_table :=
  [ffun _ => false].

Definition pqxdh_hybrid_default_source : pqxdh_hybrid_source :=
  (false, pqxdh_hybrid_default_table).

Definition pqxdh_hybrid_uniform_source :
    {distr pqxdh_hybrid_source / R} :=
  @uniform_F _ pqxdh_hybrid_default_source.

Definition pqxdh_hybrid_secret_query
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) : pqxdh_hybrid_rom_query :=
  pqxdh_hybrid_root_query
    (pqxdh_hybrid_root_atom_with_hidden component source.1 public_input).

Definition pqxdh_hybrid_root_answer
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) : bool :=
  source.2 (pqxdh_hybrid_secret_query component public_input source).

Definition pqxdh_hybrid_flip_table
    (secret_query : pqxdh_hybrid_rom_query)
    (table : pqxdh_hybrid_rom_table) : pqxdh_hybrid_rom_table :=
  [ffun query =>
    if query == secret_query then negb (table query) else table query].

Lemma pqxdh_hybrid_flip_table_at_secret
    (secret_query : pqxdh_hybrid_rom_query)
    (table : pqxdh_hybrid_rom_table) :
  pqxdh_hybrid_flip_table secret_query table secret_query =
  negb (table secret_query).
Proof. by rewrite /pqxdh_hybrid_flip_table ffunE eqxx. Qed.

Lemma pqxdh_hybrid_flip_table_away
    (secret_query query : pqxdh_hybrid_rom_query)
    (table : pqxdh_hybrid_rom_table) :
  query != secret_query ->
  pqxdh_hybrid_flip_table secret_query table query = table query.
Proof.
  move=> queries_differ.
  by rewrite /pqxdh_hybrid_flip_table ffunE (negbTE queries_differ).
Qed.

Lemma pqxdh_hybrid_flip_table_involutive
    (secret_query : pqxdh_hybrid_rom_query) :
  cancel (pqxdh_hybrid_flip_table secret_query)
    (pqxdh_hybrid_flip_table secret_query).
Proof.
  move=> table.
  apply/ffunP=> query.
  rewrite /pqxdh_hybrid_flip_table !ffunE.
  case: (query == secret_query) => //=.
  by rewrite negbK.
Qed.

Definition pqxdh_hybrid_flip_source
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) : pqxdh_hybrid_source :=
  (source.1,
    pqxdh_hybrid_flip_table
      (pqxdh_hybrid_secret_query component public_input source)
      source.2).

Lemma pqxdh_hybrid_flip_source_preserves_secret_query
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) :
  pqxdh_hybrid_secret_query component public_input
      (pqxdh_hybrid_flip_source component public_input source) =
  pqxdh_hybrid_secret_query component public_input source.
Proof. reflexivity. Qed.

Lemma pqxdh_hybrid_flip_source_involutive
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input) :
  cancel (pqxdh_hybrid_flip_source component public_input)
    (pqxdh_hybrid_flip_source component public_input).
Proof.
  move=> [hidden table].
  rewrite /pqxdh_hybrid_flip_source /=
    pqxdh_hybrid_flip_table_involutive.
  reflexivity.
Qed.

Lemma pqxdh_hybrid_uniform_source_event_reindex
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (event : pred pqxdh_hybrid_source) :
  \P_[ pqxdh_hybrid_uniform_source ] event =
  \P_[ pqxdh_hybrid_uniform_source ]
    (fun source => event
      (pqxdh_hybrid_flip_source component public_input source)).
Proof.
  rewrite /pr.
  have flip_reindex :
    psum (fun source : pqxdh_hybrid_source =>
      ((nat_of_bool (event source))%:R *
        pqxdh_hybrid_uniform_source source : R)) =
    psum (fun source : pqxdh_hybrid_source =>
      ((nat_of_bool (event
        (pqxdh_hybrid_flip_source component public_input source)))%:R *
        pqxdh_hybrid_uniform_source
          (pqxdh_hybrid_flip_source component public_input source) : R)).
  {
    apply: reindex_psum.
    - by move=> source _.
    - exists (pqxdh_hybrid_flip_source component public_input).
      + by move=> source _; apply:
          pqxdh_hybrid_flip_source_involutive.
      + by move=> source _; apply:
          pqxdh_hybrid_flip_source_involutive.
  }
  rewrite flip_reindex.
  apply: eq_psum=> source.
  congr (_ * _).
Qed.

Definition pqxdh_hybrid_challenge
    (component : pqxdh_hybrid_component)
    (challenge : bool)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) : bool :=
  xorb challenge
    (pqxdh_hybrid_root_answer component public_input source).

Lemma pqxdh_hybrid_challenge_flip_coupling
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source) :
  pqxdh_hybrid_challenge component false public_input source =
  pqxdh_hybrid_challenge component true public_input
    (pqxdh_hybrid_flip_source component public_input source).
Proof.
  case: source=> hidden table.
  rewrite /pqxdh_hybrid_challenge /pqxdh_hybrid_root_answer
    /pqxdh_hybrid_flip_source /=
    pqxdh_hybrid_flip_table_at_secret.
  by case: (table
    (pqxdh_hybrid_secret_query component public_input
      (hidden, table))).
Qed.

Definition pqxdh_hybrid_trace_queries_secret
    (component : pqxdh_hybrid_component)
    (public_input : pqxdh_root_input)
    (source : pqxdh_hybrid_source)
    (trace : pqxdh_hybrid_rom_trace) : bool :=
  has (fun entry => entry.1 ==
    pqxdh_hybrid_secret_query component public_input source) trace.

Section BoundedHybridAdversary.

  Variable result : choiceType.

  Definition pqxdh_hybrid_view :=
    (bool * rom_observation pqxdh_hybrid_rom_query bool result)%type.

  Definition pqxdh_hybrid_bounded_view
      (component : pqxdh_hybrid_component)
      (challenge : bool)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (source : pqxdh_hybrid_source)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result) :
      pqxdh_hybrid_view :=
    let root_challenge :=
      pqxdh_hybrid_challenge component challenge public_input source in
    (root_challenge,
      run_bounded_rom pqxdh_hybrid_rom_query bool fuel source.2
        (program root_challenge)).

  Lemma pqxdh_hybrid_runs_agree_without_secret_query
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (source : pqxdh_hybrid_source)
      (program : rom_tree pqxdh_hybrid_rom_query bool result) :
    ~~ pqxdh_hybrid_trace_queries_secret component public_input source
      (run_bounded_rom pqxdh_hybrid_rom_query bool fuel source.2 program).2 ->
    run_bounded_rom pqxdh_hybrid_rom_query bool fuel
      (pqxdh_hybrid_flip_source component public_input source).2
      program =
    run_bounded_rom pqxdh_hybrid_rom_query bool fuel source.2 program.
  Proof.
    case: source=> hidden table /=.
    revert program.
    induction fuel as [| fuel induction_hypothesis];
      intros [value | query next]; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite /pqxdh_hybrid_trace_queries_secret /=.
      move=> /norP [query_differs tail_avoids_secret].
      rewrite (pqxdh_hybrid_flip_table_away
        (pqxdh_hybrid_secret_query component public_input
          (hidden, table)) query table query_differs).
      rewrite (induction_hypothesis
        (next (table query)) tail_avoids_secret).
      reflexivity.
  Qed.

  Definition pqxdh_hybrid_bad_event
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (source : pqxdh_hybrid_source) : bool :=
    pqxdh_hybrid_trace_queries_secret component public_input source
      (pqxdh_hybrid_bounded_view component false public_input fuel
        source program).2.2.

  Lemma pqxdh_hybrid_coupled_views_agree_without_bad
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (source : pqxdh_hybrid_source)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result) :
    ~~ pqxdh_hybrid_bad_event component public_input fuel program
      source ->
    pqxdh_hybrid_bounded_view component false public_input fuel
      source program =
    pqxdh_hybrid_bounded_view component true public_input fuel
      (pqxdh_hybrid_flip_source component public_input source) program.
  Proof.
    move=> avoids_secret.
    have challenges_equal :=
      pqxdh_hybrid_challenge_flip_coupling component public_input source.
    rewrite /pqxdh_hybrid_bounded_view.
    rewrite -challenges_equal.
    congr (_, _).
    symmetry.
    apply: pqxdh_hybrid_runs_agree_without_secret_query.
    move: avoids_secret.
    by rewrite /pqxdh_hybrid_bad_event /pqxdh_hybrid_bounded_view.
  Qed.

  Definition pqxdh_hybrid_decision_event
      (component : pqxdh_hybrid_component)
      (challenge : bool)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool)
      (source : pqxdh_hybrid_source) : bool :=
    distinguisher
      (pqxdh_hybrid_bounded_view component challenge public_input fuel
        source program).

  Definition pqxdh_hybrid_coupled_mismatch_event
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool)
      (source : pqxdh_hybrid_source) : bool :=
    pqxdh_hybrid_decision_event component false public_input fuel
      program distinguisher source !=
    pqxdh_hybrid_decision_event component true public_input fuel
      program distinguisher
      (pqxdh_hybrid_flip_source component public_input source).

  Lemma pqxdh_hybrid_mismatch_implies_bad
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) :
    {subset
      pqxdh_hybrid_coupled_mismatch_event component public_input fuel
        program distinguisher <=
      pqxdh_hybrid_bad_event component public_input fuel program}.
  Proof.
    move=> source decisions_differ.
    case bad_query:
      (pqxdh_hybrid_bad_event component public_input fuel program
        source) => //.
    have avoids_secret :
        ~~ pqxdh_hybrid_bad_event component public_input fuel program
          source.
    { by rewrite bad_query. }
    have views_equal := pqxdh_hybrid_coupled_views_agree_without_bad
      component public_input fuel source program avoids_secret.
    have decisions_equal :
      pqxdh_hybrid_decision_event component false public_input fuel
        program distinguisher source =
      pqxdh_hybrid_decision_event component true public_input fuel
        program distinguisher
        (pqxdh_hybrid_flip_source component public_input source).
    {
      rewrite /pqxdh_hybrid_decision_event.
      exact (f_equal distinguisher views_equal).
    }
    rewrite /pqxdh_hybrid_coupled_mismatch_event in decisions_differ.
    move/negP: decisions_differ=> decisions_not_equal.
    have decisions_same :
      pqxdh_hybrid_decision_event component false public_input fuel
        program distinguisher source ==
      pqxdh_hybrid_decision_event component true public_input fuel
        program distinguisher
        (pqxdh_hybrid_flip_source component public_input source).
    { exact/eqP. }
    have impossible : False := decisions_not_equal decisions_same.
    by case: impossible.
  Qed.

  Definition pqxdh_hybrid_decision_probability
      (component : pqxdh_hybrid_component)
      (challenge : bool)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) : R :=
    \P_[ pqxdh_hybrid_uniform_source ]
      (pqxdh_hybrid_decision_event component challenge public_input
        fuel program distinguisher).

  Definition pqxdh_hybrid_advantage
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) : R :=
    `| pqxdh_hybrid_decision_probability component false public_input
          fuel program distinguisher -
        pqxdh_hybrid_decision_probability component true public_input
          fuel program distinguisher |.

  Definition pqxdh_hybrid_bad_probability
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result) : R :=
    \P_[ pqxdh_hybrid_uniform_source ]
      (pqxdh_hybrid_bad_event component public_input fuel program).

  Lemma pqxdh_hybrid_same_source_decision_difference_bound
      (left_decision right_decision : pred pqxdh_hybrid_source) :
    `| \P_[ pqxdh_hybrid_uniform_source ] left_decision -
        \P_[ pqxdh_hybrid_uniform_source ] right_decision | <=
    \P_[ pqxdh_hybrid_uniform_source ]
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
        \P_[ pqxdh_hybrid_uniform_source ] left_decision <=
        \P_[ pqxdh_hybrid_uniform_source ] right_decision +
        \P_[ pqxdh_hybrid_uniform_source ] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ pqxdh_hybrid_uniform_source ]
          [predU right_decision & mismatch])).
      exact: subset_pr left_in_union.
      exact: ler_pr_or.
    }
    have right_le :
        \P_[ pqxdh_hybrid_uniform_source ] right_decision <=
        \P_[ pqxdh_hybrid_uniform_source ] left_decision +
        \P_[ pqxdh_hybrid_uniform_source ] mismatch.
    {
      apply/(@le_trans _ _
        (\P_[ pqxdh_hybrid_uniform_source ]
          [predU left_decision & mismatch])).
      exact: subset_pr right_in_union.
      exact: ler_pr_or.
    }
    rewrite ler_norml.
    apply/andP; split.
    - rewrite lerBrDr.
      rewrite [(- \P_[ pqxdh_hybrid_uniform_source ] mismatch +
        \P_[ pqxdh_hybrid_uniform_source ] right_decision)]addrC.
      by rewrite lerBlDr.
    - rewrite lerBlDr
        [\P_[ pqxdh_hybrid_uniform_source ] mismatch + _]addrC.
      exact: left_le.
  Qed.

  (** Main structural robustness theorem for a root-derived one-bit mask: all non-selected contributions may be public, and the selected contribution may be any of the five modeled PQXDH coordinates. *)
  Theorem pqxdh_hybrid_one_hidden_contribution_confidentiality
      (component : pqxdh_hybrid_component)
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) :
    pqxdh_hybrid_advantage component public_input fuel program
      distinguisher <=
    pqxdh_hybrid_bad_probability component public_input fuel program.
  Proof.
    rewrite /pqxdh_hybrid_advantage
      /pqxdh_hybrid_decision_probability.
    rewrite (pqxdh_hybrid_uniform_source_event_reindex component public_input
      (pqxdh_hybrid_decision_event component true public_input fuel
        program distinguisher)).
    apply/(@le_trans _ _
      (\P_[ pqxdh_hybrid_uniform_source ]
        (pqxdh_hybrid_coupled_mismatch_event component public_input
          fuel program distinguisher))).
    - exact: pqxdh_hybrid_same_source_decision_difference_bound.
    - rewrite /pqxdh_hybrid_bad_probability.
      exact: subset_pr
        (pqxdh_hybrid_mismatch_implies_bad component public_input fuel
          program distinguisher).
  Qed.

  Theorem active_classical_forward_hybrid_confidentiality
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) :
    pqxdh_hybrid_component_remains_hidden active_classical Forward
        HybridMlKem = true /\
    pqxdh_hybrid_advantage HybridMlKem public_input fuel program
        distinguisher <=
      pqxdh_hybrid_bad_probability HybridMlKem public_input fuel
        program.
  Proof.
    split.
    - exact active_classical_forward_mlkem_remains_hidden.
    - exact: pqxdh_hybrid_one_hidden_contribution_confidentiality.
  Qed.

  Theorem passive_classical_forward_hybrid_confidentiality
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) :
    pqxdh_hybrid_component_remains_hidden passive_classical Forward
        HybridMlKem = true /\
    pqxdh_hybrid_advantage HybridMlKem public_input fuel program
        distinguisher <=
      pqxdh_hybrid_bad_probability HybridMlKem public_input fuel
        program.
  Proof.
    split.
    - exact passive_classical_forward_mlkem_remains_hidden.
    - exact: pqxdh_hybrid_one_hidden_contribution_confidentiality.
  Qed.

  Theorem passive_quantum_forward_hybrid_confidentiality
      (public_input : pqxdh_root_input)
      (fuel : nat)
      (program : bool -> rom_tree pqxdh_hybrid_rom_query bool result)
      (distinguisher : pqxdh_hybrid_view -> bool) :
    pqxdh_hybrid_component_remains_hidden passive_quantum Forward
        HybridMlKem = true /\
    pqxdh_hybrid_advantage HybridMlKem public_input fuel program
        distinguisher <=
      pqxdh_hybrid_bad_probability HybridMlKem public_input fuel
        program.
  Proof.
    split.
    - exact passive_quantum_forward_mlkem_remains_hidden.
    - exact: pqxdh_hybrid_one_hidden_contribution_confidentiality.
  Qed.

End BoundedHybridAdversary.

Print Assumptions pqxdh_hybrid_hidden_coordinate_injective.
Print Assumptions pqxdh_hybrid_domains_are_separated.
Print Assumptions pqxdh_hybrid_flip_source_involutive.
Print Assumptions pqxdh_hybrid_uniform_source_event_reindex.
Print Assumptions pqxdh_hybrid_runs_agree_without_secret_query.
Print Assumptions pqxdh_hybrid_mismatch_implies_bad.
Print Assumptions pqxdh_hybrid_one_hidden_contribution_confidentiality.
Print Assumptions active_classical_forward_hybrid_confidentiality.
Print Assumptions passive_classical_forward_hybrid_confidentiality.
Print Assumptions passive_quantum_forward_hybrid_confidentiality.
Print Assumptions active_quantum_replace_has_no_hidden_hybrid_component.
