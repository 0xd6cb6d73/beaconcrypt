(* SPDX-License-Identifier: 0BSD *)

(** A finite, bounded classical-ROM programming hop for privacy of beaconcrypt's modified CTX transform.

    The query [(K, (N, A, T, S, I))] represents the production outer-hash transcript. Every field and digest is represented by one bit so that the complete oracle table is finite. The real programming representation samples a fresh digest and installs it at the secret transcript; the ideal world publishes the same fresh digest without changing the oracle. A deterministic adversary is an adaptive finite query tree and may give its complete result and query trace to an arbitrary deterministic distinguisher.

    The theorem in this file is only a leakage-preservation hop conditional on [K] being a hidden uniform key supplied by an ideal AEAD/PQXDH-ratchet game. It must be composed with an ideal-AEAD confidentiality theorem. The finite atom widths do not give a production-width bound, and the classical query tree does not model superposition access or establish a QROM result. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrnum order eqtype choice fintype finfun seq all_algebra reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.
From BeaconcryptSSProve Require Import BoundedRom.

Import Num.Theory.
Import Order.POrderTheory.
Import GRing.Theory.

Local Open Scope ring_scope.

(** The public part of the CTX transcript is [(N, A, T, S, I)]. *)
Definition ctx_privacy_public_fields :=
  (bool * (bool * (bool * (bool * bool))))%type.

(** The first component is the hidden AEAD key [K]. *)
Definition ctx_privacy_query :=
  (bool * ctx_privacy_public_fields)%type.

Definition ctx_privacy_table :=
  rom_table ctx_privacy_query bool.

Definition ctx_privacy_trace :=
  rom_trace ctx_privacy_query bool.

Definition ctx_secret_transcript
    (key : bool)
    (public_fields : ctx_privacy_public_fields) : ctx_privacy_query :=
  (key, public_fields).

(** Overwrite exactly one finite-ROM entry. This is the standard programming representation of a real digest: the fresh digest is installed at the secret transcript before the bounded adversary runs. *)
Definition ctx_program_table
    (table : ctx_privacy_table)
    (secret : ctx_privacy_query)
    (fresh_digest : bool) : ctx_privacy_table :=
  [ffun input => if input == secret then fresh_digest else table input].

Lemma ctx_program_table_at_secret
    (table : ctx_privacy_table)
    (secret : ctx_privacy_query)
    (fresh_digest : bool) :
  ctx_program_table table secret fresh_digest secret = fresh_digest.
Proof.
  by rewrite /ctx_program_table ffunE eqxx.
Qed.

Lemma ctx_program_table_away_from_secret
    (table : ctx_privacy_table)
    (secret input : ctx_privacy_query)
    (fresh_digest : bool) :
  input != secret ->
  ctx_program_table table secret fresh_digest input = table input.
Proof.
  move=> input_differs.
  by rewrite /ctx_program_table ffunE (negbTE input_differs).
Qed.

Lemma ctx_program_table_same_value
    (table : ctx_privacy_table)
    (secret : ctx_privacy_query) :
  ctx_program_table table secret (table secret) = table.
Proof.
  apply/ffunP=> input.
  rewrite /ctx_program_table ffunE.
  by case: ifP => [/eqP -> | _].
Qed.

Definition ctx_programming_coins :=
  (ctx_privacy_table * bool)%type.

Definition ctx_default_programming_coins : ctx_programming_coins :=
  ([ffun _ => false], false).

Definition ctx_uniform_programming_coins :
    {distr ctx_programming_coins / R} :=
  @uniform_F _ ctx_default_programming_coins.

(** Swapping a table entry with the fresh digest is an involution. It is the finite coupling witness that turns an independently sampled table and digest into a programmed table while retaining the overwritten value as an unused coin. *)
Definition ctx_programming_swap
    (secret : ctx_privacy_query)
    (coins : ctx_programming_coins) : ctx_programming_coins :=
  (ctx_program_table coins.1 secret coins.2, coins.1 secret).

Lemma ctx_programming_swap_involutive
    (secret : ctx_privacy_query) :
  cancel (ctx_programming_swap secret) (ctx_programming_swap secret).
Proof.
  move=> [table fresh_digest].
  rewrite /ctx_programming_swap /= ctx_program_table_at_secret.
  congr (_, fresh_digest).
  apply/ffunP=> input.
  rewrite /ctx_program_table !ffunE.
  case input_is_secret: (input == secret) => //.
  by move/eqP: input_is_secret => ->.
Qed.

Lemma ctx_programming_swap_bijective
    (secret : ctx_privacy_query) :
  bijective (ctx_programming_swap secret).
Proof.
  exists (ctx_programming_swap secret).
  - exact: ctx_programming_swap_involutive.
  - exact: ctx_programming_swap_involutive.
Qed.

(** The trace records the adversary's chronological classical oracle queries. *)
Definition ctx_trace_queries
    (secret : ctx_privacy_query)
    (trace : ctx_privacy_trace) : bool :=
  has (fun entry => entry.1 == secret) trace.

Section StructuralProgrammingHop.

  Variable result : choiceType.

  Definition ctx_programming_view :=
    (bool * rom_observation ctx_privacy_query bool result)%type.

  Definition ctx_true_real_view
      (fuel : nat)
      (table : ctx_privacy_table)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      ctx_programming_view :=
    let digest := table secret in
    (digest,
      run_bounded_rom ctx_privacy_query bool fuel table
        (program digest)).

  Definition ctx_programmed_real_view
      (fuel : nat)
      (table : ctx_privacy_table)
      (secret : ctx_privacy_query)
      (fresh_digest : bool)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      ctx_programming_view :=
    (fresh_digest,
      run_bounded_rom ctx_privacy_query bool fuel
        (ctx_program_table table secret fresh_digest)
        (program fresh_digest)).

  Definition ctx_fresh_ideal_view
      (fuel : nat)
      (table : ctx_privacy_table)
      (fresh_digest : bool)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      ctx_programming_view :=
    (fresh_digest,
      run_bounded_rom ctx_privacy_query bool fuel table
        (program fresh_digest)).

  Lemma ctx_programmed_real_specializes_to_true_real
      (fuel : nat)
      (table : ctx_privacy_table)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
    ctx_programmed_real_view fuel table secret (table secret) program =
    ctx_true_real_view fuel table secret program.
  Proof.
    rewrite /ctx_programmed_real_view /ctx_true_real_view.
    by rewrite ctx_program_table_same_value.
  Qed.

  (** If the execution against the unprogrammed table never asks the secret query, adaptive control flow and both traces are identical. *)
  Lemma ctx_bounded_runs_agree_without_secret_query
      (fuel : nat)
      (table : ctx_privacy_table)
      (secret : ctx_privacy_query)
      (fresh_digest : bool)
      (program : rom_tree ctx_privacy_query bool result) :
    ~~ ctx_trace_queries secret
      (run_bounded_rom ctx_privacy_query bool fuel table program).2 ->
    run_bounded_rom ctx_privacy_query bool fuel
      (ctx_program_table table secret fresh_digest) program =
    run_bounded_rom ctx_privacy_query bool fuel table program.
  Proof.
    revert program.
    induction fuel as [| fuel induction_hypothesis];
      intros [value | input next]; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite /ctx_trace_queries /=.
      move=> /norP [input_differs tail_avoids_secret].
      rewrite (ctx_program_table_away_from_secret
        table secret input fresh_digest input_differs).
      rewrite (induction_hypothesis
        (next (table input)) tail_avoids_secret).
      reflexivity.
  Qed.

  (** Pointwise fundamental lemma for every deterministic bounded adaptive tree and every deterministic distinguisher. Any decision mismatch in the same coupled run exposes a query for the secret transcript in the ideal trace. *)
  Theorem ctx_same_run_mismatch_implies_secret_query
      (fuel : nat)
      (table : ctx_privacy_table)
      (secret : ctx_privacy_query)
      (fresh_digest : bool)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view -> bool) :
    distinguisher
      (ctx_programmed_real_view fuel table secret fresh_digest program) !=
    distinguisher
      (ctx_fresh_ideal_view fuel table fresh_digest program) ->
    ctx_trace_queries secret
      (ctx_fresh_ideal_view fuel table fresh_digest program).2.2.
  Proof.
    move=> decisions_differ.
    case bad_query:
      (ctx_trace_queries secret
        (ctx_fresh_ideal_view fuel table fresh_digest program).2.2) => //.
    have ideal_trace_avoids_secret :
      ~~ ctx_trace_queries secret
        (run_bounded_rom ctx_privacy_query bool fuel table
          (program fresh_digest)).2.
    {
      by rewrite /ctx_fresh_ideal_view in bad_query; rewrite bad_query.
    }
    have runs_equal := ctx_bounded_runs_agree_without_secret_query
      fuel table secret fresh_digest (program fresh_digest)
      ideal_trace_avoids_secret.
    move: decisions_differ.
    rewrite /ctx_programmed_real_view /ctx_fresh_ideal_view.
    by rewrite runs_equal eqxx.
  Qed.

End StructuralProgrammingHop.

(** Low-level finite reindexing of a uniform distribution by the programming involution. This avoids package-level relational rules and their infinite-sum interchange dependency. *)
Lemma ctx_uniform_programming_coins_reindex
    (output : choiceType)
    (secret : ctx_privacy_query)
    (kernel : ctx_programming_coins -> {distr output / R}) :
  @dlet R ctx_programming_coins output kernel
    ctx_uniform_programming_coins =
  @dlet R ctx_programming_coins output
    (fun coins => kernel (ctx_programming_swap secret coins))
    ctx_uniform_programming_coins.
Proof.
  apply: distr_ext=> observation.
  rewrite !dletE.
  have swap_reindex :
    psum (fun coins : ctx_programming_coins =>
      (ctx_uniform_programming_coins coins * kernel coins observation : R)) =
    psum (fun coins : ctx_programming_coins =>
      (ctx_uniform_programming_coins
        (ctx_programming_swap secret coins) *
      kernel (ctx_programming_swap secret coins) observation : R)).
  {
    apply: reindex_psum.
    - by move=> coins _.
    - move: (ctx_programming_swap_bijective secret) =>
        [inverse swap_then_inverse inverse_then_swap].
      exists inverse.
      + by move=> coins _; apply: swap_then_inverse.
      + by move=> coins _; apply: inverse_then_swap.
  }
  rewrite swap_reindex.
  apply: eq_psum=> coins.
  congr (_ * _).
Qed.

Section UniformRealRepresentation.

  Variable result : choiceType.

  Definition ctx_true_real_game
      (fuel : nat)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      {distr (ctx_programming_view result) / R} :=
    @dlet R ctx_programming_coins (ctx_programming_view result)
      (fun coins =>
        @dunit R (ctx_programming_view result)
          (ctx_true_real_view result fuel coins.1 secret program))
      ctx_uniform_programming_coins.

  Definition ctx_programmed_real_game
      (fuel : nat)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      {distr (ctx_programming_view result) / R} :=
    @dlet R ctx_programming_coins (ctx_programming_view result)
      (fun coins =>
        @dunit R (ctx_programming_view result)
          (ctx_programmed_real_view result fuel coins.1 secret coins.2
            program))
      ctx_uniform_programming_coins.

  Lemma ctx_true_view_after_programming_swap
      (fuel : nat)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (coins : ctx_programming_coins) :
    ctx_true_real_view result fuel
      (ctx_programming_swap secret coins).1 secret program =
    ctx_programmed_real_view result fuel coins.1 secret coins.2 program.
  Proof.
    rewrite /ctx_true_real_view /ctx_programmed_real_view
      /ctx_programming_swap /= ctx_program_table_at_secret.
    reflexivity.
  Qed.

  (** Checked representation theorem: sampling a uniform finite table and publishing [H(secret)] has exactly the same view distribution as sampling a fresh digest and programming a uniform table at [secret]. The unused overwritten bit makes the source spaces equal and is eliminated by the final deterministic map. *)
  Theorem ctx_true_real_is_programmed_real
      (fuel : nat)
      (secret : ctx_privacy_query)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
    ctx_true_real_game fuel secret program =
    ctx_programmed_real_game fuel secret program.
  Proof.
    rewrite /ctx_true_real_game /ctx_programmed_real_game.
    rewrite (ctx_uniform_programming_coins_reindex
      (ctx_programming_view result) secret
      (fun coins =>
        @dunit R (ctx_programming_view result)
          (ctx_true_real_view result fuel coins.1 secret program))).
    apply: distr_ext=> observation.
    apply: eq_in_dlet.
    - move=> coins _.
      by rewrite ctx_true_view_after_programming_swap.
    - by move=> coins.
  Qed.

End UniformRealRepresentation.

(** Elementary same-source coupling inequality for two deterministic decisions. It is proved only from event inclusion, the union bound, and real-order algebra. *)
Lemma same_source_decision_difference_bound
    (source : choiceType)
    (distribution : {distr source / R})
    (left_decision right_decision : pred source) :
  `| \P_[ distribution ] left_decision -
      \P_[ distribution ] right_decision | <=
  \P_[ distribution ]
    (fun sample => left_decision sample != right_decision sample).
Proof.
  pose mismatch :=
    (fun sample => left_decision sample != right_decision sample).
  have left_in_union :
      {subset left_decision <= [predU right_decision & mismatch]}.
  {
    move=> sample.
    rewrite -!topredE /= /mismatch.
    move=> left_true.
    rewrite -!topredE /= /mismatch.
    by rewrite left_true; case: (right_decision sample).
  }
  have right_in_union :
      {subset right_decision <= [predU left_decision & mismatch]}.
  {
    move=> sample.
    rewrite -!topredE /= /mismatch.
    move=> right_true.
    rewrite -!topredE /= /mismatch.
    by rewrite right_true; case: (left_decision sample).
  }
  have left_le :
      \P_[ distribution ] left_decision <=
      \P_[ distribution ] right_decision +
      \P_[ distribution ] mismatch.
  {
    apply/(@le_trans _ _
      (\P_[ distribution ] [predU right_decision & mismatch])).
    exact: subset_pr left_in_union.
    exact: ler_pr_or.
  }
  have right_le :
      \P_[ distribution ] right_decision <=
      \P_[ distribution ] left_decision +
      \P_[ distribution ] mismatch.
  {
    apply/(@le_trans _ _
      (\P_[ distribution ] [predU left_decision & mismatch])).
    exact: subset_pr right_in_union.
    exact: ler_pr_or.
  }
  rewrite ler_norml.
  apply/andP; split.
  - rewrite lerBrDr.
    rewrite [(- \P_[ distribution ] mismatch +
      \P_[ distribution ] right_decision)]addrC.
    by rewrite lerBlDr.
  - rewrite lerBlDr [\P_[ distribution ] mismatch + _]addrC.
    exact: left_le.
Qed.

Section ProbabilityLift.

  Variable result : choiceType.

  Definition ctx_coupled_execution :=
    (bool_choiceType * ctx_programming_coins)%type.

  Definition ctx_execution_secret
      (public_fields : ctx_privacy_public_fields)
      (execution : ctx_coupled_execution) : ctx_privacy_query :=
    ctx_secret_transcript execution.1 public_fields.

  Definition ctx_coupled_true_real_decision_event
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool)
      (execution : ctx_coupled_execution) : bool :=
    let secret := ctx_execution_secret public_fields execution in
    let table := execution.2.1 in
    distinguisher
      (ctx_true_real_view result fuel table secret program).

  Definition ctx_coupled_programmed_real_decision_event
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool)
      (execution : ctx_coupled_execution) : bool :=
    let secret := ctx_execution_secret public_fields execution in
    let table := execution.2.1 in
    let fresh_digest := execution.2.2 in
    distinguisher
      (ctx_programmed_real_view result fuel table secret fresh_digest
        program).

  Definition ctx_coupled_fresh_ideal_decision_event
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool)
      (execution : ctx_coupled_execution) : bool :=
    let table := execution.2.1 in
    let fresh_digest := execution.2.2 in
    distinguisher
      (ctx_fresh_ideal_view result fuel table fresh_digest program).

  Definition ctx_coupled_mismatch_event
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool)
      (execution : ctx_coupled_execution) : bool :=
    ctx_coupled_programmed_real_decision_event public_fields fuel program
      distinguisher execution !=
    ctx_coupled_fresh_ideal_decision_event public_fields fuel program
      distinguisher execution.

  Definition ctx_coupled_bad_event
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (execution : ctx_coupled_execution) : bool :=
    let secret := ctx_execution_secret public_fields execution in
    let table := execution.2.1 in
    let fresh_digest := execution.2.2 in
    ctx_trace_queries secret
      (ctx_fresh_ideal_view result fuel table fresh_digest program).2.2.

  Definition ctx_default_public_fields : ctx_privacy_public_fields :=
    (false, (false, (false, (false, false)))).

  Definition ctx_constant_table : ctx_privacy_table :=
    [ffun _ => false].

  Definition ctx_default_coupled_execution : ctx_coupled_execution :=
    (false, ctx_default_programming_coins).

  (** The finite source jointly samples a uniform hidden key, table, and fresh digest. The key is retained only in the internal coupled execution so that the proof can name the bad query; it is not passed to [program] or [distinguisher]. *)
  Definition ctx_privacy_coupled_game
      (_public_fields : ctx_privacy_public_fields) :
      {distr ctx_coupled_execution / R} :=
    @uniform_F _ ctx_default_coupled_execution.

  Definition ctx_hidden_programming_swap
      (public_fields : ctx_privacy_public_fields)
      (execution : ctx_coupled_execution) : ctx_coupled_execution :=
    (execution.1,
      ctx_programming_swap
        (ctx_execution_secret public_fields execution) execution.2).

  Lemma ctx_hidden_programming_swap_involutive
      (public_fields : ctx_privacy_public_fields) :
    cancel (ctx_hidden_programming_swap public_fields)
      (ctx_hidden_programming_swap public_fields).
  Proof.
    move=> [key coins].
    rewrite /ctx_hidden_programming_swap /ctx_execution_secret /=.
    by rewrite ctx_programming_swap_involutive.
  Qed.

  Lemma ctx_hidden_programming_swap_bijective
      (public_fields : ctx_privacy_public_fields) :
    bijective (ctx_hidden_programming_swap public_fields).
  Proof.
    exists (ctx_hidden_programming_swap public_fields).
    - exact: ctx_hidden_programming_swap_involutive.
    - exact: ctx_hidden_programming_swap_involutive.
  Qed.

  Lemma ctx_uniform_coupled_execution_reindex
      (output : choiceType)
      (public_fields : ctx_privacy_public_fields)
      (kernel : ctx_coupled_execution -> {distr output / R}) :
    @dlet R ctx_coupled_execution output kernel
      (ctx_privacy_coupled_game public_fields) =
    @dlet R ctx_coupled_execution output
      (fun execution =>
        kernel (ctx_hidden_programming_swap public_fields execution))
      (ctx_privacy_coupled_game public_fields).
  Proof.
    apply: distr_ext=> observation.
    rewrite !dletE.
    have swap_reindex :
      psum (fun execution : ctx_coupled_execution =>
        (ctx_privacy_coupled_game public_fields execution *
          kernel execution observation : R)) =
      psum (fun execution : ctx_coupled_execution =>
        (ctx_privacy_coupled_game public_fields
          (ctx_hidden_programming_swap public_fields execution) *
          kernel (ctx_hidden_programming_swap public_fields execution)
            observation : R)).
    {
      apply: reindex_psum.
      - by move=> execution _.
      - move: (ctx_hidden_programming_swap_bijective public_fields) =>
          [inverse swap_then_inverse inverse_then_swap].
        exists inverse.
        + by move=> execution _; apply: swap_then_inverse.
        + by move=> execution _; apply: inverse_then_swap.
    }
    rewrite swap_reindex.
    apply: eq_psum=> execution.
    congr (_ * _).
  Qed.

  Definition ctx_hidden_true_real_game
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      {distr (ctx_programming_view result) / R} :=
    dmargin
      (fun execution =>
        let secret := ctx_execution_secret public_fields execution in
        ctx_true_real_view result fuel execution.2.1 secret program)
      (ctx_privacy_coupled_game public_fields).

  Definition ctx_hidden_programmed_real_game
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      {distr (ctx_programming_view result) / R} :=
    dmargin
      (fun execution =>
        let secret := ctx_execution_secret public_fields execution in
        ctx_programmed_real_view result fuel execution.2.1 secret
          execution.2.2 program)
      (ctx_privacy_coupled_game public_fields).

  Definition ctx_hidden_fresh_ideal_game
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
      {distr (ctx_programming_view result) / R} :=
    dmargin
      (fun execution =>
        ctx_fresh_ideal_view result fuel execution.2.1 execution.2.2
          program)
      (ctx_privacy_coupled_game public_fields).

  Lemma ctx_hidden_true_view_after_programming_swap
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (execution : ctx_coupled_execution) :
    let swapped :=
      ctx_hidden_programming_swap public_fields execution in
    let swapped_secret :=
      ctx_execution_secret public_fields swapped in
    ctx_true_real_view result fuel swapped.2.1 swapped_secret program =
    ctx_programmed_real_view result fuel execution.2.1
      (ctx_execution_secret public_fields execution) execution.2.2 program.
  Proof.
    case: execution=> key coins.
    rewrite /ctx_hidden_programming_swap /ctx_execution_secret /=.
    exact: ctx_true_view_after_programming_swap.
  Qed.

  (** The fixed-secret representation theorem lifts to a uniform hidden key because the key-preserving programming swap is a bijection of the complete finite coin space. *)
  Theorem ctx_hidden_true_real_is_programmed_real
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result) :
    ctx_hidden_true_real_game public_fields fuel program =
    ctx_hidden_programmed_real_game public_fields fuel program.
  Proof.
    rewrite /ctx_hidden_true_real_game /ctx_hidden_programmed_real_game
      /dmargin.
    rewrite (ctx_uniform_coupled_execution_reindex
      (ctx_programming_view result) public_fields
      (fun execution =>
        @dunit R (ctx_programming_view result)
          (let secret := ctx_execution_secret public_fields execution in
          ctx_true_real_view result fuel execution.2.1 secret program))).
    apply: distr_ext=> observation.
    apply: eq_in_dlet.
    - move=> [key [table fresh_digest]] _.
      rewrite /ctx_hidden_programming_swap /ctx_execution_secret /=
        /ctx_true_real_view /ctx_programmed_real_view
        /ctx_programming_swap /= ctx_program_table_at_secret.
      reflexivity.
    - by move=> execution.
  Qed.

  (** Reindexing an event probability directly over the finite source avoids the generic marginal-probability lemma and its infinite-sum interchange dependency. *)
  Lemma ctx_uniform_coupled_event_reindex
      (public_fields : ctx_privacy_public_fields)
      (event : pred ctx_coupled_execution) :
    \P_[ ctx_privacy_coupled_game public_fields ] event =
    \P_[ ctx_privacy_coupled_game public_fields ]
      (fun execution =>
        event (ctx_hidden_programming_swap public_fields execution)).
  Proof.
    rewrite /pr.
    have swap_reindex :
      psum (fun execution : ctx_coupled_execution =>
        ((nat_of_bool (event execution))%:R *
          ctx_privacy_coupled_game public_fields execution : R)) =
      psum (fun execution : ctx_coupled_execution =>
        ((nat_of_bool
          (event
            (ctx_hidden_programming_swap public_fields execution)))%:R *
          ctx_privacy_coupled_game public_fields
            (ctx_hidden_programming_swap public_fields execution) : R)).
    {
      apply: reindex_psum.
      - by move=> execution _.
      - move: (ctx_hidden_programming_swap_bijective public_fields) =>
          [inverse swap_then_inverse inverse_then_swap].
        exists inverse.
        + by move=> execution _; apply: swap_then_inverse.
        + by move=> execution _; apply: inverse_then_swap.
    }
    rewrite swap_reindex.
    apply: eq_psum=> execution.
    congr (_ * _).
  Qed.

  Lemma ctx_hidden_true_decision_after_programming_swap
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool)
      (execution : ctx_coupled_execution) :
    ctx_coupled_true_real_decision_event public_fields fuel program
      distinguisher
      (ctx_hidden_programming_swap public_fields execution) =
    ctx_coupled_programmed_real_decision_event public_fields fuel program
      distinguisher execution.
  Proof.
    case: execution=> key [table fresh_digest].
    rewrite /ctx_coupled_true_real_decision_event
      /ctx_coupled_programmed_real_decision_event
      /ctx_hidden_programming_swap /ctx_execution_secret /=
      /ctx_true_real_view /ctx_programmed_real_view
      /ctx_programming_swap /= ctx_program_table_at_secret.
    reflexivity.
  Qed.

  Theorem ctx_hidden_true_programmed_decision_probability
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    \P_[ ctx_privacy_coupled_game public_fields ]
      (ctx_coupled_true_real_decision_event public_fields fuel program
        distinguisher) =
    \P_[ ctx_privacy_coupled_game public_fields ]
      (ctx_coupled_programmed_real_decision_event public_fields fuel program
        distinguisher).
  Proof.
    rewrite (ctx_uniform_coupled_event_reindex public_fields
      (ctx_coupled_true_real_decision_event public_fields fuel program
        distinguisher)).
    apply: eq_pr=> execution.
    exact: ctx_hidden_true_decision_after_programming_swap.
  Qed.

  Lemma ctx_coupled_event_inclusion
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    {subset
      ctx_coupled_mismatch_event public_fields fuel program distinguisher <=
      ctx_coupled_bad_event public_fields fuel program}.
  Proof.
    move=> [key [table fresh_digest]] /=.
    rewrite /ctx_coupled_mismatch_event
      /ctx_coupled_programmed_real_decision_event
      /ctx_coupled_fresh_ideal_decision_event /ctx_coupled_bad_event
      /ctx_execution_secret /=.
    exact: ctx_same_run_mismatch_implies_secret_query.
  Qed.

  (** Probability lift over any distribution of coupled coins. *)
  Theorem ctx_programming_mismatch_probability_bound
      (execution_distribution : {distr ctx_coupled_execution / R})
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    \P_[ execution_distribution ]
      (ctx_coupled_mismatch_event public_fields fuel program
        distinguisher) <=
    \P_[ execution_distribution ]
      (ctx_coupled_bad_event public_fields fuel program).
  Proof.
    exact: subset_pr
      (ctx_coupled_event_inclusion
        public_fields fuel program distinguisher).
  Qed.

  Theorem ctx_hidden_uniform_key_privacy_hop
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    \P_[ ctx_privacy_coupled_game public_fields ]
      (ctx_coupled_mismatch_event public_fields fuel program
        distinguisher) <=
    \P_[ ctx_privacy_coupled_game public_fields ]
      (ctx_coupled_bad_event public_fields fuel program).
  Proof.
    exact: ctx_programming_mismatch_probability_bound.
  Qed.

  Theorem ctx_programmed_fresh_decision_advantage_bound
      (execution_distribution : {distr ctx_coupled_execution / R})
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    `| \P_[ execution_distribution ]
          (ctx_coupled_programmed_real_decision_event public_fields fuel
            program distinguisher) -
        \P_[ execution_distribution ]
          (ctx_coupled_fresh_ideal_decision_event public_fields fuel
            program distinguisher) | <=
    \P_[ execution_distribution ]
      (ctx_coupled_bad_event public_fields fuel program).
  Proof.
    apply/(@le_trans _ _
      (\P_[ execution_distribution ]
        (ctx_coupled_mismatch_event public_fields fuel program
          distinguisher))).
    - exact: same_source_decision_difference_bound.
    - exact: ctx_programming_mismatch_probability_bound.
  Qed.

  (** End-to-end finite classical-ROM CTX leakage bound: the true real view [H(secret)] and the fresh ideal view have distinguishing-probability gap at most the probability that the ideal trace queries the hidden secret transcript. *)
  Theorem ctx_hidden_uniform_key_true_real_privacy_bound
      (public_fields : ctx_privacy_public_fields)
      (fuel : nat)
      (program : bool -> rom_tree ctx_privacy_query bool result)
      (distinguisher : ctx_programming_view result -> bool) :
    `| \P_[ ctx_privacy_coupled_game public_fields ]
          (ctx_coupled_true_real_decision_event public_fields fuel program
            distinguisher) -
        \P_[ ctx_privacy_coupled_game public_fields ]
          (ctx_coupled_fresh_ideal_decision_event public_fields fuel program
            distinguisher) | <=
    \P_[ ctx_privacy_coupled_game public_fields ]
      (ctx_coupled_bad_event public_fields fuel program).
  Proof.
    rewrite (ctx_hidden_true_programmed_decision_probability
      public_fields fuel program distinguisher).
    exact: ctx_programmed_fresh_decision_advantage_bound.
  Qed.

End ProbabilityLift.

(** A concrete one-query adversary shows that the bad event and the mismatch event are not definitionally empty. The constant ideal table answers [false], while the programmed real table answers the published fresh digest [true] at the secret transcript. *)
Definition ctx_bad_witness_secret : ctx_privacy_query :=
  ctx_secret_transcript false ctx_default_public_fields.

Definition ctx_bad_witness_program
    (_published_digest : bool) :
    rom_tree ctx_privacy_query bool bool :=
  @RomQuery ctx_privacy_query bool bool ctx_bad_witness_secret
    (fun oracle_answer =>
      @RomReturn ctx_privacy_query bool bool oracle_answer).

Definition ctx_bad_witness_distinguisher
    (view : ctx_programming_view bool_choiceType) : bool :=
  odflt false view.2.1.

Definition ctx_bad_witness_execution : ctx_coupled_execution :=
  (false, (ctx_constant_table, true)).

Lemma ctx_bad_query_witness_reachable :
  ctx_coupled_bad_event bool_choiceType ctx_default_public_fields 1
    ctx_bad_witness_program ctx_bad_witness_execution.
Proof.
  by rewrite /ctx_coupled_bad_event /ctx_bad_witness_execution
    /ctx_execution_secret /ctx_fresh_ideal_view /ctx_bad_witness_program
    /ctx_trace_queries /=.
Qed.

Lemma ctx_mismatch_witness_reachable :
  ctx_coupled_mismatch_event bool_choiceType ctx_default_public_fields 1
    ctx_bad_witness_program ctx_bad_witness_distinguisher
    ctx_bad_witness_execution.
Proof.
  by rewrite /ctx_coupled_mismatch_event /ctx_bad_witness_execution
    /ctx_coupled_programmed_real_decision_event
    /ctx_coupled_fresh_ideal_decision_event /ctx_execution_secret
    /ctx_bad_witness_distinguisher /ctx_programmed_real_view
    /ctx_fresh_ideal_view /ctx_bad_witness_program /ctx_program_table
    /ctx_constant_table /= !ffunE eqxx.
Qed.

Print Assumptions ctx_bounded_runs_agree_without_secret_query.
Print Assumptions ctx_same_run_mismatch_implies_secret_query.
Print Assumptions ctx_programming_swap_bijective.
Print Assumptions ctx_uniform_programming_coins_reindex.
Print Assumptions ctx_true_real_is_programmed_real.
Print Assumptions ctx_programming_mismatch_probability_bound.
Print Assumptions ctx_hidden_uniform_key_privacy_hop.
Print Assumptions ctx_hidden_true_real_is_programmed_real.
Print Assumptions ctx_hidden_true_programmed_decision_probability.
Print Assumptions ctx_programmed_fresh_decision_advantage_bound.
Print Assumptions ctx_hidden_uniform_key_true_real_privacy_bound.
Print Assumptions ctx_bad_query_witness_reachable.
Print Assumptions ctx_mismatch_witness_reachable.
