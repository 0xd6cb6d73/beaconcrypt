(* SPDX-License-Identifier: 0BSD *)

(** A generic finite, classical random-oracle interface for bounded game proofs.

    A program is a finite query tree: it can either return a value or issue a query and choose its continuation from the answer.
    The complete finite function implementing the oracle is held only by the runner.
    An execution exposes the return status and the chronological query/answer trace, never the function table itself.

    The fuel bound is intentionally independent of probability semantics.
    This keeps the structural facts below usable by closed SSProve games without importing package-level relational rules or their stronger proof dependencies. *)

From Stdlib Require Import Utf8 Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnum eqtype choice fintype finfun seq reals distr realsum.
From SSProve.Crypt Require Import Axioms Casts SubDistr UniformDistrLemmas.

Local Open Scope ring_scope.

Section BoundedRomStructure.

  Variables query answer : finType.

  (** The table is a finite value so it can be sampled uniformly.
      It remains an interpreter parameter and is absent from [rom_observation]. *)
  Definition rom_table := {ffun query -> answer}.

  Definition rom_query_answer := (query * answer)%type.
  Definition rom_trace := seq rom_query_answer.

  Inductive rom_tree (result : Type) : Type :=
  | RomReturn of result
  | RomQuery of query & (answer -> rom_tree result).

  Arguments RomReturn {result} _.
  Arguments RomQuery {result} _ _.

  (** [None] means that the program attempted one more query after consuming all its fuel.
      A return consumes no fuel. *)
  Fixpoint run_bounded_rom
      {result : Type}
      (fuel : nat)
      (table : rom_table)
      (program : rom_tree result) {struct fuel}
      : (option result * rom_trace)%type :=
    match program with
    | RomReturn value => (Some value, [::])
    | RomQuery input next =>
        match fuel with
        | O => (None, [::])
        | S remaining =>
            let output := table input in
            let execution :=
              run_bounded_rom remaining table (next output) in
            (execution.1, (input, output) :: execution.2)
        end
    end.

  Definition rom_trace_consistent
      (table : rom_table)
      (trace : rom_trace) : bool :=
    all (fun entry => entry.2 == table entry.1) trace.

  (** Every completed oracle query consumes exactly one unit of fuel. *)
  Theorem run_bounded_rom_query_count_bound
      (result : Type)
      (fuel : nat)
      (table : rom_table)
      (program : rom_tree result) :
    Nat.le (size (run_bounded_rom fuel table program).2) fuel.
  Proof.
    revert program.
    induction fuel as [| fuel induction_hypothesis];
      intros [value | input next]; simpl.
    - exact: Nat.le_refl.
    - exact: Nat.le_refl.
    - exact: Nat.le_0_l.
    - apply: le_n_S.
      exact: induction_hypothesis.
  Qed.

  (** Every answer in the public trace is exactly the answer returned by the one hidden table used for that run.
      Repeated queries are therefore consistent automatically. *)
  Theorem run_bounded_rom_trace_consistent
      (result : Type)
      (fuel : nat)
      (table : rom_table)
      (program : rom_tree result) :
    rom_trace_consistent table (run_bounded_rom fuel table program).2.
  Proof.
    elim: fuel program => [| fuel induction_hypothesis]
      [value | input next] //=.
    by rewrite eqxx; apply: induction_hypothesis.
  Qed.

  (** A same-run implication can inspect both the result and its trace, but not the hidden table.
      This pure form is convenient when constructing a collision or bad-event extractor before lifting it to probability. *)
  Lemma run_bounded_rom_same_run_event_inclusion
      (result : Type)
      (fuel : nat)
      (table : rom_table)
      (program : rom_tree result)
      (event bad : (option result * rom_trace)%type -> bool) :
    {subset event <= bad} ->
    event (run_bounded_rom fuel table program) ->
    bad (run_bounded_rom fuel table program).
  Proof.
    exact.
  Qed.

End BoundedRomStructure.

Section BoundedRomGames.

  Variables query answer : finType.
  Variable default_answer : answer.

  Definition rom_constant_table : rom_table query answer :=
    [ffun _ => default_answer].

  (** This distribution samples a complete finite random function.
      The sampled function is consumed by [bounded_rom_game] and never appears in its observation. *)
  Definition uniform_hidden_rom_table :
      {distr (rom_table query answer) / R} :=
    @uniform_F (rom_table query answer) rom_constant_table.

  Definition rom_observation (result : choiceType) :=
    (option result * rom_trace query answer)%type.

  Definition bounded_rom_game
      (result : choiceType)
      (table_distribution : {distr (rom_table query answer) / R})
      (fuel : nat)
      (program : rom_tree query answer result) :
      {distr (rom_observation result) / R} :=
    @dlet R (rom_table query answer) (rom_observation result)
      (fun table =>
         @dunit R (rom_observation result)
           (run_bounded_rom query answer fuel table program))
      table_distribution.

  Definition uniform_bounded_rom_game
      (result : choiceType)
      (fuel : nat)
      (program : rom_tree query answer result) :
      {distr (rom_observation result) / R} :=
    bounded_rom_game result uniform_hidden_rom_table fuel program.

  (** Both events are evaluated on the very same hidden-table execution.
      This is the generic event-reduction rule used by bounded ROM games. *)
  Theorem bounded_rom_same_run_event_reduction
      (result : choiceType)
      (table_distribution : {distr (rom_table query answer) / R})
      (fuel : nat)
      (program : rom_tree query answer result)
      (event bad : rom_observation result -> bool) :
    {subset event <= bad} ->
    \P_[ bounded_rom_game result table_distribution fuel program ] event <=
    \P_[ bounded_rom_game result table_distribution fuel program ] bad.
  Proof.
    move=> event_inclusion.
    exact: subset_pr event_inclusion.
  Qed.

  (** An extractor is also applied to the same public observation.
      Its witness need not reveal the ROM table, and its bad predicate can be used directly as the right-hand event of a reduction. *)
  Theorem bounded_rom_same_run_extractor_reduction
      (result witness : choiceType)
      (table_distribution : {distr (rom_table query answer) / R})
      (fuel : nat)
      (program : rom_tree query answer result)
      (event : rom_observation result -> bool)
      (extract : rom_observation result -> witness)
      (bad : witness -> bool) :
    (forall observation, event observation -> bad (extract observation)) ->
    \P_[ bounded_rom_game result table_distribution fuel program ] event <=
    \P_[ bounded_rom_game result table_distribution fuel program ]
      (fun observation => bad (extract observation)).
  Proof.
    move=> extractor_sound.
    apply: subset_pr.
    exact: extractor_sound.
  Qed.

End BoundedRomGames.

Print Assumptions run_bounded_rom_query_count_bound.
Print Assumptions run_bounded_rom_trace_consistent.
Print Assumptions bounded_rom_same_run_event_reduction.
Print Assumptions bounded_rom_same_run_extractor_reduction.
