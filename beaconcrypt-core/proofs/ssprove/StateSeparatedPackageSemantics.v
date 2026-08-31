(* SPDX-License-Identifier: 0BSD *)

(** This file gives the state-separated response package a checked finite one-call semantics. The stock SSProve [Pr]/[Pr_op] path in the pinned 0.2.4 release transitively depends on an unaccepted infinite-sum interchange theorem, so it is not an admissible capstone under this repository's assumption policy. The restricted evaluator below instead executes the exact linked public operation from [empty_heap] with one externally supplied value for its sole joint finite sampler. A transparent indexed certificate checks the complete returned value and final heap before kernel normalization erases its raw package index and soundness proof; reportable theorems then expose the public observation and two designated CKEY slots. This is not an unrestricted contextual equivalence: a second call distinguishes the tombstoned state-separated package from the stateless monolithic harness. *)

From Stdlib Require Import Bool Utf8 Logic.ProofIrrelevance.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq fintype.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms Package pkg_core_definition.
From BeaconcryptSSProve Require Import PqxdhRatchetGames
  StateSeparatedComposition.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

(** The restricted semantics accepts only samplers whose result type is the complete finite ROM sample. The linked response package contains exactly one such sampler, and [uniform_response_sample_op] is structurally pinned to [uniform_rom_sample] by the inventory. *)
Definition cast_response_sample
  (sample : rom_sample) (operation : Op) : option (Arit operation) :=
  match operation as operation' return option (Arit operation') with
  | existT sample_type _ =>
      match choice_type_eqP sample_type chRomSample with
      | ReflectT equal_types =>
          Some
            (eq_rect chRomSample chElement sample sample_type
              (Logic.eq_sym equal_types))
      | ReflectF _ => None
      end
  end.

Lemma cast_uniform_response_sample :
  forall sample,
    cast_response_sample sample uniform_response_sample_op = Some sample.
Proof.
  move=> sample.
  unfold cast_response_sample, uniform_response_sample_op.
  destruct (choice_type_eqP chRomSample chRomSample)
    as [sample_equal | sample_different].
  2: elim sample_different; reflexivity.
  assert (sample_equal = erefl) as -> by apply proof_irrelevance.
  reflexivity.
Qed.

(** Calls remaining after linking or samplers of another result type reject. Reads and writes use SSProve's actual heap functions, so execution starts from the same canonical empty heap as the stock interpreter. *)
Fixpoint run_response_code_with_sample
  {A : choiceType} (sample : rom_sample) (program : raw_code A)
  (state : heap) : option (A * heap) :=
  match program with
  | ret result => Some (result, state)
  | opr _ _ _ => None
  | getr location continuation =>
      run_response_code_with_sample sample
        (continuation (get_heap state location)) state
  | putr location value continuation =>
      run_response_code_with_sample sample continuation
        (set_heap state location value)
  | sampler operation continuation =>
      match cast_response_sample sample operation with
      | Some value =>
          run_response_code_with_sample sample (continuation value) state
      | None => None
      end
  end.

Definition response_run_summary : Type :=
  option (public_response_observation * (ckey_slot * ckey_slot)).

Definition summarize_response_run
  (execution : option (public_response_observation * heap)) :
  response_run_summary :=
  match execution with
  | Some (observation, state) =>
      Some
        (observation,
          (get_heap state server_ckey_loc,
           get_heap state beacon_ckey_loc))
  | None => None
  end.

Definition run_response_signature : opsig :=
  (run_response_id, (chUnit, chPublicResponseObservation)).

(** These staged projections remove each package-validity proof before raw parallel composition and linking. They are definitionally the raw fields of the exact packages in [StateSeparatedComposition], but no bundled proof remains in their normal forms. *)
Definition consuming_ckey_raw : raw_package :=
  Eval cbn in (consuming_ckey : raw_package).

Definition keying_package_raw
  (session : bounded_session_handle) (authenticated : bool)
  (input : pqxdh_root_input) : raw_package :=
  Eval cbn in (keying_package session authenticated input : raw_package).

Definition keyed_package_raw
  (session : bounded_session_handle) (challenge : bool) : raw_package :=
  Eval cbn in (keyed_package session challenge : raw_package).

Definition successful_composition_driver_raw : raw_package :=
  Eval cbn in (successful_composition_driver : raw_package).

Definition rejected_composition_driver_raw : raw_package :=
  Eval cbn in (rejected_composition_driver : raw_package).

Definition authenticated_composition_core_raw
  (session : bounded_session_handle) (challenge : bool)
  (input : pqxdh_root_input) : raw_package :=
  pkg_composition.link
    (pkg_composition.par
      (keying_package_raw session true input)
      (keyed_package_raw session challenge))
    consuming_ckey_raw.

Definition authenticated_response_package_raw
  (session : bounded_session_handle) (challenge : bool)
  (input : pqxdh_root_input) : raw_package :=
  pkg_composition.link successful_composition_driver_raw
    (authenticated_composition_core_raw session challenge input).

Definition rejected_response_package_raw : raw_package :=
  rejected_composition_driver_raw.

(** Kernel reduction projects the raw authenticated [RUN] code before any reportable theorem mentions it. *)
Definition authenticated_linked_response_code
  (session : bounded_session_handle) (challenge : bool)
  (input : pqxdh_root_input) : raw_code chPublicResponseObservation :=
  Eval cbn in
    get_op_default
      (authenticated_response_package_raw session challenge input)
      run_response_signature Datatypes.tt.

Definition rejected_linked_response_code :
  raw_code chPublicResponseObservation :=
  Eval cbn in
    get_op_default rejected_response_package_raw
      run_response_signature Datatypes.tt.

Lemma run_response_code_bind :
  forall {A B : choiceType} (sample : rom_sample) (program : raw_code A)
    (continuation : A -> raw_code B) state,
    run_response_code_with_sample sample (bind program continuation) state =
      match run_response_code_with_sample sample program state with
      | Some (result, next_state) =>
          run_response_code_with_sample sample
            (continuation result) next_state
      | None => None
      end.
Proof.
  move=> A B sample program.
  induction program as
    [result | C operation argument continuation
    | location continuation induction_hypothesis
    | location value program induction_hypothesis
    | operation continuation induction_hypothesis];
    move=> next state; cbn.
  - reflexivity.
  - reflexivity.
  - apply induction_hypothesis.
  - apply induction_hypothesis.
  - destruct (cast_response_sample sample operation); last reflexivity.
    apply induction_hypothesis.
Qed.

Lemma code_link_operation_uses_default :
  forall {A : choiceType} (operation : opsig) (argument : src operation)
    (continuation : tgt operation -> raw_code A) (provider : raw_package),
    pkg_composition.code_link
      (opr operation argument continuation) provider =
    bind (get_op_default provider operation argument)
      (fun result =>
        pkg_composition.code_link (continuation result) provider).
Proof.
  move=> A operation argument continuation provider.
  unfold get_op_default.
  cbn [pkg_composition.code_link].
  destruct (pkg_composition.lookup_op provider operation); reflexivity.
Qed.

Lemma code_link_return :
  forall {A : choiceType} (result : A) provider,
    pkg_composition.code_link (ret result) provider = ret result.
Proof. reflexivity. Qed.

Lemma run_response_code_link_return :
  forall {A : choiceType} sample (result : A) provider state,
    run_response_code_with_sample sample
      (pkg_composition.code_link (ret result) provider) state =
      Some (result, state).
Proof. reflexivity. Qed.

Lemma self_typed_function_cast :
  forall (source target : choice_type)
    (function : source -> raw_code target),
    (match choice_type_eqP source source with
     | ReflectT source_equal =>
         match choice_type_eqP target target with
         | ReflectT target_equal =>
             Some
               (pkg_composition.cast_fun
                 source_equal target_equal function)
         | ReflectF _ => None
         end
     | ReflectF _ => None
     end) = Some function.
Proof.
  move=> source target function.
  destruct (choice_type_eqP source source)
    as [source_equal | source_different].
  2: elim source_different; reflexivity.
  destruct (choice_type_eqP target target)
    as [target_equal | target_different].
  2: elim target_different; reflexivity.
  rewrite pkg_composition.cast_fun_K.
  reflexivity.
Qed.

Definition setup_server_signature : opsig :=
  (setup_server_id, (chRomSample, chUnit)).
Definition setup_beacon_signature : opsig :=
  (setup_beacon_id, (chRomSample, chUnit)).
Definition seal_response_signature : opsig :=
  (seal_response_id, (chRomSample, chBool)).
Definition open_response_signature : opsig :=
  (open_response_id, (chProd chRomSample chBool, chBool)).

Definition server_installed_heap
  (session : bounded_session_handle) (sample : rom_sample)
  (input : pqxdh_root_input) : heap :=
  set_heap empty_heap server_ckey_loc
    (Some
      (false,
       (production_role_payloads
          session true (sample_to_tape sample) input).1)).

Definition server_consumed_heap
  (session : bounded_session_handle) (sample : rom_sample)
  (input : pqxdh_root_input) : heap :=
  set_heap (server_installed_heap session sample input)
    server_ckey_loc taken_slot.

Definition authenticated_response_ciphertext
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) : bool :=
  let server :=
    (production_role_payloads
      session true (sample_to_tape sample) input).1 in
  let output :=
    ratchet_step_expansion
      (sample_to_tape sample) (payload_send_chain server) in
  xorb challenge output.1.1.

Definition beacon_installed_heap
  (session : bounded_session_handle) (sample : rom_sample)
  (input : pqxdh_root_input) : heap :=
  set_heap (server_consumed_heap session sample input)
    beacon_ckey_loc
    (Some
      (false,
       (production_role_payloads
          session true (sample_to_tape sample) input).2)).

Definition both_consumed_heap
  (session : bounded_session_handle) (sample : rom_sample)
  (input : pqxdh_root_input) : heap :=
  set_heap (beacon_installed_heap session sample input)
    beacon_ckey_loc taken_slot.

Definition authenticated_opened_plaintext
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) : bool :=
  let beacon :=
    (production_role_payloads
      session true (sample_to_tape sample) input).2 in
  let output :=
    ratchet_step_expansion
      (sample_to_tape sample) (payload_receive_chain beacon) in
  xorb
    (authenticated_response_ciphertext session challenge sample input)
    output.1.1.

Lemma beacon_server_locations_neq :
  beacon_ckey_loc != server_ckey_loc.
Proof.
  apply/negP.
  move=> /eqP locations_equal.
  apply role_ckey_locations_are_distinct.
  symmetry.
  exact locations_equal.
Qed.

Lemma server_beacon_locations_neq :
  server_ckey_loc != beacon_ckey_loc.
Proof.
  apply/negP.
  move=> /eqP locations_equal.
  exact (role_ckey_locations_are_distinct locations_equal).
Qed.

Lemma authenticated_response_ciphertext_matches_separated :
  forall session challenge sample input,
    authenticated_response_ciphertext session challenge sample input =
      (separated_first_response session true challenge
        (sample_to_tape sample) input).1.
Proof.
  move=> session challenge sample input.
  rewrite /authenticated_response_ciphertext /separated_first_response.
  case halves: (production_initial_halves (sample_to_tape sample) input) =>
    [left_chain right_chain].
  rewrite /production_role_payloads halves /=.
  rewrite (separated_ckey_transfer_is_one_way_and_role_oriented
    session true left_chain right_chain) /=.
  reflexivity.
Qed.

Lemma both_consumed_heap_has_taken_slots :
  forall session sample input,
    get_heap (both_consumed_heap session sample input) server_ckey_loc =
      taken_slot /\
    get_heap (both_consumed_heap session sample input) beacon_ckey_loc =
      taken_slot.
Proof.
  move=> session sample input.
  rewrite /both_consumed_heap /beacon_installed_heap.
  rewrite set_heap_contract.
  split.
  - rewrite get_set_heap_neq; last exact server_beacon_locations_neq.
    rewrite /server_consumed_heap get_set_heap_eq.
    reflexivity.
  - rewrite get_set_heap_eq.
    reflexivity.
Qed.

Lemma summarize_both_consumed_run :
  forall session sample input observation,
    summarize_response_run
      (Some
        (observation,
         both_consumed_heap session sample input)) =
      Some (observation, (taken_slot, taken_slot)).
Proof.
  move=> session sample input observation.
  change
    (Some
      (observation,
       (get_heap (both_consumed_heap session sample input) server_ckey_loc,
        get_heap (both_consumed_heap session sample input)
          beacon_ckey_loc)) =
     Some (observation, (taken_slot, taken_slot))).
  destruct (both_consumed_heap_has_taken_slots session sample input)
    as [server_taken beacon_taken].
  rewrite server_taken beacon_taken.
  reflexivity.
Qed.

Lemma empty_heap_has_empty_ckey_slots :
  get_heap empty_heap server_ckey_loc = empty_slot /\
  get_heap empty_heap beacon_ckey_loc = empty_slot.
Proof. split; reflexivity. Qed.

Lemma summarize_empty_heap_run :
  forall observation,
    summarize_response_run (Some (observation, empty_heap)) =
      Some (observation, (empty_slot, empty_slot)).
Proof.
  move=> observation.
  change
    (Some
      (observation,
       (get_heap empty_heap server_ckey_loc,
        get_heap empty_heap beacon_ckey_loc)) =
     Some (observation, (empty_slot, empty_slot))).
  destruct empty_heap_has_empty_ckey_slots
    as [server_empty beacon_empty].
  rewrite server_empty beacon_empty.
  reflexivity.
Qed.

Theorem core_setup_server_runs_from_empty :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (composition_core session true challenge input)
        setup_server_signature sample)
      empty_heap =
    Some
      (Datatypes.tt,
       server_installed_heap session sample input).
Proof.
  move=> session challenge sample input.
  rewrite composition_core_equation_1 get_op_default_link.
  unfold setup_server_signature.
  unfold get_op_default.
  cbn [pkg_composition.lookup_op pkg_composition.par
    keying_package keyed_package].
  cbn [keying_package keyed_package pkg_composition.par].
  repeat rewrite self_typed_function_cast.
  simpl.
  repeat rewrite self_typed_function_cast.
  cbn [run_response_code_with_sample server_installed_heap].
  reflexivity.
Qed.

Theorem core_seal_response_runs_after_server_setup :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (composition_core session true challenge input)
        seal_response_signature sample)
      (server_installed_heap session sample input) =
    Some
      (authenticated_response_ciphertext
        session challenge sample input,
       server_consumed_heap session sample input).
Proof.
  move=> session challenge sample input.
  case halves: (production_initial_halves (sample_to_tape sample) input) =>
    [left_chain right_chain].
  rewrite composition_core_equation_1 get_op_default_link.
  unfold seal_response_signature.
  unfold get_op_default.
  cbn [pkg_composition.lookup_op pkg_composition.par
    keying_package keyed_package].
  cbn [keying_package keyed_package pkg_composition.par].
  repeat rewrite self_typed_function_cast.
  simpl.
  repeat rewrite self_typed_function_cast.
  simpl.
  rewrite run_response_code_bind.
  unfold server_installed_heap.
  rewrite get_set_heap_eq.
  cbn [run_response_code_with_sample].
  rewrite /production_role_payloads halves /= /payload_session /payload_role
    /payload_authenticated /server_payload /make_payload.
  cbn [run_response_code_with_sample].
  rewrite eqxx.
  cbn [run_response_code_with_sample].
  rewrite /authenticated_response_ciphertext /server_consumed_heap
    /server_installed_heap /production_role_payloads halves /=
    /payload_send_chain /server_payload /make_payload.
  reflexivity.
Qed.

Theorem core_setup_beacon_runs_after_server_seal :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (composition_core session true challenge input)
        setup_beacon_signature sample)
      (server_consumed_heap session sample input) =
    Some
      (Datatypes.tt,
       beacon_installed_heap session sample input).
Proof.
  move=> session challenge sample input.
  rewrite composition_core_equation_1 get_op_default_link.
  unfold setup_beacon_signature.
  unfold get_op_default.
  cbn [pkg_composition.lookup_op pkg_composition.par
    keying_package keyed_package].
  cbn [keying_package keyed_package pkg_composition.par].
  repeat rewrite self_typed_function_cast.
  simpl.
  repeat rewrite self_typed_function_cast.
  cbn [run_response_code_with_sample].
  unfold server_consumed_heap, server_installed_heap.
  rewrite set_heap_contract.
  rewrite run_response_code_bind.
  cbn [run_response_code_with_sample].
  rewrite get_set_heap_neq; last exact beacon_server_locations_neq.
  rewrite get_empty_heap.
  change (heap_init (projT1 beacon_ckey_loc)) with (None : ckey_slot).
  rewrite /payload_role /beacon_payload /make_payload.
  cbn [run_response_code_with_sample].
  rewrite /beacon_installed_heap /server_consumed_heap
    /server_installed_heap set_heap_contract.
  reflexivity.
Qed.

Theorem core_open_response_runs_after_beacon_setup :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (composition_core session true challenge input)
        open_response_signature
        (sample,
         authenticated_response_ciphertext
           session challenge sample input))
      (beacon_installed_heap session sample input) =
    Some
      (authenticated_opened_plaintext session challenge sample input,
       both_consumed_heap session sample input).
Proof.
  move=> session challenge sample input.
  case halves: (production_initial_halves (sample_to_tape sample) input) =>
    [left_chain right_chain].
  rewrite composition_core_equation_1 get_op_default_link.
  unfold open_response_signature.
  unfold get_op_default.
  cbn [pkg_composition.lookup_op pkg_composition.par
    keying_package keyed_package].
  cbn [keying_package keyed_package pkg_composition.par].
  repeat rewrite self_typed_function_cast.
  simpl.
  repeat rewrite self_typed_function_cast.
  simpl.
  rewrite run_response_code_bind.
  unfold beacon_installed_heap.
  rewrite get_set_heap_eq.
  cbn [run_response_code_with_sample].
  rewrite /production_role_payloads halves /= /payload_session /payload_role
    /payload_authenticated /beacon_payload /make_payload.
  cbn [run_response_code_with_sample].
  rewrite eqxx.
  cbn [run_response_code_with_sample].
  rewrite /authenticated_opened_plaintext /both_consumed_heap
    /beacon_installed_heap /production_role_payloads halves /=
    /payload_receive_chain /beacon_payload /make_payload.
  reflexivity.
Qed.

(** The exact linked authenticated [RUN] body consumes one joint sample, returns the optional ciphertext, and leaves both private CKEY slots tombstoned. *)
Local Lemma checked_authenticated_package_run_normalizes :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (state_separated_response_package session true challenge input)
        run_response_signature Datatypes.tt)
      empty_heap =
    Some
      (Some
         (authenticated_response_ciphertext
           session challenge sample input),
       both_consumed_heap session sample input).
Proof.
  move=> session challenge sample input.
  rewrite state_separated_response_package_equation_1 get_op_default_link.
  cbn [composition_driver].
  unfold run_response_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_sample].
  rewrite cast_uniform_response_sample.
  cbn [run_response_code_with_sample].
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default run_response_code_bind.
  rewrite run_response_code_bind.
  fold setup_server_signature.
  rewrite core_setup_server_runs_from_empty.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_link_return.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite code_link_operation_uses_default run_response_code_bind.
  rewrite run_response_code_bind.
  fold seal_response_signature.
  rewrite core_seal_response_runs_after_server_setup.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_link_return.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite code_link_operation_uses_default run_response_code_bind.
  fold setup_beacon_signature.
  rewrite core_setup_beacon_runs_after_server_seal.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite code_link_operation_uses_default run_response_code_bind.
  fold open_response_signature.
  rewrite core_open_response_runs_after_beacon_setup.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_link_return.
  cbn -[pkg_composition.code_link get_op_default
    authenticated_response_ciphertext both_consumed_heap].
  reflexivity.
Qed.

(** False provenance returns the explicit rejection observation before sampling or invoking the core, and it leaves the canonical empty heap unchanged. *)
Local Lemma checked_rejected_package_run_normalizes :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (get_op_default
        (state_separated_response_package session false challenge input)
        run_response_signature Datatypes.tt)
      empty_heap = Some (None, empty_heap).
Proof.
  move=> session challenge sample input.
  rewrite state_separated_response_package_equation_1 get_op_default_link.
  cbn [composition_driver].
  unfold run_response_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_sample].
  reflexivity.
Qed.

(** The raw projections above are definitionally the computational fields of the checked packages. These local bridge lemmas deliberately retain SSProve's syntax types: in release 0.2.4, merely mentioning those types makes [Print Assumptions] traverse the generic sampler distribution and its rejected infinite-sum interchange dependency. The reportable capstones therefore start from the proof-erased normal forms below, while these lemmas kernel-check that those normal forms are exactly what the linked [RUN] bodies execute to. *)
Local Lemma authenticated_linked_response_code_is_checked_run :
  forall session challenge input,
    authenticated_linked_response_code session challenge input =
      get_op_default
        (state_separated_response_package session true challenge input)
        run_response_signature Datatypes.tt.
Proof.
  move=> session challenge input.
  unfold authenticated_linked_response_code,
    authenticated_response_package_raw,
    authenticated_composition_core_raw,
    successful_composition_driver_raw, keying_package_raw,
    keyed_package_raw, consuming_ckey_raw.
  rewrite state_separated_response_package_equation_1 get_op_default_link.
  reflexivity.
Qed.

Local Lemma rejected_linked_response_code_is_checked_run :
  forall session challenge input,
    rejected_linked_response_code =
      get_op_default
        (state_separated_response_package session false challenge input)
        run_response_signature Datatypes.tt.
Proof.
  move=> session challenge input.
  unfold rejected_linked_response_code, rejected_response_package_raw,
    rejected_composition_driver_raw.
  rewrite state_separated_response_package_equation_1 get_op_default_link.
  cbn [composition_driver].
  unfold run_response_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  reflexivity.
Qed.

Definition authenticated_package_execution_normal_form
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  option (public_response_observation * heap) :=
  Some
    (Some
       (authenticated_response_ciphertext
          session challenge sample input),
     both_consumed_heap session sample input).

Definition rejected_package_execution_normal_form :
  option (public_response_observation * heap) :=
  Some (None, empty_heap).

Local Lemma authenticated_linked_response_code_has_normal_form :
  forall session challenge sample input,
    run_response_code_with_sample sample
      (authenticated_linked_response_code session challenge input)
      empty_heap =
    authenticated_package_execution_normal_form
      session challenge sample input.
Proof.
  move=> session challenge sample input.
  rewrite authenticated_linked_response_code_is_checked_run.
  rewrite checked_authenticated_package_run_normalizes.
  reflexivity.
Qed.

Local Lemma rejected_linked_response_code_has_normal_form :
  forall (session : bounded_session_handle) (challenge : bool)
    (sample : rom_sample) (input : pqxdh_root_input),
    run_response_code_with_sample sample
      rejected_linked_response_code empty_heap =
    rejected_package_execution_normal_form.
Proof.
  move=> session challenge sample input.
  rewrite (rejected_linked_response_code_is_checked_run
    session challenge input).
  rewrite checked_rejected_package_run_normalizes.
  reflexivity.
Qed.

Local Lemma authenticated_package_execution_normalizes :
  forall session challenge sample input,
    summarize_response_run
      (authenticated_package_execution_normal_form
        session challenge sample input) =
      Some
        (separated_public_response_observation
          session true challenge sample input,
         (taken_slot, taken_slot)).
Proof.
  move=> session challenge sample input.
  unfold authenticated_package_execution_normal_form.
  rewrite summarize_both_consumed_run.
  rewrite /separated_public_response_observation /=.
  rewrite authenticated_response_ciphertext_matches_separated.
  reflexivity.
Qed.

Local Lemma rejected_package_execution_normalizes :
  summarize_response_run rejected_package_execution_normal_form =
    Some (None, (empty_slot, empty_slot)).
Proof.
  unfold rejected_package_execution_normal_form.
  apply summarize_empty_heap_run.
Qed.

(** A certificate is indexed by the exact raw execution, including its full final heap. Its soundness field is checked before kernel reduction erases both that raw-code index and the proof, leaving a reportable normal form that does not inherit assumptions from SSProve's generic sampler syntax. *)
Record response_run_certificate
  (execution : option (public_response_observation * heap)) := {
  certified_response_run : option (public_response_observation * heap);
  response_run_certificate_sound : execution = certified_response_run
}.

Definition authenticated_package_run_certificate
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  response_run_certificate
    (run_response_code_with_sample sample
      (authenticated_linked_response_code session challenge input)
      empty_heap).
Proof.
  refine
    {| certified_response_run :=
         authenticated_package_execution_normal_form
           session challenge sample input |}.
  apply authenticated_linked_response_code_has_normal_form.
Defined.

Definition rejected_package_run_certificate
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  response_run_certificate
    (run_response_code_with_sample sample
      rejected_linked_response_code empty_heap).
Proof.
  refine
    {| certified_response_run :=
         rejected_package_execution_normal_form |}.
  apply (rejected_linked_response_code_has_normal_form
    session challenge sample input).
Defined.

Definition authenticated_package_run_normal_form
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  option (public_response_observation * heap) :=
  Eval cbn in
    @certified_response_run _
      (authenticated_package_run_certificate
        session challenge sample input).

Definition rejected_package_run_normal_form
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  option (public_response_observation * heap) :=
  Eval cbn in
    @certified_response_run _
      (rejected_package_run_certificate
        session challenge sample input).

(** The authenticated proof-erased certificate exposes the optional ciphertext and records that both private CKEY slots were destructively consumed. *)
Theorem authenticated_package_run_normalizes :
  forall session challenge sample input,
    summarize_response_run
      (authenticated_package_run_normal_form
        session challenge sample input) =
      Some
        (separated_public_response_observation
          session true challenge sample input,
         (taken_slot, taken_slot)).
Proof.
  move=> session challenge sample input.
  apply authenticated_package_execution_normalizes.
Qed.

(** The rejected proof-erased certificate returns [None] before sampling or core invocation and retains two empty private slots. *)
Theorem rejected_package_run_normalizes :
  forall session challenge sample input,
    summarize_response_run
      (rejected_package_run_normal_form
        session challenge sample input) =
      Some (None, (empty_slot, empty_slot)).
Proof.
  move=> session challenge sample input.
  apply rejected_package_execution_normalizes.
Qed.

(** This is the authenticated public marginal of the restricted one-call package semantics; private heap contents are intentionally discarded. *)
Definition package_public_response_observation
  (session : bounded_session_handle) (challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  public_response_observation :=
  match
    summarize_response_run
      (authenticated_package_run_normal_form
        session challenge sample input)
  with
  | Some (observation, _) => observation
  | None => None
  end.

Theorem package_public_response_observation_matches_direct :
  forall session challenge sample input,
    package_public_response_observation
      session challenge sample input =
    separated_public_response_observation
      session true challenge sample input.
Proof.
  move=> session challenge sample input.
  unfold package_public_response_observation.
  rewrite authenticated_package_run_normalizes.
  reflexivity.
Qed.

Definition state_separated_package_response_view_game
  (session : bounded_session_handle) (input : pqxdh_root_input)
  (challenge : bool) (distinguisher : pred public_response_observation) : R :=
  \P_[uniform_rom_sample]
    [pred sample |
      distinguisher
        (package_public_response_observation
          session challenge sample input)].

Theorem state_separated_package_response_view_matches_direct :
  forall session input challenge distinguisher,
    state_separated_package_response_view_game
      session input challenge distinguisher =
    state_separated_public_response_view_game
      session input challenge distinguisher.
Proof.
  move=> session input challenge distinguisher.
  rewrite /state_separated_package_response_view_game
    /state_separated_public_response_view_game.
  apply/eq_pr=> sample.
  change
    (distinguisher
       (package_public_response_observation
         session challenge sample input) =
     distinguisher
       (separated_public_response_observation
         session true challenge sample input)).
  rewrite package_public_response_observation_matches_direct.
  reflexivity.
Qed.

Definition state_separated_package_response_advantage
  (session : bounded_session_handle) (input : pqxdh_root_input)
  (distinguisher : pred public_response_observation) : R :=
  `| state_separated_package_response_view_game
       session input false distinguisher -
     state_separated_package_response_view_game
       session input true distinguisher |.

Theorem state_separated_package_response_advantage_matches_direct :
  forall session input distinguisher,
    state_separated_package_response_advantage
      session input distinguisher =
    state_separated_public_response_advantage
      session input distinguisher.
Proof.
  move=> session input distinguisher.
  rewrite /state_separated_package_response_advantage
    /state_separated_public_response_advantage.
  rewrite !state_separated_package_response_view_matches_direct.
  reflexivity.
Qed.

Print Assumptions authenticated_package_run_normalizes.
Print Assumptions rejected_package_run_normalizes.
Print Assumptions package_public_response_observation_matches_direct.
Print Assumptions state_separated_package_response_view_matches_direct.
Print Assumptions state_separated_package_response_advantage_matches_direct.
