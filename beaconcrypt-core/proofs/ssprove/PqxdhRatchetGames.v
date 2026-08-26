(* SPDX-License-Identifier: 0BSD *)

(** This file gives a closed, finite game model of one beaconcrypt PQXDH session followed by one symmetric-ratchet record at fixed sequence zero. It is a bounded unrolling, not an unbounded ratchet theorem. Cryptographic implementations are outside the model: random-oracle answers and encryption are ideal, authentication rejects every classical forgery, and honest ML-KEM decapsulation remains opaque even to the passive quantum attacker. The quantum scenarios are classical SSProve games with explicit post-quantum capabilities; they are not QROM proofs and do not model superposition queries. *)

From Stdlib Require Import Bool Utf8 btauto.Btauto.
From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq fintype.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms Casts ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl Package Prelude.
From extructures Require Import ord fset fmap.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

(** Attacker modalities are explicit rather than encoded by four unrelated games. One Ed seed jointly supplies the Ed25519 signing identity and its converted X25519 identity, so the quantum capability compromises both together rather than treating them as independent secrets. It never reveals an honest ML-KEM secret; an active quantum attacker instead forges the classical authentication and substitutes a public key for an ML-KEM secret key it selected itself. *)
Inductive network_power : Type :=
| PassiveNetwork
| ActiveNetwork.

Inductive computation_power : Type :=
| ClassicalComputation
| QuantumComputation.

Inductive network_action : Type :=
| Forward
| Replace.

Record attacker_model : Type := {
  attacker_network : network_power;
  attacker_computation : computation_power
}.

Definition active_classical : attacker_model :=
  {| attacker_network := ActiveNetwork;
     attacker_computation := ClassicalComputation |}.

Definition passive_classical : attacker_model :=
  {| attacker_network := PassiveNetwork;
     attacker_computation := ClassicalComputation |}.

Definition active_quantum : attacker_model :=
  {| attacker_network := ActiveNetwork;
     attacker_computation := QuantumComputation |}.

Definition passive_quantum : attacker_model :=
  {| attacker_network := PassiveNetwork;
     attacker_computation := QuantumComputation |}.

Definition network_is_active (model : attacker_model) : bool :=
  match attacker_network model with
  | PassiveNetwork => false
  | ActiveNetwork => true
  end.

Definition quantum_recovers_joint_ed_seed (model : attacker_model) : bool :=
  match attacker_computation model with
  | ClassicalComputation => false
  | QuantumComputation => true
  end.

Definition quantum_recovers_classical_secrets : attacker_model -> bool :=
  quantum_recovers_joint_ed_seed.

Definition can_forge_ed25519_identity (model : attacker_model) : bool :=
  quantum_recovers_joint_ed_seed model.

Definition can_recover_converted_x25519_identity (model : attacker_model) : bool :=
  quantum_recovers_joint_ed_seed model.

Definition action_is_replace (action : network_action) : bool :=
  match action with
  | Forward => false
  | Replace => true
  end.

Definition can_forge_bundle_authentication (model : attacker_model) : bool :=
  network_is_active model && can_forge_ed25519_identity model.

Definition ideal_bundle_authentication_accepts
  (model : attacker_model) (action : network_action) : bool :=
  match action with
  | Forward => true
  | Replace => can_forge_bundle_authentication model
  end.

Definition can_install_attacker_mlkem_key
  (model : attacker_model) (action : network_action) : bool :=
  action_is_replace action && ideal_bundle_authentication_accepts model action.

Definition can_decapsulate_honest_mlkem (_ : attacker_model) : bool := false.

Definition can_decapsulate_selected_mlkem
  (model : attacker_model) (action : network_action) : bool :=
  can_install_attacker_mlkem_key model action.

Definition attacker_can_recompute_accepted_root_input
  (model : attacker_model) (action : network_action) : bool :=
  can_recover_converted_x25519_identity model &&
  match action with
  | Forward => can_decapsulate_honest_mlkem model
  | Replace => can_decapsulate_selected_mlkem model action
  end.

Lemma quantum_joint_seed_compromise :
  forall model,
    can_forge_ed25519_identity model =
    can_recover_converted_x25519_identity model.
Proof. reflexivity. Qed.

Lemma active_classical_root_hidden :
  forall action,
    attacker_can_recompute_accepted_root_input active_classical action = false.
Proof. by case. Qed.

Lemma passive_classical_forward_root_hidden :
  attacker_can_recompute_accepted_root_input passive_classical Forward = false.
Proof. reflexivity. Qed.

Lemma passive_quantum_mlkem_is_opaque :
  quantum_recovers_classical_secrets passive_quantum = true /\
  can_decapsulate_honest_mlkem passive_quantum = false /\
  attacker_can_recompute_accepted_root_input passive_quantum Forward = false.
Proof. repeat split. Qed.

Lemma active_quantum_substitution_succeeds :
  ideal_bundle_authentication_accepts active_quantum Replace = true /\
  can_install_attacker_mlkem_key active_quantum Replace = true /\
  can_decapsulate_selected_mlkem active_quantum Replace = true /\
  attacker_can_recompute_accepted_root_input active_quantum Replace = true.
Proof. repeat split. Qed.

Lemma active_classical_replace_is_rejected :
  ideal_bundle_authentication_accepts active_classical Replace = false.
Proof. reflexivity. Qed.

(** A PQXDH root input records exactly the production [build_root_key_input] 192-byte ordering after its fixed padding: four classical DH contributions followed by the post-quantum KEM contribution. Bundle authentication is public control metadata and is deliberately not hashed as part of this root input. Bits are finite atoms here, not implementations of cryptographic values. *)
Record pqxdh_root_input : Type := {
  dh1_contribution : bool;
  dh2_contribution : bool;
  dh3_contribution : bool;
  dh4_contribution : bool;
  mlkem_contribution : bool
}.

Definition honest_pqxdh_input : pqxdh_root_input :=
  {| dh1_contribution := true;
     dh2_contribution := false;
     dh3_contribution := true;
     dh4_contribution := false;
     mlkem_contribution := true |}.

Definition substituted_pqxdh_input : pqxdh_root_input :=
  {| dh1_contribution := false;
     dh2_contribution := true;
     dh3_contribution := false;
     dh4_contribution := true;
     mlkem_contribution := false |}.

Definition submitted_bundle_is_honest (action : network_action) : bool :=
  negb (action_is_replace action).

Definition accepted_pqxdh_input (action : network_action) : pqxdh_root_input :=
  if action_is_replace action
  then substituted_pqxdh_input
  else honest_pqxdh_input.

Lemma active_quantum_accepts_substitution :
  ideal_bundle_authentication_accepts active_quantum Replace = true /\
  submitted_bundle_is_honest Replace = false /\
  accepted_pqxdh_input Replace = substituted_pqxdh_input.
Proof. repeat split. Qed.

Lemma active_classical_keeps_honest_bundle :
  ideal_bundle_authentication_accepts active_classical Forward = true /\
  submitted_bundle_is_honest Forward = true /\
  accepted_pqxdh_input Forward = honest_pqxdh_input.
Proof. repeat split. Qed.

(** The PQXDH HKDF label is separate, but initial ratchet expansion and every later ratchet step use the same symmetric-ratchet HKDF label. The finite oracle table is therefore keyed only by the symmetric input bit, without a phase tag. Each full 76-byte-style answer is represented by its first prefix component, second prefix component, and final suffix component. Initial 64-byte-style expansion reads the first two components, making its output an exact prefix of the step expansion on an equal input. These are the computational counterparts of the deterministic [build_root_key_input], [split_initial_ratchet_kdf_output], and [split_ratchet_kdf_output] contracts checked through the hax/Lean/F* correctness boundary; this file does not re-prove those implementation contracts. *)
Record symmetric_hkdf_output : Type := {
  hkdf_first_prefix : bool;
  hkdf_second_prefix : bool;
  hkdf_final_suffix : bool
}.

Record rom_tape : Type := {
  pqxdh_honest_root_answer : bool;
  pqxdh_substituted_root_answer : bool;
  symmetric_answer_false : symmetric_hkdf_output;
  symmetric_answer_true : symmetric_hkdf_output
}.

Definition is_substituted_pqxdh_input (input : pqxdh_root_input) : bool :=
  negb (dh1_contribution input) &&
  dh2_contribution input &&
  negb (dh3_contribution input) &&
  dh4_contribution input &&
  negb (mlkem_contribution input).

Definition ideal_pqxdh_root
  (tape : rom_tape) (input : pqxdh_root_input) : bool :=
  if is_substituted_pqxdh_input input
  then pqxdh_substituted_root_answer tape
  else pqxdh_honest_root_answer tape.

Lemma honest_root_query_uses_honest_entry :
  forall tape,
    ideal_pqxdh_root tape honest_pqxdh_input =
    pqxdh_honest_root_answer tape.
Proof. reflexivity. Qed.

Lemma substituted_root_query_uses_substituted_entry :
  forall tape,
    ideal_pqxdh_root tape substituted_pqxdh_input =
    pqxdh_substituted_root_answer tape.
Proof. reflexivity. Qed.

Definition ideal_symmetric_hkdf
  (tape : rom_tape) (input : bool) : symmetric_hkdf_output :=
  if input then symmetric_answer_true tape else symmetric_answer_false tape.

Definition initial_ratchet_expansion
  (tape : rom_tape) (root : bool) : bool * bool :=
  let output := ideal_symmetric_hkdf tape root in
  (hkdf_first_prefix output, hkdf_second_prefix output).

Definition ratchet_step_expansion
  (tape : rom_tape) (chain : bool) : bool * bool * bool :=
  let output := ideal_symmetric_hkdf tape chain in
  (hkdf_first_prefix output, hkdf_second_prefix output, hkdf_final_suffix output).

Lemma shared_symmetric_label_has_prefix_consistency :
  forall tape input,
    initial_ratchet_expansion tape input =
    let '(key, next_chain, _) := ratchet_step_expansion tape input in
    (key, next_chain).
Proof. reflexivity. Qed.

Record established_keys : Type := {
  established_root_key : bool;
  established_chain_key : bool;
  established_record_key : bool;
  established_next_chain : bool;
  established_nonce : bool
}.

Definition derive_keys_from_input
  (tape : rom_tape) (input : pqxdh_root_input) : established_keys :=
  let root := ideal_pqxdh_root tape input in
  let '(_, chain) := initial_ratchet_expansion tape root in
  let '(record, next_chain, nonce) := ratchet_step_expansion tape chain in
  {| established_root_key := root;
     established_chain_key := chain;
     established_record_key := record;
     established_next_chain := next_chain;
     established_nonce := nonce |}.

Definition establish_and_ratchet
  (action : network_action) (tape : rom_tape) : established_keys :=
  derive_keys_from_input tape (accepted_pqxdh_input action).

Lemma forward_game_uses_honest_root_entry :
  forall tape,
    established_root_key (establish_and_ratchet Forward tape) =
    pqxdh_honest_root_answer tape.
Proof. reflexivity. Qed.

Lemma replace_game_uses_substituted_root_entry :
  forall tape,
    established_root_key (establish_and_ratchet Replace tape) =
    pqxdh_substituted_root_answer tape.
Proof. reflexivity. Qed.

Definition record_ciphertext
  (action : network_action) (challenge : bool) (tape : rom_tape) : bool :=
  xorb challenge (established_record_key (establish_and_ratchet action tape)).

Definition attacker_recompute_record_pad
  (tape : rom_tape) (input : pqxdh_root_input) : bool :=
  let root := ideal_pqxdh_root tape input in
  let '(_, chain) := initial_ratchet_expansion tape root in
  let '(record, _, _) := ratchet_step_expansion tape chain in
  record.

Lemma recomputation_capability_forces_substituted_acceptance :
  forall model action,
    attacker_can_recompute_accepted_root_input model action = true ->
    ideal_bundle_authentication_accepts model action = true /\
    accepted_pqxdh_input action = substituted_pqxdh_input.
Proof.
  move=> [network computation] action.
  rewrite /attacker_can_recompute_accepted_root_input
    /can_recover_converted_x25519_identity /quantum_recovers_joint_ed_seed
    /can_decapsulate_honest_mlkem /can_decapsulate_selected_mlkem
    /can_install_attacker_mlkem_key /ideal_bundle_authentication_accepts
    /can_forge_bundle_authentication /can_forge_ed25519_identity
    /network_is_active /action_is_replace.
  case: network; case: computation; case: action => /=;
    try (move=> impossible; discriminate impossible).
  by move=> _; split.
Qed.

Lemma attacker_recomputed_pad_matches_game :
  forall model action tape,
    attacker_can_recompute_accepted_root_input model action = true ->
    attacker_recompute_record_pad tape substituted_pqxdh_input =
    established_record_key (establish_and_ratchet action tape).
Proof.
  move=> model action tape recomputes.
  have [_ accepted_input] :=
    recomputation_capability_forces_substituted_acceptance
      model action recomputes.
  rewrite /attacker_recompute_record_pad /establish_and_ratchet
    /derive_keys_from_input accepted_input.
  reflexivity.
Qed.

(** The observation is the only challenge-dependent component of an accepted transcript. Ideal authentication maps a rejected replacement to the fixed failure observation. A capable active quantum attacker removes the pad only by recomputing from the exact substituted root input; [attacker_recomputed_pad_matches_game] proves that this independently defined path matches the accepted game derivation. *)
Definition protocol_observation
  (model : attacker_model) (action : network_action)
  (challenge : bool) (tape : rom_tape) : bool :=
  if ideal_bundle_authentication_accepts model action then
    let ciphertext := record_ciphertext action challenge tape in
    if attacker_can_recompute_accepted_root_input model action
    then xorb ciphertext
      (attacker_recompute_record_pad tape substituted_pqxdh_input)
    else ciphertext
  else false.

Lemma active_quantum_recovers_challenge :
  forall challenge tape,
    protocol_observation active_quantum Replace challenge tape = challenge.
Proof.
  move=> challenge tape.
  rewrite /protocol_observation /= /record_ciphertext.
  rewrite (attacker_recomputed_pad_matches_game
    active_quantum Replace tape erefl).
  case: (established_record_key (establish_and_ratchet Replace tape)).
  - by case: challenge.
  - by case: challenge.
Qed.

Lemma active_classical_replace_observation_is_failure :
  forall challenge tape,
    protocol_observation active_classical Replace challenge tape = false.
Proof. reflexivity. Qed.

Definition i_bool : nat := #|'bool|.

#[local] Instance i_bool_positive : Positive i_bool.
Proof. rewrite /i_bool card_bool. done. Defined.

Definition rom_coin : Type := Arit (uniform i_bool).

Definition coin_to_bool (coin : rom_coin) : bool := otf coin.

Definition flip_coin (coin : rom_coin) : rom_coin :=
  fto (negb (coin_to_bool coin)).

Lemma flip_coin_involutive : cancel flip_coin flip_coin.
Proof.
  move=> coin.
  rewrite /flip_coin /coin_to_bool otf_fto negbK fto_otf.
  reflexivity.
Qed.

Lemma flip_coin_bijective : bijective flip_coin.
Proof.
  exists flip_coin.
  - exact flip_coin_involutive.
  - exact flip_coin_involutive.
Qed.

Definition tape_of_bits
  (honest_root_bit substituted_root_bit
   false_first_bit false_second_bit false_suffix_bit
   true_first_bit true_second_bit true_suffix_bit : bool) : rom_tape :=
  {| pqxdh_honest_root_answer := honest_root_bit;
     pqxdh_substituted_root_answer := substituted_root_bit;
     symmetric_answer_false :=
       {| hkdf_first_prefix := false_first_bit;
          hkdf_second_prefix := false_second_bit;
          hkdf_final_suffix := false_suffix_bit |};
     symmetric_answer_true :=
       {| hkdf_first_prefix := true_first_bit;
          hkdf_second_prefix := true_second_bit;
          hkdf_final_suffix := true_suffix_bit |} |}.

Definition tape_of_coins
  (honest_root_coin substituted_root_coin
   false_first_coin false_second_coin false_suffix_coin
   true_first_coin true_second_coin true_suffix_coin : rom_coin) : rom_tape :=
  tape_of_bits (coin_to_bool honest_root_coin)
    (coin_to_bool substituted_root_coin)
    (coin_to_bool false_first_coin)
    (coin_to_bool false_second_coin)
    (coin_to_bool false_suffix_coin)
    (coin_to_bool true_first_coin)
    (coin_to_bool true_second_coin)
    (coin_to_bool true_suffix_coin).

Definition challenge_id : nat := 37.

Definition challenge_interface : Interface :=
  [interface #val #[challenge_id] : 'unit → 'bool ].

(** The package samples the finite lazy-ROM tape and returns the complete challenge-dependent observation. This is an executable perfect-primitive game, not a cryptographic implementation. *)
Definition pqxdh_ratchet_package
  (model : attacker_model) (action : network_action) (challenge : bool) :
  package fset0 [interface] challenge_interface :=
  [package
    #def #[challenge_id] (_ : 'unit) : 'bool {
      honest_root_coin <$ uniform i_bool ;;
      substituted_root_coin <$ uniform i_bool ;;
      false_first_coin <$ uniform i_bool ;;
      false_second_coin <$ uniform i_bool ;;
      false_suffix_coin <$ uniform i_bool ;;
      true_first_coin <$ uniform i_bool ;;
      true_second_coin <$ uniform i_bool ;;
      true_suffix_coin <$ uniform i_bool ;;
      ret (protocol_observation model action challenge
        (tape_of_coins honest_root_coin substituted_root_coin
          false_first_coin false_second_coin false_suffix_coin
          true_first_coin true_second_coin true_suffix_coin))
    }
  ].

Definition pqxdh_ratchet_games
  (model : attacker_model) (action : network_action) :
  loc_GamePair challenge_interface :=
  fun challenge => {locpackage pqxdh_ratchet_package model action challenge}.

(** A single value of [rom_sample] is the joint finite tape underlying the eight sequential samples in [pqxdh_ratchet_package]: two input-sensitive root entries and six symmetric-KDF answer components. Sampling the product uniformly makes the view game below a deterministic pushforward of the complete bounded protocol computation, rather than a separately postulated uniform view. *)
Definition rom_sample : Type :=
  (bool *
   (bool *
    (bool *
     (bool *
      (bool *
       (bool *
        (bool * bool)))))))%type.

Definition zero_rom_sample : rom_sample :=
  (false,
   (false,
    (false,
     (false,
      (false,
       (false,
        (false, false))))))).

Definition uniform_rom_sample : {distr rom_sample / R} :=
  @uniform_F _ zero_rom_sample.

Definition sample_to_tape (sample : rom_sample) : rom_tape :=
  let '(honest_root_coin,
        (substituted_root_coin,
         (false_first_coin,
          (false_second_coin,
           (false_suffix_coin,
            (true_first_coin,
             (true_second_coin, true_suffix_coin))))))) := sample in
  tape_of_bits honest_root_coin substituted_root_coin
    false_first_coin false_second_coin false_suffix_coin
    true_first_coin true_second_coin true_suffix_coin.

Definition sample_of_coins
  (honest_root_coin substituted_root_coin
   false_first_coin false_second_coin false_suffix_coin
   true_first_coin true_second_coin true_suffix_coin : rom_coin) : rom_sample :=
  (coin_to_bool honest_root_coin,
   (coin_to_bool substituted_root_coin,
    (coin_to_bool false_first_coin,
     (coin_to_bool false_second_coin,
      (coin_to_bool false_suffix_coin,
       (coin_to_bool true_first_coin,
        (coin_to_bool true_second_coin, coin_to_bool true_suffix_coin))))))).

Lemma sample_of_coins_to_tape :
  forall honest_root_coin substituted_root_coin
    false_first_coin false_second_coin false_suffix_coin
    true_first_coin true_second_coin true_suffix_coin,
    sample_to_tape
      (sample_of_coins honest_root_coin substituted_root_coin
        false_first_coin false_second_coin false_suffix_coin
        true_first_coin true_second_coin true_suffix_coin) =
    tape_of_coins honest_root_coin substituted_root_coin
      false_first_coin false_second_coin false_suffix_coin
      true_first_coin true_second_coin true_suffix_coin.
Proof. reflexivity. Qed.

Definition flip_rom_sample (sample : rom_sample) : rom_sample :=
  let '(honest_root_coin,
        (substituted_root_coin,
         (false_first_coin,
          (false_second_coin,
           (false_suffix_coin,
            (true_first_coin,
             (true_second_coin, true_suffix_coin))))))) := sample in
  (honest_root_coin,
   (substituted_root_coin,
    (negb false_first_coin,
     (false_second_coin,
      (false_suffix_coin,
       (negb true_first_coin,
        (true_second_coin, true_suffix_coin))))))).

Lemma flip_rom_sample_involutive :
  cancel flip_rom_sample flip_rom_sample.
Proof.
  move=> [honest_root_coin
    [substituted_root_coin
     [false_first_coin
      [false_second_coin
       [false_suffix_coin
        [true_first_coin
         [true_second_coin true_suffix_coin]]]]]]].
  rewrite /flip_rom_sample /= !negbK.
  reflexivity.
Qed.

Lemma flip_rom_sample_bijective : bijective flip_rom_sample.
Proof.
  exists flip_rom_sample.
  - exact flip_rom_sample_involutive.
  - exact flip_rom_sample_involutive.
Qed.

Definition protocol_sample_observation
  (model : attacker_model) (action : network_action)
  (challenge : bool) (sample : rom_sample) : bool :=
  protocol_observation model action challenge (sample_to_tape sample).

(** This equality links the deterministic return expression of the executable eight-sample package to the pure finite view computation. It does not equate the package interpreter's nested-bind distribution with the direct product distribution, because that general library path carries an unaccepted interchange dependency. *)
Lemma executable_package_body_uses_protocol_sample_observation :
  forall model action challenge honest_root_coin substituted_root_coin
    false_first_coin false_second_coin false_suffix_coin
    true_first_coin true_second_coin true_suffix_coin,
    protocol_observation model action challenge
      (tape_of_coins honest_root_coin substituted_root_coin
        false_first_coin false_second_coin false_suffix_coin
        true_first_coin true_second_coin true_suffix_coin) =
    protocol_sample_observation model action challenge
      (sample_of_coins honest_root_coin substituted_root_coin
        false_first_coin false_second_coin false_suffix_coin
        true_first_coin true_second_coin true_suffix_coin).
Proof. reflexivity. Qed.

Lemma hidden_sample_observation_flip :
  forall model action sample,
    attacker_can_recompute_accepted_root_input model action = false ->
    protocol_sample_observation model action false sample =
    protocol_sample_observation model action true (flip_rom_sample sample).
Proof.
  move=> model action
    [honest_root_coin
     [substituted_root_coin
      [false_first_coin
       [false_second_coin
        [false_suffix_coin
         [true_first_coin
          [true_second_coin true_suffix_coin]]]]]]] hidden.
  case: action hidden => hidden.
  - rewrite /protocol_sample_observation /sample_to_tape /flip_rom_sample
      /protocol_observation /record_ciphertext /establish_and_ratchet
      /derive_keys_from_input /ideal_pqxdh_root /is_substituted_pqxdh_input
      /accepted_pqxdh_input /action_is_replace /initial_ratchet_expansion
      /ratchet_step_expansion /ideal_symmetric_hkdf /tape_of_bits hidden /=.
    case: honest_root_coin => /=;
    case: false_second_coin => /=;
    case: true_second_coin => /=;
    btauto.
  - rewrite /protocol_sample_observation /sample_to_tape /flip_rom_sample
      /protocol_observation.
    case authentication:
      (ideal_bundle_authentication_accepts model Replace) => /=.
    + rewrite hidden /record_ciphertext /establish_and_ratchet
        /derive_keys_from_input /ideal_pqxdh_root /is_substituted_pqxdh_input
        /accepted_pqxdh_input /action_is_replace /initial_ratchet_expansion
        /ratchet_step_expansion /ideal_symmetric_hkdf /tape_of_bits /=.
      case: substituted_root_coin => /=;
      case: false_second_coin => /=;
      case: true_second_coin => /=;
      btauto.
    + reflexivity.
Qed.

(** This is the decision probability obtained by deterministically pushing one jointly uniform finite eight-coin tape through the actual bounded PQXDH-plus-ratchet observation and then through a deterministic distinguisher. Defining this finite pushforward directly avoids MathComp's general [dlet]/[dmargin] construction and its unaccepted infinite-sum interchange dependency in the pinned library. *)
Definition protocol_view_game
  (model : attacker_model) (action : network_action) (challenge : bool)
  (distinguisher : pred bool) : R :=
  \P_[uniform_rom_sample]
    [pred sample |
      distinguisher
        (protocol_sample_observation model action challenge sample)].

Definition protocol_view_advantage
  (model : attacker_model) (action : network_action)
  (distinguisher : pred bool) : R :=
  `| protocol_view_game model action false distinguisher -
      protocol_view_game model action true distinguisher |.

Lemma hidden_root_games_equivalent :
  forall model action,
    attacker_can_recompute_accepted_root_input model action = false ->
    forall distinguisher,
      protocol_view_game model action false distinguisher =
      protocol_view_game model action true distinguisher.
Proof.
  move=> model action hidden distinguisher.
  rewrite /protocol_view_game /pr.
  rewrite (reindex_psum
    (S := fun sample =>
      (distinguisher
        (protocol_sample_observation model action false sample))%:R *
      uniform_rom_sample sample)
    (P := predT)
    (h := flip_rom_sample)).
  - apply/eq_psum=> sample.
    rewrite (hidden_sample_observation_flip model action
      (flip_rom_sample sample) hidden).
    rewrite flip_rom_sample_involutive.
    reflexivity.
  - by move=> sample _; rewrite inE.
  - exists flip_rom_sample.
    + move=> sample; rewrite !inE => _.
      exact (flip_rom_sample_involutive sample).
    + move=> sample; rewrite !inE => _.
      exact (flip_rom_sample_involutive sample).
Qed.

Theorem hidden_root_confidentiality :
  forall model action,
    attacker_can_recompute_accepted_root_input model action = false ->
    forall distinguisher,
      protocol_view_advantage model action distinguisher = 0.
Proof.
  move=> model action hidden distinguisher.
  rewrite /protocol_view_advantage
    (hidden_root_games_equivalent model action hidden distinguisher).
  by rewrite GRing.subrr normr0.
Qed.

Theorem active_classical_confidentiality :
  forall action distinguisher,
    protocol_view_advantage active_classical action distinguisher = 0.
Proof.
  move=> action.
  exact (hidden_root_confidentiality active_classical action
    (active_classical_root_hidden action)).
Qed.

Lemma passive_classical_games_are_active_classical_games :
  pqxdh_ratchet_games passive_classical Forward =
  pqxdh_ratchet_games active_classical Forward.
Proof. reflexivity. Qed.

Lemma passive_classical_view_game_is_active_classical_view_game :
  forall challenge distinguisher,
    protocol_view_game passive_classical Forward challenge distinguisher =
    protocol_view_game active_classical Forward challenge distinguisher.
Proof. reflexivity. Qed.

Theorem passive_classical_confidentiality :
  forall distinguisher,
    protocol_view_advantage passive_classical Forward distinguisher = 0.
Proof.
  move=> distinguisher.
  rewrite /protocol_view_advantage
    !passive_classical_view_game_is_active_classical_view_game.
  exact (active_classical_confidentiality Forward distinguisher).
Qed.

Theorem passive_quantum_capability_confidentiality :
  forall distinguisher,
    protocol_view_advantage passive_quantum Forward distinguisher = 0.
Proof.
  apply (hidden_root_confidentiality passive_quantum Forward).
  reflexivity.
Qed.

(** This compatibility alias states security only for the explicit classical-query capability game above. In particular, its name must not be read as a QROM theorem or as a proof against superposition oracle queries. *)
Corollary passive_quantum_confidentiality :
  forall distinguisher,
    protocol_view_advantage passive_quantum Forward distinguisher = 0.
Proof. exact passive_quantum_capability_confidentiality. Qed.

(** The identity event is a concrete distinguisher after active quantum substitution: it returns the plaintext recovered by reproducing the PQXDH-root and symmetric-ratchet oracle queries under the attacker-selected ML-KEM secret. *)
Definition recovered_plaintext_distinguisher : pred bool := fun view => view.

Lemma active_quantum_sample_observation :
  forall challenge sample,
    protocol_sample_observation active_quantum Replace challenge sample = challenge.
Proof.
  move=> challenge sample.
  exact (active_quantum_recovers_challenge challenge (sample_to_tape sample)).
Qed.

(** This event-level theorem is an explicit advantage-one attack on every finite ROM tape. *)
Theorem active_quantum_per_tape_perfect_distinguishing_witness :
  forall sample,
    recovered_plaintext_distinguisher
      (protocol_sample_observation active_quantum Replace false sample) = false /\
    recovered_plaintext_distinguisher
      (protocol_sample_observation active_quantum Replace true sample) = true.
Proof.
  move=> sample.
  rewrite /recovered_plaintext_distinguisher
    !active_quantum_sample_observation.
  by split.
Qed.

Lemma uniform_rom_sample_lossless :
  \P_[uniform_rom_sample] predT = 1.
Proof.
  rewrite pr_predT psum_fin /uniform_rom_sample /uniform_F /=.
  rewrite /index_enum -enumT sumr_const /r.
  have r_ge_zero : 0 <= (@r _ zero_rom_sample) := r_nonneg.
  rewrite (ger0_norm r_ge_zero).
  rewrite /r GRing.mulrC -GRing.invf_div GRing.divr1 GRing.divff //.
  exact (@card_non_zero _ zero_rom_sample).
Qed.

Lemma active_quantum_false_decision_probability_zero :
  protocol_view_game active_quantum Replace false
    recovered_plaintext_distinguisher = 0.
Proof.
  rewrite /protocol_view_game.
  transitivity (\P_[uniform_rom_sample] pred0).
  - apply/eq_pr=> sample.
    rewrite !inE /recovered_plaintext_distinguisher.
    exact (active_quantum_sample_observation false sample).
  - exact (pr_pred0 uniform_rom_sample).
Qed.

Lemma active_quantum_true_decision_probability_one :
  protocol_view_game active_quantum Replace true
    recovered_plaintext_distinguisher = 1.
Proof.
  rewrite /protocol_view_game.
  transitivity (\P_[uniform_rom_sample] predT).
  - apply/eq_pr=> sample.
    rewrite !inE /recovered_plaintext_distinguisher.
    exact (active_quantum_sample_observation true sample).
  - exact uniform_rom_sample_lossless.
Qed.

Theorem active_quantum_advantage_one :
  protocol_view_advantage active_quantum Replace
    recovered_plaintext_distinguisher = 1.
Proof.
  rewrite /protocol_view_advantage
    active_quantum_false_decision_probability_zero
    active_quantum_true_decision_probability_one.
  by rewrite GRing.sub0r normrN normr1.
Qed.

Print Assumptions active_classical_confidentiality.
Print Assumptions passive_classical_confidentiality.
Print Assumptions passive_quantum_confidentiality.
Print Assumptions active_quantum_per_tape_perfect_distinguishing_witness.
Print Assumptions active_quantum_advantage_one.
Print Assumptions hidden_root_games_equivalent.
