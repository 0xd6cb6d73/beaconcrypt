(* SPDX-License-Identifier: 0BSD *)

(** A bounded two-session extension of the state-separated response seam.

    The one-call package deliberately tombstones its two role slots, so a
    stateless monolithic package is observably different on a second call.
    This module instead gives each Boolean session handle its own server and
    beacon slot and compares repeated calls with a stateful reference that
    records used handles.  One complete finite ROM tape is sampled on the
    first fresh authenticated call and cached for every later session.  A new
    tape per session would incorrectly allow equal KDF queries to receive
    different answers and would hide cross-session collisions.

    Session handles select only private CKEY locations and static protocol
    inputs.  They are not added to the PQXDH root, symmetric-ratchet input,
    direction, sequence, or any domain label. *)

From Stdlib Require Import Bool Utf8 Logic.ProofIrrelevance.

From SSProve.Relational Require Import OrderEnrichedCategory
  GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq fintype.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms Casts ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl Package Prelude pkg_core_definition.
From BeaconcryptSSProve Require Import ProtocolLabels PqxdhRatchetGames
  StateSeparatedComposition StateSeparatedPackageSemantics.
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

(** Static protocol parameters for the two bounded sessions. *)
Definition session_pair (value : Type) : Type := (value * value)%type.

Definition select_session {value : Type}
    (session : bounded_session_handle) (values : session_pair value) : value :=
  if session then values.2 else values.1.

Lemma select_session_false {value : Type} (values : session_pair value) :
  select_session false values = values.1.
Proof. reflexivity. Qed.

Lemma select_session_true {value : Type} (values : session_pair value) :
  select_session true values = values.2.
Proof. reflexivity. Qed.

(** The old role locations become session zero.  Session one gets two fresh,
    statically disjoint locations, while the outer driver owns a separate
    cache containing the single joint ROM tape. *)
Definition server_session_one_loc : Location := (chCkeySlot; 82%N).
Definition beacon_session_one_loc : Location := (chCkeySlot; 83%N).
Definition chCachedRomSample : choice_type := chOption chRomSample.
Definition indexed_rom_cache_loc : Location := (chCachedRomSample; 84%N).

Definition indexed_server_ckey_loc
    (session : bounded_session_handle) : Location :=
  if session then server_session_one_loc else server_ckey_loc.

Definition indexed_beacon_ckey_loc
    (session : bounded_session_handle) : Location :=
  if session then beacon_session_one_loc else beacon_ckey_loc.

Definition indexed_ckey_locs : {fset Location} :=
  fset [:: server_ckey_loc; beacon_ckey_loc;
    server_session_one_loc; beacon_session_one_loc].

Definition indexed_cache_locs : {fset Location} :=
  fset [:: indexed_rom_cache_loc].

Definition indexed_response_locs : {fset Location} :=
  indexed_ckey_locs :|: indexed_cache_locs.

Definition get_indexed_server_slot
    (state : heap) (session : bounded_session_handle) : ckey_slot :=
  if session
  then get_heap state server_session_one_loc
  else get_heap state server_ckey_loc.

Definition get_indexed_beacon_slot
    (state : heap) (session : bounded_session_handle) : ckey_slot :=
  if session
  then get_heap state beacon_session_one_loc
  else get_heap state beacon_ckey_loc.

Lemma indexed_role_session_locations_are_distinct :
  server_ckey_loc <> beacon_ckey_loc /\
  server_ckey_loc <> server_session_one_loc /\
  server_ckey_loc <> beacon_session_one_loc /\
  beacon_ckey_loc <> server_session_one_loc /\
  beacon_ckey_loc <> beacon_session_one_loc /\
  server_session_one_loc <> beacon_session_one_loc.
Proof.
  repeat split; move=> locations_equal;
    have indices_equal :=
      f_equal (fun location : Location => location.π2) locations_equal;
    discriminate indices_equal.
Qed.

Lemma indexed_server_beacon_locations_neq
    (server_session beacon_session : bounded_session_handle) :
  indexed_server_ckey_loc server_session !=
    indexed_beacon_ckey_loc beacon_session.
Proof.
  case: server_session; case: beacon_session;
    apply/negP; move=> /eqP locations_equal;
    have indices_equal :=
      f_equal (fun location : Location => location.π2) locations_equal;
    discriminate indices_equal.
Qed.

Lemma indexed_server_sessions_are_disjoint
    (session : bounded_session_handle) :
  indexed_server_ckey_loc session !=
    indexed_server_ckey_loc (negb session).
Proof.
  case: session;
    apply/negP; move=> /eqP locations_equal;
    have indices_equal :=
      f_equal (fun location : Location => location.π2) locations_equal;
    discriminate indices_equal.
Qed.

Lemma indexed_beacon_sessions_are_disjoint
    (session : bounded_session_handle) :
  indexed_beacon_ckey_loc session !=
    indexed_beacon_ckey_loc (negb session).
Proof.
  case: session;
    apply/negP; move=> /eqP locations_equal;
    have indices_equal :=
      f_equal (fun location : Location => location.π2) locations_equal;
    discriminate indices_equal.
Qed.

(** Private CKEY freshness is a read-only check over the selected role slots.
    A partially installed or already consumed session is therefore not fresh. *)
Definition indexed_fresh_id : nat := 89%N.

Definition indexed_ckey_keying_interface : Interface :=
  [interface
    #val #[put_server_id] : 'payload → 'unit ;
    #val #[put_beacon_id] : 'payload → 'unit ;
    #val #[indexed_fresh_id] : 'bool → 'bool
  ].

Definition indexed_ckey_interface : Interface :=
  [interface
    #val #[put_server_id] : 'payload → 'unit ;
    #val #[put_beacon_id] : 'payload → 'unit ;
    #val #[take_server_id] : 'bool → 'payload ;
    #val #[take_beacon_id] : 'bool → 'payload ;
    #val #[indexed_fresh_id] : 'bool → 'bool
  ].

Definition indexed_consuming_ckey :
    package indexed_ckey_locs [interface] indexed_ckey_interface :=
  [package
    #def #[put_server_id] (payload : 'payload) : 'unit {
      if payload_session payload then
        slot ← get server_session_one_loc ;;
        #assert (slot == None) ;;
        #assert (payload_role payload == server_role) ;;
        #put server_session_one_loc := Some (false, payload) ;;
        @ret 'unit Datatypes.tt
      else
        slot ← get server_ckey_loc ;;
        #assert (slot == None) ;;
        #assert (payload_role payload == server_role) ;;
        #put server_ckey_loc := Some (false, payload) ;;
        @ret 'unit Datatypes.tt
    } ;
    #def #[put_beacon_id] (payload : 'payload) : 'unit {
      if payload_session payload then
        slot ← get beacon_session_one_loc ;;
        #assert (slot == None) ;;
        #assert (payload_role payload == beacon_role) ;;
        #put beacon_session_one_loc := Some (false, payload) ;;
        @ret 'unit Datatypes.tt
      else
        slot ← get beacon_ckey_loc ;;
        #assert (slot == None) ;;
        #assert (payload_role payload == beacon_role) ;;
        #put beacon_ckey_loc := Some (false, payload) ;;
        @ret 'unit Datatypes.tt
    } ;
    #def #[take_server_id] (session : 'bool) : 'payload {
      if session then
        slot ← get server_session_one_loc ;;
        #assert (isSome slot) as slot_some ;;
        let marked_payload := getSome slot slot_some in
        #assert (marked_payload.1 == false) ;;
        let payload := marked_payload.2 in
        #assert (payload_role payload == server_role) ;;
        #assert (payload_session payload == session) ;;
        #put server_session_one_loc := Some (true, zero_payload) ;;
        @ret 'payload payload
      else
        slot ← get server_ckey_loc ;;
        #assert (isSome slot) as slot_some ;;
        let marked_payload := getSome slot slot_some in
        #assert (marked_payload.1 == false) ;;
        let payload := marked_payload.2 in
        #assert (payload_role payload == server_role) ;;
        #assert (payload_session payload == session) ;;
        #put server_ckey_loc := Some (true, zero_payload) ;;
        @ret 'payload payload
    } ;
    #def #[take_beacon_id] (session : 'bool) : 'payload {
      if session then
        slot ← get beacon_session_one_loc ;;
        #assert (isSome slot) as slot_some ;;
        let marked_payload := getSome slot slot_some in
        #assert (marked_payload.1 == false) ;;
        let payload := marked_payload.2 in
        #assert (payload_role payload == beacon_role) ;;
        #assert (payload_session payload == session) ;;
        #put beacon_session_one_loc := Some (true, zero_payload) ;;
        @ret 'payload payload
      else
        slot ← get beacon_ckey_loc ;;
        #assert (isSome slot) as slot_some ;;
        let marked_payload := getSome slot slot_some in
        #assert (marked_payload.1 == false) ;;
        let payload := marked_payload.2 in
        #assert (payload_role payload == beacon_role) ;;
        #assert (payload_session payload == session) ;;
        #put beacon_ckey_loc := Some (true, zero_payload) ;;
        @ret 'payload payload
    } ;
    #def #[indexed_fresh_id] (session : 'bool) : 'bool {
      if session then
        server_slot ← get server_session_one_loc ;;
        beacon_slot ← get beacon_session_one_loc ;;
        @ret 'bool ((server_slot == None) && (beacon_slot == None))
      else
        server_slot ← get server_ckey_loc ;;
        beacon_slot ← get beacon_ckey_loc ;;
        @ret 'bool ((server_slot == None) && (beacon_slot == None))
    }
  ].

(** Indexed CK/CD operations carry the session only as private routing
    metadata.  The selected production input goes through the unchanged root,
    initialization, and step functions. *)
Definition chSessionSample : choice_type := chProd chBool chRomSample.
Definition chSessionSampleCiphertext : choice_type :=
  chProd chBool (chProd chRomSample chBool).

Notation "'session_sample" := chSessionSample
  (in custom pack_type at level 2).
Notation "'session_sample" := chSessionSample (at level 2) : package_scope.
Notation "'session_sample_ciphertext" := chSessionSampleCiphertext
  (in custom pack_type at level 2).
Notation "'session_sample_ciphertext" := chSessionSampleCiphertext
  (at level 2) : package_scope.

Definition indexed_available_id : nat := 90%N.
Definition indexed_setup_server_id : nat := 91%N.
Definition indexed_setup_beacon_id : nat := 92%N.
Definition indexed_seal_response_id : nat := 93%N.
Definition indexed_open_response_id : nat := 94%N.
Definition indexed_run_response_id : nat := 95%N.

Definition indexed_keying_interface : Interface :=
  [interface
    #val #[indexed_available_id] : 'bool → 'bool ;
    #val #[indexed_setup_server_id] : 'session_sample → 'unit ;
    #val #[indexed_setup_beacon_id] : 'session_sample → 'unit
  ].

Definition indexed_keyed_interface : Interface :=
  [interface
    #val #[indexed_seal_response_id] : 'session_sample → 'bool ;
    #val #[indexed_open_response_id] : 'session_sample_ciphertext → 'bool
  ].

Definition indexed_composition_core_interface : Interface :=
  [interface
    #val #[indexed_available_id] : 'bool → 'bool ;
    #val #[indexed_setup_server_id] : 'session_sample → 'unit ;
    #val #[indexed_setup_beacon_id] : 'session_sample → 'unit ;
    #val #[indexed_seal_response_id] : 'session_sample → 'bool ;
    #val #[indexed_open_response_id] : 'session_sample_ciphertext → 'bool
  ].

Definition indexed_response_interface : Interface :=
  [interface
    #val #[indexed_run_response_id] : 'bool → 'response
  ].

Definition indexed_keying_package
    (authentications : session_pair bool)
    (inputs : session_pair pqxdh_root_input) :
    package fset0 indexed_ckey_keying_interface indexed_keying_interface :=
  [package
    #def #[indexed_available_id] (session : 'bool) : 'bool {
      #import {sig #[indexed_fresh_id] : 'bool → 'bool } as FRESH ;;
      fresh ← FRESH session ;;
      @ret 'bool fresh
    } ;
    #def #[indexed_setup_server_id]
        ('(session, sample) : 'session_sample) : 'unit {
      #import {sig #[put_server_id] : 'payload → 'unit } as PUT_SERVER ;;
      let tape := sample_to_tape sample in
      let input := select_session session inputs in
      let authenticated := select_session session authentications in
      let payloads :=
        production_role_payloads session authenticated tape input in
      PUT_SERVER payloads.1 ;;
      @ret 'unit Datatypes.tt
    } ;
    #def #[indexed_setup_beacon_id]
        ('(session, sample) : 'session_sample) : 'unit {
      #import {sig #[put_beacon_id] : 'payload → 'unit } as PUT_BEACON ;;
      let tape := sample_to_tape sample in
      let input := select_session session inputs in
      let authenticated := select_session session authentications in
      let payloads :=
        production_role_payloads session authenticated tape input in
      PUT_BEACON payloads.2 ;;
      @ret 'unit Datatypes.tt
    }
  ].

Definition indexed_keyed_package
    (challenges : session_pair bool) :
    package fset0 ckey_take_interface indexed_keyed_interface :=
  [package
    #def #[indexed_seal_response_id]
        ('(session, sample) : 'session_sample) : 'bool {
      #import {sig #[take_server_id] : 'bool → 'payload } as TAKE_SERVER ;;
      server ← TAKE_SERVER session ;;
      #assert (payload_authenticated server == true) ;;
      let tape := sample_to_tape sample in
      let output :=
        ratchet_step_expansion tape (payload_send_chain server) in
      @ret 'bool (xorb (select_session session challenges) output.1.1)
    } ;
    #def #[indexed_open_response_id]
        ('(session, (sample, ciphertext)) : 'session_sample_ciphertext) : 'bool {
      #import {sig #[take_beacon_id] : 'bool → 'payload } as TAKE_BEACON ;;
      beacon ← TAKE_BEACON session ;;
      #assert (payload_authenticated beacon == true) ;;
      let tape := sample_to_tape sample in
      let output :=
        ratchet_step_expansion tape (payload_receive_chain beacon) in
      @ret 'bool (xorb ciphertext output.1.1)
    }
  ].

#[tactic=notac] Equations? indexed_composition_core
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input) :
    package indexed_ckey_locs [interface]
      indexed_composition_core_interface :=
  indexed_composition_core authentications challenges inputs :=
  {package
    (par (indexed_keying_package authentications inputs)
         (indexed_keyed_package challenges)) ∘ indexed_consuming_ckey
  }.
Proof.
  ssprove_valid.
  - instantiate (1 := (fset0 : {fset Location})).
    rewrite fsetU0.
    apply fsubsetxx.
  - unfold indexed_ckey_keying_interface, ckey_take_interface,
      indexed_ckey_interface.
    rewrite -!fset_cat; simpl; fsubset_auto.
  - unfold indexed_composition_core_interface, indexed_keying_interface,
      indexed_keyed_interface.
    rewrite -!fset_cat; simpl; fsubset_auto.
  - apply fsub0set.
  - apply fsubsetxx.
Qed.

(** The driver helper sequences one fresh session after a cached or newly
    sampled tape has been chosen. *)
Definition indexed_driver_run_with_sample
    (setup_server : (bool * rom_sample)%type -> raw_code Datatypes.unit)
    (seal : (bool * rom_sample)%type -> raw_code bool)
    (setup_beacon : (bool * rom_sample)%type -> raw_code Datatypes.unit)
    (open_response :
      (bool * (rom_sample * bool))%type -> raw_code bool)
    (session : bounded_session_handle) (sample : rom_sample) :
    raw_code public_response_observation :=
  bind (setup_server (session, sample)) (fun _ =>
  bind (seal (session, sample)) (fun ciphertext =>
  bind (setup_beacon (session, sample)) (fun _ =>
  bind (open_response (session, (sample, ciphertext))) (fun _ =>
  ret (Some ciphertext))))).

(** Per-session provenance is checked before the successful driver is chosen.
    A mixed-authentication pair therefore uses the successful driver but the
    selected false-provenance branch must still return before freshness or
    sampling.  This wrapper supplies that branch explicitly. *)
Definition indexed_authentication_driver
    (authentications : session_pair bool) :
    package indexed_cache_locs indexed_composition_core_interface
      indexed_response_interface :=
  [package
    #def #[indexed_run_response_id] (session : 'bool) : 'response {
      if select_session session authentications then
        #import {sig #[indexed_available_id] : 'bool → 'bool } as AVAILABLE ;;
        #import {sig #[indexed_setup_server_id] :
          'session_sample → 'unit } as SETUP_SERVER ;;
        #import {sig #[indexed_setup_beacon_id] :
          'session_sample → 'unit } as SETUP_BEACON ;;
        #import {sig #[indexed_seal_response_id] :
          'session_sample → 'bool } as SEAL ;;
        #import {sig #[indexed_open_response_id] :
          'session_sample_ciphertext → 'bool } as OPEN ;;
        fresh ← AVAILABLE session ;;
        if fresh then
          cached ← get indexed_rom_cache_loc ;;
          match cached with
          | Some sample =>
              SETUP_SERVER (session, sample) ;;
              ciphertext ← SEAL (session, sample) ;;
              SETUP_BEACON (session, sample) ;;
              opened_plaintext ← OPEN (session, (sample, ciphertext)) ;;
              @ret 'response (Some ciphertext)
          | None =>
              sample <$ uniform_response_sample_op ;;
              #put indexed_rom_cache_loc := Some sample ;;
              SETUP_SERVER (session, sample) ;;
              ciphertext ← SEAL (session, sample) ;;
              SETUP_BEACON (session, sample) ;;
              opened_plaintext ← OPEN (session, (sample, ciphertext)) ;;
              @ret 'response (Some ciphertext)
          end
        else @ret 'response None
      else @ret 'response None
    }
  ].

#[tactic=notac] Equations? indexed_state_separated_response_package
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input) :
    package indexed_response_locs [interface] indexed_response_interface :=
  indexed_state_separated_response_package authentications challenges inputs :=
  {package
    indexed_authentication_driver authentications ∘
      indexed_composition_core authentications challenges inputs
  }.
Proof.
  ssprove_valid.
  - unfold indexed_response_locs.
    exact: fsubsetUr.
  - unfold indexed_response_locs.
    exact: fsubsetUl.
Qed.

(** The stream evaluator records exactly whether the one joint ROM tape was
    consumed.  It rejects unresolved calls, sampler underflow, and samplers of
    any other result type. *)
Fixpoint run_response_code_with_samples
    {A : choiceType} (samples : seq rom_sample) (program : raw_code A)
    (state : heap) : option (A * heap * seq rom_sample) :=
  match program with
  | ret result => Some (result, state, samples)
  | opr _ _ _ => None
  | getr location continuation =>
      run_response_code_with_samples samples
        (continuation (get_heap state location)) state
  | putr location value continuation =>
      run_response_code_with_samples samples continuation
        (set_heap state location value)
  | sampler operation continuation =>
      match samples with
      | [::] => None
      | sample :: remaining =>
          match cast_response_sample sample operation with
          | Some value =>
              run_response_code_with_samples remaining
                (continuation value) state
          | None => None
          end
      end
  end.

Definition indexed_run_signature : opsig :=
  (indexed_run_response_id, (chBool, chPublicResponseObservation)).

Lemma run_response_code_with_samples_bind :
  forall {A B : choiceType} (samples : seq rom_sample)
    (program : raw_code A) (continuation : A -> raw_code B) state,
    run_response_code_with_samples samples (bind program continuation) state =
      match run_response_code_with_samples samples program state with
      | Some (result, next_state, remaining) =>
          run_response_code_with_samples remaining
            (continuation result) next_state
      | None => None
      end.
Proof.
  move=> A B samples program.
  revert samples.
  induction program as
    [result | C operation argument next
    | location next induction_hypothesis
    | location value program induction_hypothesis
    | operation next induction_hypothesis];
    move=> samples continuation state; cbn.
  - reflexivity.
  - reflexivity.
  - apply induction_hypothesis.
  - apply induction_hypothesis.
  - case: samples=> [| sample remaining]; first reflexivity.
    destruct (cast_response_sample sample operation); last reflexivity.
    apply induction_hypothesis.
Qed.

Definition indexed_available_signature : opsig :=
  (indexed_available_id, (chBool, chBool)).
Definition indexed_setup_server_signature : opsig :=
  (indexed_setup_server_id, (chSessionSample, chUnit)).
Definition indexed_setup_beacon_signature : opsig :=
  (indexed_setup_beacon_id, (chSessionSample, chUnit)).
Definition indexed_seal_response_signature : opsig :=
  (indexed_seal_response_id, (chSessionSample, chBool)).
Definition indexed_open_response_signature : opsig :=
  (indexed_open_response_id, (chSessionSampleCiphertext, chBool)).

(** Validity-free projections keep exact package syntax out of the reportable
    capstones. *)
Definition indexed_consuming_ckey_raw : raw_package :=
  Eval cbn in (indexed_consuming_ckey : raw_package).

Definition indexed_keying_package_raw
    (authentications : session_pair bool)
    (inputs : session_pair pqxdh_root_input) : raw_package :=
  Eval cbn in
    (indexed_keying_package authentications inputs : raw_package).

Definition indexed_keyed_package_raw
    (challenges : session_pair bool) : raw_package :=
  Eval cbn in (indexed_keyed_package challenges : raw_package).

Definition indexed_authentication_driver_raw
    (authentications : session_pair bool) : raw_package :=
  Eval cbn in
    (indexed_authentication_driver authentications : raw_package).

Definition indexed_composition_core_raw
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input) : raw_package :=
  pkg_composition.link
    (pkg_composition.par
      (indexed_keying_package_raw authentications inputs)
      (indexed_keyed_package_raw challenges))
    indexed_consuming_ckey_raw.

Definition indexed_response_package_raw
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input) : raw_package :=
  pkg_composition.link
    (indexed_authentication_driver_raw authentications)
    (indexed_composition_core_raw authentications challenges inputs).

Definition indexed_linked_run_code
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) :
    raw_code chPublicResponseObservation :=
  Eval cbn in
    get_op_default
      (indexed_response_package_raw authentications challenges inputs)
      indexed_run_signature session.

Definition indexed_role_payloads
    (authentications : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample) :
    ckey_payload * ckey_payload :=
  production_role_payloads session
    (select_session session authentications)
    (sample_to_tape sample) (select_session session inputs).

Definition indexed_response_ciphertext
    (challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample) : bool :=
  authenticated_response_ciphertext session
    (select_session session challenges) sample
    (select_session session inputs).

Definition indexed_cache_heap (sample : rom_sample) (state : heap) : heap :=
  set_heap state indexed_rom_cache_loc (Some sample).

Definition indexed_server_installed_heap
    (authentications : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample)
    (state : heap) : heap :=
  if session then
    set_heap state server_session_one_loc
      (Some (false, (indexed_role_payloads
        authentications inputs session sample).1))
  else
    set_heap state server_ckey_loc
      (Some (false, (indexed_role_payloads
        authentications inputs session sample).1)).

Definition indexed_server_consumed_heap
    (session : bounded_session_handle) (state : heap) : heap :=
  if session
  then set_heap state server_session_one_loc taken_slot
  else set_heap state server_ckey_loc taken_slot.

Definition indexed_beacon_installed_heap
    (authentications : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample)
    (state : heap) : heap :=
  if session then
    set_heap state beacon_session_one_loc
      (Some (false, (indexed_role_payloads
        authentications inputs session sample).2))
  else
    set_heap state beacon_ckey_loc
      (Some (false, (indexed_role_payloads
        authentications inputs session sample).2)).

Definition indexed_beacon_consumed_heap
    (session : bounded_session_handle) (state : heap) : heap :=
  if session
  then set_heap state beacon_session_one_loc taken_slot
  else set_heap state beacon_ckey_loc taken_slot.

Definition indexed_session_consumed_heap
    (session : bounded_session_handle) (state : heap) : heap :=
  if session then
    set_heap
      (set_heap state server_session_one_loc taken_slot)
      beacon_session_one_loc taken_slot
  else
    set_heap
      (set_heap state server_ckey_loc taken_slot)
      beacon_ckey_loc taken_slot.

Definition indexed_first_session_heap
    (session : bounded_session_handle) (sample : rom_sample) : heap :=
  indexed_session_consumed_heap session
    (indexed_cache_heap sample empty_heap).

Definition indexed_both_sessions_heap
    (first_session : bounded_session_handle) (sample : rom_sample) : heap :=
  indexed_session_consumed_heap (negb first_session)
    (indexed_first_session_heap first_session sample).

Definition indexed_opened_plaintext
    (challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample) : bool :=
  authenticated_opened_plaintext session
    (select_session session challenges) sample
    (select_session session inputs).

Lemma empty_heap_has_empty_indexed_state :
  forall session,
    get_indexed_server_slot empty_heap session = empty_slot /\
    get_indexed_beacon_slot empty_heap session = empty_slot /\
    get_heap empty_heap indexed_rom_cache_loc = None.
Proof. case=> /=; repeat split; reflexivity. Qed.

Lemma run_response_code_with_samples_link_return :
  forall {A : choiceType} samples (result : A) provider state,
    run_response_code_with_samples samples
      (pkg_composition.code_link (ret result) provider) state =
    Some (result, state, samples).
Proof. reflexivity. Qed.

(** The linked core exposes the selected pair of CKEY slots as a read-only
    freshness result. *)
Lemma indexed_core_availability_checks_slots :
  forall authentications challenges inputs session samples state,
    run_response_code_with_samples samples
      (get_op_default
        (indexed_composition_core authentications challenges inputs)
        indexed_available_signature session)
      state =
    Some
      (((get_indexed_server_slot state session == empty_slot) &&
        (get_indexed_beacon_slot state session == empty_slot)),
       state, samples).
Proof.
  move=> authentications challenges inputs session samples state.
  case: session.
  all: rewrite indexed_composition_core_equation_1 get_op_default_link.
  all: unfold indexed_available_signature, get_op_default.
  all: cbn [pkg_composition.lookup_op pkg_composition.par
    indexed_keying_package indexed_keyed_package].
  all: cbn [indexed_keying_package indexed_keyed_package
    pkg_composition.par].
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: repeat rewrite self_typed_function_cast.
  all: cbn [run_response_code_with_samples get_indexed_server_slot
    get_indexed_beacon_slot empty_slot].
  all: reflexivity.
Qed.

Lemma indexed_core_setup_server_runs :
  forall authentications challenges inputs session sample samples state,
    select_session session authentications = true ->
    get_indexed_server_slot state session = empty_slot ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_composition_core authentications challenges inputs)
        indexed_setup_server_signature (session, sample))
      state =
    Some
      (Datatypes.tt,
       indexed_server_installed_heap
         authentications inputs session sample state,
       samples).
Proof.
  move=> authentications challenges inputs session sample samples state
    authenticated_true server_empty.
  case: session authenticated_true server_empty =>
    authenticated_true server_empty.
  all: rewrite indexed_composition_core_equation_1 get_op_default_link.
  all: unfold indexed_setup_server_signature, get_op_default.
  all: cbn [pkg_composition.lookup_op pkg_composition.par
    indexed_keying_package indexed_keyed_package].
  all: cbn [indexed_keying_package indexed_keyed_package
    pkg_composition.par].
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: cbn [get_indexed_server_slot] in server_empty.
  all: rewrite run_response_code_with_samples_bind.
  all: rewrite server_empty eqxx.
  all: cbn [run_response_code_with_samples].
  all: reflexivity.
Qed.

Lemma indexed_core_seal_response_runs :
  forall authentications challenges inputs session sample samples state,
    select_session session authentications = true ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_composition_core authentications challenges inputs)
        indexed_seal_response_signature (session, sample))
      (indexed_server_installed_heap
        authentications inputs session sample state) =
    Some
      (indexed_response_ciphertext challenges inputs session sample,
       indexed_server_consumed_heap session
         (indexed_server_installed_heap
           authentications inputs session sample state),
       samples).
Proof.
  move=> authentications challenges inputs session sample samples state
    authenticated_true.
  case: session authenticated_true => authenticated_true.
  all: rewrite indexed_composition_core_equation_1 get_op_default_link.
  all: unfold indexed_seal_response_signature, get_op_default.
  all: cbn [pkg_composition.lookup_op pkg_composition.par
    indexed_keying_package indexed_keyed_package].
  all: cbn [indexed_keying_package indexed_keyed_package
    pkg_composition.par].
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: rewrite run_response_code_with_samples_bind.
  all: cbn [indexed_server_installed_heap].
  all: rewrite get_set_heap_eq.
  all: cbn [run_response_code_with_samples select_session]
    in authenticated_true.
  all: rewrite authenticated_true.
  all: repeat rewrite run_response_code_with_samples_bind.
  all: cbn [assertD isSome getSome payload_role payload_session
    payload_authenticated server_payload make_payload
    run_response_code_with_samples].
  all: cbn [indexed_response_ciphertext authenticated_response_ciphertext
    indexed_server_consumed_heap select_session payload_send_chain
    server_payload make_payload taken_slot].
  all: reflexivity.
Qed.

Lemma indexed_core_setup_beacon_runs :
  forall authentications challenges inputs session sample samples state,
    get_indexed_beacon_slot state session = empty_slot ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_composition_core authentications challenges inputs)
        indexed_setup_beacon_signature (session, sample))
      state =
    Some
      (Datatypes.tt,
       indexed_beacon_installed_heap
         authentications inputs session sample state,
       samples).
Proof.
  move=> authentications challenges inputs session sample samples state
    beacon_empty.
  case: session beacon_empty => beacon_empty.
  all: rewrite indexed_composition_core_equation_1 get_op_default_link.
  all: unfold indexed_setup_beacon_signature, get_op_default.
  all: cbn [pkg_composition.lookup_op pkg_composition.par
    indexed_keying_package indexed_keyed_package].
  all: cbn [indexed_keying_package indexed_keyed_package
    pkg_composition.par].
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: cbn [get_indexed_beacon_slot] in beacon_empty.
  all: rewrite run_response_code_with_samples_bind.
  all: rewrite beacon_empty eqxx.
  all: cbn [assertD payload_role beacon_payload make_payload
    run_response_code_with_samples indexed_beacon_installed_heap].
  all: reflexivity.
Qed.

Lemma indexed_core_open_response_runs :
  forall authentications challenges inputs session sample samples state,
    select_session session authentications = true ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_composition_core authentications challenges inputs)
        indexed_open_response_signature
          (session,
           (sample,
            indexed_response_ciphertext
              challenges inputs session sample)))
      (indexed_beacon_installed_heap
        authentications inputs session sample state) =
    Some
      (indexed_opened_plaintext challenges inputs session sample,
       indexed_beacon_consumed_heap session
         (indexed_beacon_installed_heap
           authentications inputs session sample state),
       samples).
Proof.
  move=> authentications challenges inputs session sample samples state
    authenticated_true.
  case: session authenticated_true => authenticated_true.
  all: rewrite indexed_composition_core_equation_1 get_op_default_link.
  all: unfold indexed_open_response_signature, get_op_default.
  all: cbn [pkg_composition.lookup_op pkg_composition.par
    indexed_keying_package indexed_keyed_package].
  all: cbn [indexed_keying_package indexed_keyed_package
    pkg_composition.par].
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: repeat rewrite self_typed_function_cast.
  all: simpl.
  all: rewrite run_response_code_with_samples_bind.
  all: cbn [indexed_beacon_installed_heap].
  all: rewrite get_set_heap_eq.
  all: cbn [select_session] in authenticated_true.
  all: rewrite authenticated_true.
  all: repeat rewrite run_response_code_with_samples_bind.
  all: cbn [assertD isSome getSome payload_role payload_session
    payload_authenticated beacon_payload make_payload
    run_response_code_with_samples].
  all: cbn [indexed_opened_plaintext authenticated_opened_plaintext
    indexed_response_ciphertext authenticated_response_ciphertext
    indexed_beacon_consumed_heap indexed_beacon_installed_heap
    select_session payload_receive_chain beacon_payload make_payload
    taken_slot].
  all: reflexivity.
Qed.

Lemma indexed_core_stages_leave_consumed_session :
  forall authentications inputs session sample state,
    indexed_beacon_consumed_heap session
      (indexed_beacon_installed_heap authentications inputs session sample
        (indexed_server_consumed_heap session
          (indexed_server_installed_heap
            authentications inputs session sample state))) =
    indexed_session_consumed_heap session state.
Proof.
  move=> authentications inputs session sample state.
  case: session.
  all: cbn [indexed_beacon_consumed_heap indexed_beacon_installed_heap
    indexed_server_consumed_heap indexed_server_installed_heap
    indexed_session_consumed_heap].
  all: repeat rewrite set_heap_contract.
  all: reflexivity.
Qed.

Lemma indexed_cache_preserves_role_slots :
  forall sample state session,
    get_indexed_server_slot (indexed_cache_heap sample state) session =
      get_indexed_server_slot state session /\
    get_indexed_beacon_slot (indexed_cache_heap sample state) session =
      get_indexed_beacon_slot state session.
Proof.
  move=> sample state session.
  case: session; split;
    cbn [get_indexed_server_slot get_indexed_beacon_slot
      indexed_cache_heap].
  all: rewrite get_set_heap_neq; first reflexivity.
  all: apply/negP; move=> /eqP locations_equal.
  all: have indices_equal :=
    f_equal (fun location : Location => location.π2) locations_equal.
  all: discriminate indices_equal.
Qed.

Lemma indexed_server_stages_preserve_beacon_slot :
  forall authentications inputs session sample state,
    get_indexed_beacon_slot
      (indexed_server_consumed_heap session
        (indexed_server_installed_heap
          authentications inputs session sample state)) session =
    get_indexed_beacon_slot state session.
Proof.
  move=> authentications inputs session sample state.
  case: session;
    cbn [get_indexed_beacon_slot indexed_server_consumed_heap
      indexed_server_installed_heap].
  all: repeat rewrite get_set_heap_neq; first reflexivity.
  all: apply/negP; move=> /eqP locations_equal.
  all: have indices_equal :=
    f_equal (fun location : Location => location.π2) locations_equal.
  all: discriminate indices_equal.
Qed.

(** This projection packages the four linked core calls after the driver has
    selected its cached or newly sampled tape. *)
Definition indexed_linked_driver_code
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample) :
    raw_code chPublicResponseObservation :=
  pkg_composition.code_link
    (indexed_driver_run_with_sample
      (fun argument =>
        opr indexed_setup_server_signature argument
          (fun result => ret result))
      (fun argument =>
        opr indexed_seal_response_signature argument
          (fun result => ret result))
      (fun argument =>
        opr indexed_setup_beacon_signature argument
          (fun result => ret result))
      (fun argument =>
        opr indexed_open_response_signature argument
          (fun result => ret result))
      session sample)
    (indexed_composition_core authentications challenges inputs).

Local Lemma indexed_linked_driver_runs :
  forall authentications challenges inputs session sample samples state,
    select_session session authentications = true ->
    get_indexed_server_slot state session = empty_slot ->
    get_indexed_beacon_slot state session = empty_slot ->
    run_response_code_with_samples samples
      (indexed_linked_driver_code
        authentications challenges inputs session sample)
      state =
    Some
      (Some (indexed_response_ciphertext
        challenges inputs session sample),
       indexed_session_consumed_heap session state,
       samples).
Proof.
  move=> authentications challenges inputs session sample samples state
    authenticated_true server_empty beacon_empty.
  unfold indexed_linked_driver_code, indexed_driver_run_with_sample.
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_setup_server_signature.
  rewrite indexed_core_setup_server_runs; try assumption.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_with_samples_link_return.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_seal_response_signature.
  rewrite indexed_core_seal_response_runs; try assumption.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_with_samples_link_return.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  fold indexed_setup_beacon_signature.
  rewrite indexed_core_setup_beacon_runs.
  2: rewrite indexed_server_stages_preserve_beacon_slot;
    exact beacon_empty.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  fold indexed_open_response_signature.
  rewrite indexed_core_open_response_runs; try assumption.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite run_response_code_with_samples_link_return.
  cbn -[pkg_composition.code_link get_op_default].
  rewrite indexed_core_stages_leave_consumed_session.
  reflexivity.
Qed.

(** The canonical first-success heap records one used handle, one untouched
    handle, and the globally cached tape. *)
Lemma indexed_first_session_heap_summary :
  forall session sample,
    get_indexed_server_slot
      (indexed_first_session_heap session sample) session = taken_slot /\
    get_indexed_beacon_slot
      (indexed_first_session_heap session sample) session = taken_slot /\
    get_indexed_server_slot
      (indexed_first_session_heap session sample) (negb session) =
        empty_slot /\
    get_indexed_beacon_slot
      (indexed_first_session_heap session sample) (negb session) =
        empty_slot /\
    get_heap (indexed_first_session_heap session sample)
      indexed_rom_cache_loc = Some sample.
Proof.
  case=> sample;
    cbn [get_indexed_server_slot get_indexed_beacon_slot
      indexed_first_session_heap indexed_session_consumed_heap
      indexed_cache_heap]; repeat split; simpl.
  all: repeat first
    [ rewrite get_set_heap_eq
    | rewrite get_set_heap_neq;
      [| apply/negP; move=> /eqP locations_equal;
         have indices_equal :=
           f_equal (fun location : Location => location.π2)
             locations_equal;
         discriminate indices_equal] ].
  all: try rewrite get_empty_heap.
  all: reflexivity.
Qed.

(** After both distinct handles succeed, all four CKEY slots are tombstoned
    and the original global tape remains cached. *)
Lemma indexed_both_sessions_heap_summary :
  forall session sample,
    get_indexed_server_slot
      (indexed_both_sessions_heap session sample) false = taken_slot /\
    get_indexed_beacon_slot
      (indexed_both_sessions_heap session sample) false = taken_slot /\
    get_indexed_server_slot
      (indexed_both_sessions_heap session sample) true = taken_slot /\
    get_indexed_beacon_slot
      (indexed_both_sessions_heap session sample) true = taken_slot /\
    get_heap (indexed_both_sessions_heap session sample)
      indexed_rom_cache_loc = Some sample.
Proof.
  case=> sample;
    cbn [get_indexed_server_slot get_indexed_beacon_slot
      indexed_both_sessions_heap indexed_first_session_heap
      indexed_session_consumed_heap indexed_cache_heap];
    repeat split; simpl.
  all: repeat first
    [ rewrite get_set_heap_eq
    | rewrite get_set_heap_neq;
      [| apply/negP; move=> /eqP locations_equal;
         have indices_equal :=
           f_equal (fun location : Location => location.π2)
             locations_equal;
         discriminate indices_equal] ].
  all: try rewrite get_empty_heap.
  all: reflexivity.
Qed.

(** False provenance is rejected before freshness, cache access, sampling,
    or any state mutation. *)
Local Lemma checked_indexed_rejected_run_neutral :
  forall authentications challenges inputs session samples state,
    select_session session authentications = false ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      state =
    Some (None, state, samples).
Proof.
  move=> authentications challenges inputs session samples state
    authenticated_false.
  rewrite indexed_state_separated_response_package_equation_1
    get_op_default_link.
  cbn [indexed_authentication_driver].
  unfold indexed_run_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite authenticated_false.
  reflexivity.
Qed.

(** Authenticated but unavailable handles return [None] after a read-only
    freshness check.  In particular, neither the heap nor sample stream is
    changed. *)
Local Lemma checked_indexed_unavailable_run_neutral :
  forall authentications challenges inputs session samples state,
    select_session session authentications = true ->
    ((get_indexed_server_slot state session == empty_slot) &&
     (get_indexed_beacon_slot state session == empty_slot)) = false ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      state =
    Some (None, state, samples).
Proof.
  move=> authentications challenges inputs session samples state
    authenticated_true unavailable.
  rewrite indexed_state_separated_response_package_equation_1
    get_op_default_link.
  cbn [indexed_authentication_driver].
  unfold indexed_run_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite authenticated_true.
  cbn [run_response_code_with_samples].
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_available_signature.
  rewrite indexed_core_availability_checks_slots.
  rewrite run_response_code_with_samples_link_return.
  rewrite unavailable.
  reflexivity.
Qed.

(** The first fresh authenticated call consumes exactly the head sample,
    caches it, produces the selected monolithic ciphertext, and tombstones
    only that handle's two role slots. *)
Local Lemma checked_indexed_first_fresh_run :
  forall authentications challenges inputs session sample remaining,
    select_session session authentications = true ->
    run_response_code_with_samples (sample :: remaining)
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      empty_heap =
    Some
      (Some (indexed_response_ciphertext
        challenges inputs session sample),
       indexed_first_session_heap session sample,
       remaining).
Proof.
  move=> authentications challenges inputs session sample remaining
    authenticated_true.
  destruct (empty_heap_has_empty_indexed_state session) as
    [server_empty [beacon_empty cache_empty]].
  rewrite indexed_state_separated_response_package_equation_1
    get_op_default_link.
  cbn [indexed_authentication_driver].
  unfold indexed_run_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite authenticated_true.
  cbn [run_response_code_with_samples].
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_available_signature.
  rewrite indexed_core_availability_checks_slots.
  rewrite run_response_code_with_samples_link_return.
  rewrite server_empty beacon_empty !eqxx.
  cbn [andb].
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite cache_empty.
  cbn.
  destruct (choice_type_eqP chRomSample chRomSample) as
    [sample_equal | sample_different].
  2: elim sample_different; reflexivity.
  assert (sample_equal = erefl) as -> by apply proof_irrelevance.
  cbn.
  change
    (run_response_code_with_samples remaining
      (indexed_linked_driver_code
        authentications challenges inputs session sample)
      (indexed_cache_heap sample empty_heap) =
     Some
       (Some (indexed_response_ciphertext
         challenges inputs session sample),
        indexed_first_session_heap session sample,
        remaining)).
  rewrite indexed_linked_driver_runs; try assumption.
  unfold indexed_first_session_heap.
  reflexivity.
Qed.

(** An authenticated fresh call with no external tape fails by sampler
    underflow after read-only availability and cache checks. *)
Local Lemma checked_indexed_first_fresh_underflow :
  forall authentications challenges inputs session,
    select_session session authentications = true ->
    run_response_code_with_samples [::]
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      empty_heap = None.
Proof.
  move=> authentications challenges inputs session authenticated_true.
  destruct (empty_heap_has_empty_indexed_state session) as
    [server_empty [beacon_empty cache_empty]].
  rewrite indexed_state_separated_response_package_equation_1
    get_op_default_link.
  cbn [indexed_authentication_driver].
  unfold indexed_run_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite authenticated_true.
  cbn [run_response_code_with_samples].
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_available_signature.
  rewrite indexed_core_availability_checks_slots.
  rewrite run_response_code_with_samples_link_return.
  rewrite server_empty beacon_empty !eqxx.
  cbn [andb].
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite cache_empty.
  reflexivity.
Qed.

(** A fresh opposite handle reuses the cached tape and therefore consumes no
    further external sample. *)
Local Lemma checked_indexed_other_handle_uses_cached_sample :
  forall authentications challenges inputs first_session sample samples,
    select_session (negb first_session) authentications = true ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature (negb first_session))
      (indexed_first_session_heap first_session sample) =
    Some
      (Some (indexed_response_ciphertext
        challenges inputs (negb first_session) sample),
       indexed_both_sessions_heap first_session sample,
       samples).
Proof.
  move=> authentications challenges inputs first_session sample samples
    authenticated_true.
  destruct (indexed_first_session_heap_summary first_session sample) as
    [used_server
      [used_beacon [server_empty [beacon_empty cache_present]]]].
  rewrite indexed_state_separated_response_package_equation_1
    get_op_default_link.
  cbn [indexed_authentication_driver].
  unfold indexed_run_signature, get_op_default.
  cbn [pkg_composition.lookup_op].
  rewrite setmE eq_refl.
  cbn [pkg_composition.mkdef].
  rewrite self_typed_function_cast.
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite authenticated_true.
  cbn [run_response_code_with_samples].
  rewrite !pkg_composition.code_link_bind.
  rewrite code_link_operation_uses_default
    run_response_code_with_samples_bind.
  rewrite run_response_code_with_samples_bind.
  fold indexed_available_signature.
  rewrite indexed_core_availability_checks_slots.
  rewrite run_response_code_with_samples_link_return.
  rewrite server_empty beacon_empty !eqxx.
  cbn [andb].
  cbn [pkg_composition.code_link run_response_code_with_samples].
  rewrite cache_present.
  cbn.
  change
    (run_response_code_with_samples samples
      (indexed_linked_driver_code authentications challenges inputs
        (negb first_session) sample)
      (indexed_first_session_heap first_session sample) =
     Some
       (Some (indexed_response_ciphertext challenges inputs
         (negb first_session) sample),
        indexed_both_sessions_heap first_session sample,
        samples)).
  rewrite indexed_linked_driver_runs; try assumption.
  unfold indexed_both_sessions_heap.
  reflexivity.
Qed.

(** Reusing the first successful handle returns [None] and preserves both the
    exact heap and residual sample stream. *)
Local Lemma checked_indexed_reused_handle_run_neutral :
  forall authentications challenges inputs session sample samples,
    select_session session authentications = true ->
    run_response_code_with_samples samples
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      (indexed_first_session_heap session sample) =
    Some
      (None, indexed_first_session_heap session sample, samples).
Proof.
  move=> authentications challenges inputs session sample samples
    authenticated_true.
  destruct (indexed_first_session_heap_summary session sample) as
    [server_taken
      [beacon_taken [other_server [other_beacon cache_present]]]].
  apply checked_indexed_unavailable_run_neutral;
    first exact authenticated_true.
  rewrite server_taken.
  reflexivity.
Qed.

(** Only reachable states occur in the pure reference.  The first successful
    handle is retained after both handles are used so the reference has an
    exact canonical heap representation. *)
Inductive indexed_reference_state : Type :=
| IndexedReferenceFresh
| IndexedReferenceOneUsed
    (first_session : bounded_session_handle) (sample : rom_sample)
| IndexedReferenceBothUsed
    (first_session : bounded_session_handle) (sample : rom_sample).

Definition empty_indexed_reference_state : indexed_reference_state :=
  IndexedReferenceFresh.

Definition indexed_reference_heap (state : indexed_reference_state) : heap :=
  match state with
  | IndexedReferenceFresh => empty_heap
  | IndexedReferenceOneUsed first_session sample =>
      indexed_first_session_heap first_session sample
  | IndexedReferenceBothUsed first_session sample =>
      indexed_both_sessions_heap first_session sample
  end.

Definition indexed_reference_ciphertext
    (challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (sample : rom_sample) :
    public_response_observation :=
  monolithic_public_response_observation
    (select_session session challenges) sample
    (select_session session inputs).

(** Each successful indexed response is exactly the existing monolithic
    observation for the selected static parameters. *)
Theorem indexed_response_matches_monolithic :
  forall challenges inputs session sample,
    Some (indexed_response_ciphertext challenges inputs session sample) =
      indexed_reference_ciphertext challenges inputs session sample.
Proof.
  move=> challenges inputs session sample.
  unfold indexed_response_ciphertext, indexed_reference_ciphertext,
    monolithic_public_response_observation.
  rewrite authenticated_response_ciphertext_matches_separated.
  rewrite (separated_first_response_matches_monolithic session true
    (select_session session challenges) (sample_to_tape sample)
    (select_session session inputs) erefl).
  reflexivity.
Qed.

(** A rejected call is neutral.  The first successful call consumes and
    caches one complete ROM tape; the other handle reuses it; every later
    call is neutral. *)
Definition indexed_reference_step
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (session : bounded_session_handle) (samples : seq rom_sample)
    (state : indexed_reference_state) :
    option
      (public_response_observation * indexed_reference_state *
       seq rom_sample) :=
  if select_session session authentications then
    match state with
    | IndexedReferenceFresh =>
        match samples with
        | [::] => None
        | sample :: remaining =>
            Some
              (indexed_reference_ciphertext
                 challenges inputs session sample,
               IndexedReferenceOneUsed session sample,
               remaining)
        end
    | IndexedReferenceOneUsed first_session sample =>
        if Bool.eqb session first_session then
          Some (None, state, samples)
        else
          Some
            (indexed_reference_ciphertext
               challenges inputs session sample,
             IndexedReferenceBothUsed first_session sample,
             samples)
    | IndexedReferenceBothUsed _ _ => Some (None, state, samples)
    end
  else Some (None, state, samples).

Fixpoint run_indexed_reference_trace
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (requests : seq bounded_session_handle) (samples : seq rom_sample)
    (state : indexed_reference_state) :
    option
      (seq public_response_observation * indexed_reference_state *
       seq rom_sample) :=
  match requests with
  | [::] => Some ([::], state, samples)
  | session :: remaining_requests =>
      match indexed_reference_step
        authentications challenges inputs session samples state
      with
      | None => None
      | Some (observation, next_state, remaining_samples) =>
          match run_indexed_reference_trace
            authentications challenges inputs remaining_requests
            remaining_samples next_state
          with
          | None => None
          | Some (observations, final_state, residual_samples) =>
              Some
                (observation :: observations, final_state,
                 residual_samples)
          end
      end
  end.

(** Finite public contexts may choose their next handle after seeing the
    previous optional ciphertext. *)
Inductive indexed_public_context : Type :=
| IndexedContextReturn (result : bool)
| IndexedContextCall
    (session : bounded_session_handle)
    (continuation : public_response_observation -> indexed_public_context).

Fixpoint run_indexed_reference_context
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (samples : seq rom_sample)
    (state : indexed_reference_state) :
    option (bool * indexed_reference_state * seq rom_sample) :=
  match context with
  | IndexedContextReturn result => Some (result, state, samples)
  | IndexedContextCall session continuation =>
      match indexed_reference_step
        authentications challenges inputs session samples state
      with
      | None => None
      | Some (observation, next_state, remaining_samples) =>
          run_indexed_reference_context
            authentications challenges inputs (continuation observation)
            remaining_samples next_state
      end
  end.

(** Exact package/reference one-step equality over every reachable reference
    state.  This local theorem retains checked package syntax; later
    certificates erase that syntax before exposing public capstones. *)
Local Lemma checked_indexed_step_matches_reference :
  forall authentications challenges inputs session samples state,
    run_response_code_with_samples samples
      (get_op_default
        (indexed_state_separated_response_package
          authentications challenges inputs)
        indexed_run_signature session)
      (indexed_reference_heap state) =
    match indexed_reference_step
      authentications challenges inputs session samples state
    with
    | None => None
    | Some (observation, next_state, remaining_samples) =>
        Some
          (observation, indexed_reference_heap next_state,
           remaining_samples)
    end.
Proof.
  move=> authentications challenges inputs session samples state.
  case authenticated: (select_session session authentications).
  2: rewrite /indexed_reference_step authenticated;
    apply checked_indexed_rejected_run_neutral;
    exact authenticated.
  destruct state as
    [| first_session cached_sample | first_session cached_sample].
  - rewrite /indexed_reference_step authenticated /=.
    destruct samples as [| sample remaining].
    + apply checked_indexed_first_fresh_underflow.
      exact authenticated.
    + rewrite checked_indexed_first_fresh_run; last exact authenticated.
      rewrite indexed_response_matches_monolithic.
      reflexivity.
  - destruct session, first_session.
    + rewrite /indexed_reference_step authenticated /=.
      rewrite checked_indexed_reused_handle_run_neutral;
        first reflexivity.
      exact authenticated.
    + rewrite /indexed_reference_step authenticated /=.
      rewrite (checked_indexed_other_handle_uses_cached_sample
        authentications challenges inputs false cached_sample samples
        authenticated).
      rewrite indexed_response_matches_monolithic.
      reflexivity.
    + rewrite /indexed_reference_step authenticated /=.
      rewrite (checked_indexed_other_handle_uses_cached_sample
        authentications challenges inputs true cached_sample samples
        authenticated).
      rewrite indexed_response_matches_monolithic.
      reflexivity.
    + rewrite /indexed_reference_step authenticated /=.
      rewrite checked_indexed_reused_handle_run_neutral;
        first reflexivity.
      exact authenticated.
  - rewrite /indexed_reference_step authenticated /=.
    destruct (indexed_both_sessions_heap_summary
      first_session cached_sample) as
      [server_zero
        [beacon_zero [server_one [beacon_one cache_present]]]].
    assert
      (((get_indexed_server_slot
          (indexed_both_sessions_heap first_session cached_sample)
          session == empty_slot) &&
        (get_indexed_beacon_slot
          (indexed_both_sessions_heap first_session cached_sample)
          session == empty_slot)) = false) as unavailable.
    { destruct session.
      - rewrite server_one.
        reflexivity.
      - rewrite server_zero.
        reflexivity. }
    rewrite checked_indexed_unavailable_run_neutral;
      first reflexivity.
    + exact authenticated.
    + exact unavailable.
Qed.

Local Fixpoint run_indexed_package_trace
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (requests : seq bounded_session_handle) (samples : seq rom_sample)
    (state : heap) :
    option
      (seq public_response_observation * heap * seq rom_sample) :=
  match requests with
  | [::] => Some ([::], state, samples)
  | session :: remaining_requests =>
      match run_response_code_with_samples samples
        (get_op_default
          (indexed_state_separated_response_package
            authentications challenges inputs)
          indexed_run_signature session)
        state
      with
      | None => None
      | Some (observation, next_state, remaining_samples) =>
          match run_indexed_package_trace
            authentications challenges inputs remaining_requests
            remaining_samples next_state
          with
          | None => None
          | Some (observations, final_state, residual_samples) =>
              Some
                (observation :: observations, final_state,
                 residual_samples)
          end
      end
  end.

Local Fixpoint run_indexed_package_context
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (samples : seq rom_sample)
    (state : heap) : option (bool * heap * seq rom_sample) :=
  match context with
  | IndexedContextReturn result => Some (result, state, samples)
  | IndexedContextCall session continuation =>
      match run_response_code_with_samples samples
        (get_op_default
          (indexed_state_separated_response_package
            authentications challenges inputs)
          indexed_run_signature session)
        state
      with
      | None => None
      | Some (observation, next_state, remaining_samples) =>
          run_indexed_package_context
            authentications challenges inputs (continuation observation)
            remaining_samples next_state
      end
  end.

Local Lemma checked_indexed_trace_matches_reference :
  forall authentications challenges inputs requests samples state,
    run_indexed_package_trace
      authentications challenges inputs requests samples
      (indexed_reference_heap state) =
    match run_indexed_reference_trace
      authentications challenges inputs requests samples state
    with
    | None => None
    | Some (observations, final_state, residual_samples) =>
        Some
          (observations, indexed_reference_heap final_state,
           residual_samples)
    end.
Proof.
  move=> authentications challenges inputs requests.
  induction requests as [| session remaining_requests induction_hypothesis];
    move=> samples state; first reflexivity.
  cbn [run_indexed_package_trace run_indexed_reference_trace].
  rewrite checked_indexed_step_matches_reference.
  destruct (indexed_reference_step authentications challenges inputs
    session samples state) as
    [[[observation next_state] remaining_samples] |];
    last reflexivity.
  cbn.
  rewrite induction_hypothesis.
  destruct (run_indexed_reference_trace authentications challenges inputs
    remaining_requests remaining_samples next_state) as
    [[[observations final_state] residual_samples] |];
    reflexivity.
Qed.

Local Lemma checked_indexed_context_matches_reference :
  forall authentications challenges inputs context samples state,
    run_indexed_package_context
      authentications challenges inputs context samples
      (indexed_reference_heap state) =
    match run_indexed_reference_context
      authentications challenges inputs context samples state
    with
    | None => None
    | Some (result, final_state, residual_samples) =>
        Some
          (result, indexed_reference_heap final_state,
           residual_samples)
    end.
Proof.
  move=> authentications challenges inputs context.
  induction context as
    [result | session continuation induction_hypothesis];
    move=> samples state; first reflexivity.
  cbn [run_indexed_package_context run_indexed_reference_context].
  rewrite checked_indexed_step_matches_reference.
  destruct (indexed_reference_step authentications challenges inputs
    session samples state) as
    [[[observation next_state] remaining_samples] |];
    last reflexivity.
  cbn.
  apply induction_hypothesis.
Qed.

Definition indexed_reference_trace_normal_form
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (requests : seq bounded_session_handle) (samples : seq rom_sample) :
    option
      (seq public_response_observation * heap * seq rom_sample) :=
  match run_indexed_reference_trace
    authentications challenges inputs requests samples
    empty_indexed_reference_state
  with
  | None => None
  | Some (observations, final_state, residual_samples) =>
      Some
        (observations, indexed_reference_heap final_state,
         residual_samples)
  end.

(** The exact raw trace remains in the certificate index and soundness field.
    Kernel reduction of the projection below retains only the pure reference
    normal form. *)
Record indexed_trace_run_certificate
    (execution :
      option
        (seq public_response_observation * heap * seq rom_sample)) := {
  certified_indexed_trace_run :
    option
      (seq public_response_observation * heap * seq rom_sample);
  indexed_trace_run_certificate_sound :
    execution = certified_indexed_trace_run
}.

Definition indexed_package_trace_run_certificate
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (requests : seq bounded_session_handle) (samples : seq rom_sample) :
    indexed_trace_run_certificate
      (run_indexed_package_trace
        authentications challenges inputs requests samples empty_heap).
Proof.
  refine
    {| certified_indexed_trace_run :=
         indexed_reference_trace_normal_form
           authentications challenges inputs requests samples |}.
  apply (checked_indexed_trace_matches_reference
    authentications challenges inputs requests samples
    empty_indexed_reference_state).
Defined.

Definition indexed_package_trace_normal_form
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (requests : seq bounded_session_handle) (samples : seq rom_sample) :
    option
      (seq public_response_observation * heap * seq rom_sample) :=
  Eval cbn in
    @certified_indexed_trace_run _
      (indexed_package_trace_run_certificate
        authentications challenges inputs requests samples).

Theorem indexed_package_trace_matches_reference :
  forall authentications challenges inputs requests samples,
    indexed_package_trace_normal_form
      authentications challenges inputs requests samples =
    indexed_reference_trace_normal_form
      authentications challenges inputs requests samples.
Proof. reflexivity. Qed.

Definition indexed_reference_context_normal_form
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (samples : seq rom_sample) :
    option (bool * heap * seq rom_sample) :=
  match run_indexed_reference_context
    authentications challenges inputs context samples
    empty_indexed_reference_state
  with
  | None => None
  | Some (result, final_state, residual_samples) =>
      Some
        (result, indexed_reference_heap final_state,
         residual_samples)
  end.

Record indexed_context_run_certificate
    (execution : option (bool * heap * seq rom_sample)) := {
  certified_indexed_context_run :
    option (bool * heap * seq rom_sample);
  indexed_context_run_certificate_sound :
    execution = certified_indexed_context_run
}.

Definition indexed_package_context_run_certificate
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (samples : seq rom_sample) :
    indexed_context_run_certificate
      (run_indexed_package_context
        authentications challenges inputs context samples empty_heap).
Proof.
  refine
    {| certified_indexed_context_run :=
         indexed_reference_context_normal_form
           authentications challenges inputs context samples |}.
  apply (checked_indexed_context_matches_reference
    authentications challenges inputs context samples
    empty_indexed_reference_state).
Defined.

Definition indexed_package_context_normal_form
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (samples : seq rom_sample) :
    option (bool * heap * seq rom_sample) :=
  Eval cbn in
    @certified_indexed_context_run _
      (indexed_package_context_run_certificate
        authentications challenges inputs context samples).

Theorem indexed_package_context_matches_reference :
  forall authentications challenges inputs context samples,
    indexed_package_context_normal_form
      authentications challenges inputs context samples =
    indexed_reference_context_normal_form
      authentications challenges inputs context samples.
Proof. reflexivity. Qed.

(** A successful handle consumes the only external tape once; immediate
    handle reuse returns [None] with the first-success heap unchanged. *)
Theorem indexed_same_handle_trace_normalizes :
  forall authentications challenges inputs session sample,
    select_session session authentications = true ->
    indexed_package_trace_normal_form
      authentications challenges inputs [:: session; session] [:: sample] =
    Some
      ([:: indexed_reference_ciphertext
             challenges inputs session sample; None],
       indexed_first_session_heap session sample,
       [::]).
Proof.
  move=> authentications challenges inputs session sample authenticated.
  destruct session;
    rewrite indexed_package_trace_matches_reference;
    unfold indexed_reference_trace_normal_form;
    cbn [run_indexed_reference_trace empty_indexed_reference_state];
    rewrite /indexed_reference_step authenticated /=;
    reflexivity.
Qed.

(** Rejected provenance is visible as [None] but is otherwise exactly
    neutral, including preservation of every supplied tape. *)
Theorem indexed_rejected_trace_is_neutral :
  forall authentications challenges inputs session samples,
    select_session session authentications = false ->
    indexed_package_trace_normal_form
      authentications challenges inputs [:: session] samples =
    Some ([:: None], empty_heap, samples).
Proof.
  move=> authentications challenges inputs session samples rejected.
  rewrite indexed_package_trace_matches_reference.
  unfold indexed_reference_trace_normal_form.
  cbn [run_indexed_reference_trace empty_indexed_reference_state].
  rewrite /indexed_reference_step rejected /=.
  reflexivity.
Qed.

(** Sampler underflow remains explicit rather than being assigned a default
    tape. *)
Theorem indexed_fresh_trace_underflow_is_explicit :
  forall authentications challenges inputs session,
    select_session session authentications = true ->
    indexed_package_trace_normal_form
      authentications challenges inputs [:: session] [::] = None.
Proof.
  move=> authentications challenges inputs session authenticated.
  rewrite indexed_package_trace_matches_reference.
  unfold indexed_reference_trace_normal_form.
  cbn [run_indexed_reference_trace empty_indexed_reference_state].
  rewrite /indexed_reference_step authenticated /=.
  reflexivity.
Qed.

(** Two distinct authenticated handles both produce their selected
    monolithic observations while sharing and consuming only one tape. *)
Theorem indexed_distinct_handle_trace_normalizes :
  forall authentications challenges inputs first_session sample,
    select_session first_session authentications = true ->
    select_session (negb first_session) authentications = true ->
    indexed_package_trace_normal_form
      authentications challenges inputs
      [:: first_session; negb first_session] [:: sample] =
    Some
      ([:: indexed_reference_ciphertext
             challenges inputs first_session sample;
           indexed_reference_ciphertext
             challenges inputs (negb first_session) sample],
       indexed_both_sessions_heap first_session sample,
       [::]).
Proof.
  move=> authentications challenges inputs first_session sample
    authenticated_first authenticated_other.
  destruct first_session;
    destruct authentications as [authentication_zero authentication_one];
    destruct authentication_zero, authentication_one;
    cbn [select_session] in authenticated_first, authenticated_other;
    try discriminate;
    rewrite indexed_package_trace_matches_reference;
    unfold indexed_reference_trace_normal_form;
    cbn [run_indexed_reference_trace indexed_reference_step
      empty_indexed_reference_state indexed_reference_heap select_session];
    reflexivity.
Qed.

(** Reversing the two fresh requests reverses the public observation order
    and records the reverse handle as the first user of the shared tape. *)
Theorem indexed_reverse_handle_trace_normalizes :
  forall authentications challenges inputs first_session sample,
    select_session first_session authentications = true ->
    select_session (negb first_session) authentications = true ->
    indexed_package_trace_normal_form
      authentications challenges inputs
      [:: negb first_session; first_session] [:: sample] =
    Some
      ([:: indexed_reference_ciphertext
             challenges inputs (negb first_session) sample;
           indexed_reference_ciphertext
             challenges inputs first_session sample],
       indexed_both_sessions_heap (negb first_session) sample,
       [::]).
Proof.
  move=> authentications challenges inputs first_session sample
    authenticated_first authenticated_other.
  destruct first_session;
    destruct authentications as [authentication_zero authentication_one];
    destruct authentication_zero, authentication_one;
    cbn [select_session] in authenticated_first, authenticated_other;
    try discriminate;
    rewrite indexed_package_trace_matches_reference;
    unfold indexed_reference_trace_normal_form;
    cbn [run_indexed_reference_trace indexed_reference_step
      empty_indexed_reference_state indexed_reference_heap select_session];
    reflexivity.
Qed.

Definition indexed_private_state_summary (state : heap) :
    ckey_slot * ckey_slot * ckey_slot * ckey_slot * option rom_sample :=
  (get_indexed_server_slot state false,
   get_indexed_beacon_slot state false,
   get_indexed_server_slot state true,
   get_indexed_beacon_slot state true,
   get_heap state indexed_rom_cache_loc).

Theorem indexed_both_sessions_private_summary :
  forall first_session sample,
    indexed_private_state_summary
      (indexed_both_sessions_heap first_session sample) =
    (taken_slot, taken_slot, taken_slot, taken_slot, Some sample).
Proof.
  move=> first_session sample.
  destruct (indexed_both_sessions_heap_summary first_session sample) as
    [server_zero
      [beacon_zero [server_one [beacon_one cache_present]]]].
  unfold indexed_private_state_summary.
  rewrite server_zero beacon_zero server_one beacon_one cache_present.
  reflexivity.
Qed.

(** Both fresh-session orders end in the same observable private-state
    summary, even though the canonical heap remembers which handle ran
    first. *)
Theorem indexed_both_orders_have_same_private_summary :
  forall first_session sample,
    indexed_private_state_summary
      (indexed_both_sessions_heap first_session sample) =
    indexed_private_state_summary
      (indexed_both_sessions_heap (negb first_session) sample).
Proof.
  move=> first_session sample.
  rewrite !indexed_both_sessions_private_summary.
  reflexivity.
Qed.

(** The global cache is a fifth location, disjoint from every role/session
    slot by its statically assigned index. *)
Theorem indexed_cache_location_is_disjoint :
  indexed_rom_cache_loc <> server_ckey_loc /\
  indexed_rom_cache_loc <> beacon_ckey_loc /\
  indexed_rom_cache_loc <> server_session_one_loc /\
  indexed_rom_cache_loc <> beacon_session_one_loc.
Proof.
  repeat split; move=> locations_equal;
    have indices_equal :=
      f_equal (fun location : Location => location.π2) locations_equal;
    discriminate indices_equal.
Qed.

(** The Boolean handle is ghost routing metadata: once the selected static
    challenge and PQXDH input agree, changing the handle cannot change the
    cryptographic response. *)
Theorem indexed_session_handle_is_ghost :
  forall challenges inputs left_session right_session sample,
    select_session left_session challenges =
      select_session right_session challenges ->
    select_session left_session inputs =
      select_session right_session inputs ->
    indexed_response_ciphertext
      challenges inputs left_session sample =
    indexed_response_ciphertext
      challenges inputs right_session sample.
Proof.
  move=> challenges inputs left_session right_session sample
    challenges_equal inputs_equal.
  unfold indexed_response_ciphertext.
  rewrite !authenticated_response_ciphertext_matches_separated.
  rewrite (separated_first_response_matches_monolithic left_session true
    (select_session left_session challenges) (sample_to_tape sample)
    (select_session left_session inputs) erefl).
  rewrite (separated_first_response_matches_monolithic right_session true
    (select_session right_session challenges) (sample_to_tape sample)
    (select_session right_session inputs) erefl).
  rewrite challenges_equal inputs_equal.
  reflexivity.
Qed.

(** No session, role, direction, sequence, or phase label is introduced.
    Initialization and record steps intentionally share the exact production
    symmetric-ratchet label while retaining their production output sizes. *)
Theorem indexed_sessions_use_production_kdf_domains :
  kdf_use_info PqxdhRootDerivation = pqxdh_info /\
  kdf_use_info InitialRatchetExpansion = symmetric_ratchet_info /\
  kdf_use_info RatchetStepExpansion = symmetric_ratchet_info /\
  kdf_use_info InitialRatchetExpansion =
    kdf_use_info RatchetStepExpansion /\
  kdf_output_size PqxdhRootDerivation = 32%N /\
  kdf_output_size InitialRatchetExpansion = 64%N /\
  kdf_output_size RatchetStepExpansion = 76%N.
Proof. repeat split; reflexivity. Qed.

Definition indexed_reference_context_view
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (sample : rom_sample) : bool :=
  match indexed_reference_context_normal_form
    authentications challenges inputs context [:: sample]
  with
  | Some (result, _, _) => result
  | None => false
  end.

Definition indexed_reference_has_sample
    (state : indexed_reference_state) (samples : seq rom_sample) : Prop :=
  match state with
  | IndexedReferenceFresh => samples <> [::]
  | IndexedReferenceOneUsed _ _ | IndexedReferenceBothUsed _ _ => True
  end.

Lemma indexed_reference_step_preserves_sample_supply :
  forall authentications challenges inputs session samples state,
    indexed_reference_has_sample state samples ->
    exists observation next_state remaining_samples,
      indexed_reference_step
        authentications challenges inputs session samples state =
        Some (observation, next_state, remaining_samples) /\
      indexed_reference_has_sample next_state remaining_samples.
Proof.
  move=> authentications challenges inputs session samples state supplied.
  case authenticated: (select_session session authentications).
  - destruct state as
      [| first_session cached_sample | first_session cached_sample].
    + destruct samples as [| sample remaining].
      * elim (supplied erefl).
      * exists
          (indexed_reference_ciphertext challenges inputs session sample),
          (IndexedReferenceOneUsed session sample), remaining.
        split; first by rewrite /indexed_reference_step authenticated.
        exact I.
    + case same_session: (Bool.eqb session first_session).
      * exists None,
          (IndexedReferenceOneUsed first_session cached_sample), samples.
        split; first by rewrite /indexed_reference_step authenticated
          same_session.
        exact I.
      * exists
          (indexed_reference_ciphertext
            challenges inputs session cached_sample),
          (IndexedReferenceBothUsed first_session cached_sample), samples.
        split; first by rewrite /indexed_reference_step authenticated
          same_session.
        exact I.
    + exists None,
        (IndexedReferenceBothUsed first_session cached_sample), samples.
      split; first by rewrite /indexed_reference_step authenticated.
      exact I.
  - exists None, state, samples.
    split; first by rewrite /indexed_reference_step authenticated.
    exact supplied.
Qed.

Lemma indexed_reference_context_preserves_sample_supply :
  forall authentications challenges inputs context samples state,
    indexed_reference_has_sample state samples ->
    exists result final_state residual_samples,
      run_indexed_reference_context
        authentications challenges inputs context samples state =
        Some (result, final_state, residual_samples) /\
      indexed_reference_has_sample final_state residual_samples.
Proof.
  move=> authentications challenges inputs context.
  induction context as
    [result | session continuation induction_hypothesis];
    move=> samples state supplied.
  - exists result, state, samples.
    split; first reflexivity.
    exact supplied.
  - destruct (indexed_reference_step_preserves_sample_supply
      authentications challenges inputs session samples state supplied) as
      [observation
        [next_state
          [remaining_samples [step_result next_supplied]]]].
    destruct (induction_hypothesis observation remaining_samples
      next_state next_supplied) as
      [result [final_state [residual_samples [context_result supplied_final]]]].
    exists result, final_state, residual_samples.
    split; last exact supplied_final.
    cbn [run_indexed_reference_context].
    rewrite step_result.
    exact context_result.
Qed.

(** A singleton complete ROM tape is sufficient for every finite adaptive
    context because only the first successful fresh handle samples. *)
Theorem indexed_package_context_single_sample_is_total :
  forall authentications challenges inputs context sample,
    exists result final_state residual_samples,
      indexed_package_context_normal_form
        authentications challenges inputs context [:: sample] =
      Some (result, final_state, residual_samples).
Proof.
  move=> authentications challenges inputs context sample.
  rewrite indexed_package_context_matches_reference.
  destruct (indexed_reference_context_preserves_sample_supply
    authentications challenges inputs context [:: sample]
    empty_indexed_reference_state) as
    [result [final_reference_state [residual_samples [context_result supplied]]]].
  - move=> impossible.
    discriminate impossible.
  - exists result, (indexed_reference_heap final_reference_state),
      residual_samples.
    unfold indexed_reference_context_normal_form.
    rewrite context_result.
    reflexivity.
Qed.

Definition indexed_package_context_view
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) (sample : rom_sample) : bool :=
  match indexed_package_context_normal_form
    authentications challenges inputs context [:: sample]
  with
  | Some (result, _, _) => result
  | None => false
  end.

(** Pointwise equality covers adaptive callers because a context continuation
    may choose its next handle from the preceding optional ciphertext. *)
Theorem indexed_public_context_view_matches_reference :
  forall authentications challenges inputs context sample,
    indexed_package_context_view
      authentications challenges inputs context sample =
    indexed_reference_context_view
      authentications challenges inputs context sample.
Proof.
  move=> authentications challenges inputs context sample.
  unfold indexed_package_context_view, indexed_reference_context_view.
  rewrite indexed_package_context_matches_reference.
  reflexivity.
Qed.

Definition indexed_package_public_context_game
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) : R :=
  \P_[uniform_rom_sample]
    [pred sample |
      indexed_package_context_view
        authentications challenges inputs context sample].

Definition indexed_reference_public_context_game
    (authentications challenges : session_pair bool)
    (inputs : session_pair pqxdh_root_input)
    (context : indexed_public_context) : R :=
  \P_[uniform_rom_sample]
    [pred sample |
      indexed_reference_context_view
        authentications challenges inputs context sample].

(** Direct finite pushforward equality avoids the stock generic [Pr] path
    and its rejected infinite-sum interchange dependency. *)
Theorem indexed_public_context_game_matches_reference :
  forall authentications challenges inputs context,
    indexed_package_public_context_game
      authentications challenges inputs context =
    indexed_reference_public_context_game
      authentications challenges inputs context.
Proof.
  move=> authentications challenges inputs context.
  rewrite /indexed_package_public_context_game
    /indexed_reference_public_context_game.
  apply/eq_pr=> sample.
  change
    (indexed_package_context_view
       authentications challenges inputs context sample =
     indexed_reference_context_view
       authentications challenges inputs context sample).
  apply indexed_public_context_view_matches_reference.
Qed.

Print Assumptions indexed_role_session_locations_are_distinct.
Print Assumptions indexed_cache_location_is_disjoint.
Print Assumptions indexed_first_session_heap_summary.
Print Assumptions indexed_both_sessions_heap_summary.
Print Assumptions indexed_response_matches_monolithic.
Print Assumptions indexed_package_trace_matches_reference.
Print Assumptions indexed_package_context_matches_reference.
Print Assumptions indexed_same_handle_trace_normalizes.
Print Assumptions indexed_rejected_trace_is_neutral.
Print Assumptions indexed_fresh_trace_underflow_is_explicit.
Print Assumptions indexed_distinct_handle_trace_normalizes.
Print Assumptions indexed_reverse_handle_trace_normalizes.
Print Assumptions indexed_both_orders_have_same_private_summary.
Print Assumptions indexed_session_handle_is_ghost.
Print Assumptions indexed_sessions_use_production_kdf_domains.
Print Assumptions indexed_package_context_single_sample_is_total.
Print Assumptions indexed_public_context_view_matches_reference.
Print Assumptions indexed_public_context_game_matches_reference.
