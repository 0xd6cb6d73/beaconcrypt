(* SPDX-License-Identifier: 0BSD *)

(** This file mechanizes the first state-separating composition slice for beaconcrypt. It models one accepted registration, the server's sequence-one response, and the beacon's matching open. The public experiment samples its finite ROM tape internally and exports only an optional response ciphertext; neither the tape nor the opened plaintext crosses the public interface. It remains a single-call structural and key-correctness slice: it does not model the production record encoding, nonce, associated data, AEAD, CTX, or identifier checks, and it does not establish a package-interpreter contextual equivalence, the repeatable CKEY interface, or the computational theorem from the state-separation paper. *)

From Stdlib Require Import Bool Utf8.

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq fintype.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms Casts ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition pkg_rhl Package Prelude.
From BeaconcryptSSProve Require Import ProtocolLabels PqxdhRatchetGames.
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

(** Roles and session handles are finite ghost metadata. They are checked by CKEY but never passed to a KDF, associated-data builder, record, or CTX input. *)
Definition server_role : bool := false.
Definition beacon_role : bool := true.
Definition bounded_session_handle : Type := bool.
Definition role_chains : Type := (bool * bool)%type.
Definition ckey_payload : Type :=
  (bool * (bounded_session_handle * (bool * role_chains)))%type.

Definition payload_role (payload : ckey_payload) : bool := payload.1.
Definition payload_session (payload : ckey_payload) : bounded_session_handle := payload.2.1.
Definition payload_authenticated (payload : ckey_payload) : bool := payload.2.2.1.
Definition payload_send_chain (payload : ckey_payload) : bool := payload.2.2.2.1.
Definition payload_receive_chain (payload : ckey_payload) : bool := payload.2.2.2.2.

Definition make_payload
  (role : bool) (session : bounded_session_handle) (authenticated : bool)
  (send_chain receive_chain : bool) : ckey_payload :=
  (role, (session, (authenticated, (send_chain, receive_chain)))).

Definition server_payload
  (session : bounded_session_handle) (authenticated left right : bool) : ckey_payload :=
  make_payload server_role session authenticated left right.

Definition beacon_payload
  (session : bounded_session_handle) (authenticated left right : bool) : ckey_payload :=
  make_payload beacon_role session authenticated right left.

Theorem complementary_role_orientation :
  forall session authenticated left right,
    payload_send_chain (server_payload session authenticated left right) = left /\
    payload_receive_chain (server_payload session authenticated left right) = right /\
    payload_send_chain (beacon_payload session authenticated left right) = right /\
    payload_receive_chain (beacon_payload session authenticated left right) = left.
Proof. repeat split. Qed.

Theorem first_response_roles_share_left_half :
  forall session authenticated left right,
    payload_send_chain (server_payload session authenticated left right) =
    payload_receive_chain (beacon_payload session authenticated left right).
Proof. reflexivity. Qed.

(** A slot is [None] before installation, [Some (false, payload)] while full, and [Some (true, zero_payload)] after destructive take. The tombstone prevents reset and the zero payload clears every modeled secret and provenance field. *)
Definition zero_payload : ckey_payload :=
  make_payload server_role false false false false.

Definition ckey_slot : Type := option (bool * ckey_payload).
Definition empty_slot : ckey_slot := None.
Definition taken_slot : ckey_slot := Some (true, zero_payload).

Definition slot_put
  (expected_role : bool) (payload : ckey_payload) (slot : ckey_slot) :
  ckey_slot * bool :=
  if (slot == None) && (payload_role payload == expected_role)
  then (Some (false, payload), true)
  else (slot, false).

Definition slot_take
  (expected_role : bool) (session : bounded_session_handle) (slot : ckey_slot) :
  ckey_slot * option ckey_payload :=
  match slot with
  | Some (false, payload) =>
      if (payload_role payload == expected_role) &&
         (payload_session payload == session)
      then (taken_slot, Some payload)
      else (slot, None)
  | _ => (slot, None)
  end.

Lemma server_slot_put_then_take :
  forall session authenticated left right,
    let payload := server_payload session authenticated left right in
    let '(full, installed) := slot_put server_role payload empty_slot in
    installed = true /\
    slot_take server_role session full = (taken_slot, Some payload).
Proof.
  move=> session authenticated left right.
  rewrite /slot_put /slot_take /empty_slot /server_payload /make_payload
    /payload_role /payload_session /server_role /=.
  by rewrite eqxx.
Qed.

Lemma beacon_slot_put_then_take :
  forall session authenticated left right,
    let payload := beacon_payload session authenticated left right in
    let '(full, installed) := slot_put beacon_role payload empty_slot in
    installed = true /\
    slot_take beacon_role session full = (taken_slot, Some payload).
Proof.
  move=> session authenticated left right.
  rewrite /slot_put /slot_take /empty_slot /beacon_payload /make_payload
    /payload_role /payload_session /beacon_role /=.
  by rewrite eqxx.
Qed.

Lemma slot_duplicate_put_rejects_without_mutation :
  forall role payload,
    payload_role payload = role ->
    slot_put role payload (Some (false, payload)) =
      (Some (false, payload), false).
Proof.
  move=> role payload payload_role_eq.
  rewrite /slot_put /=.
  reflexivity.
Qed.

Lemma slot_retake_rejects_without_mutation :
  forall role session,
    slot_take role session taken_slot = (taken_slot, None).
Proof. reflexivity. Qed.

Lemma slot_cross_role_take_rejects_without_mutation :
  forall session authenticated left right,
    let payload := server_payload session authenticated left right in
    slot_take beacon_role session (Some (false, payload)) =
      (Some (false, payload), None).
Proof. reflexivity. Qed.

Lemma slot_cross_session_take_rejects_without_mutation :
  forall session authenticated left right,
    let payload := server_payload session authenticated left right in
    slot_take server_role (negb session) (Some (false, payload)) =
      (Some (false, payload), None).
Proof.
  move=> session authenticated left right.
  rewrite /slot_take /server_payload /make_payload /payload_role
    /payload_session /server_role /=.
  by case: session.
Qed.

Record private_ckey_state : Type := {
  ckey_server_slot : ckey_slot;
  ckey_beacon_slot : ckey_slot
}.

Definition empty_ckey_state : private_ckey_state :=
  {| ckey_server_slot := empty_slot;
     ckey_beacon_slot := empty_slot |}.

Definition ckey_put_server
  (payload : ckey_payload) (state : private_ckey_state) :
  private_ckey_state * bool :=
  let '(slot, installed) := slot_put server_role payload (ckey_server_slot state) in
  ({| ckey_server_slot := slot;
      ckey_beacon_slot := ckey_beacon_slot state |}, installed).

Definition ckey_put_beacon
  (payload : ckey_payload) (state : private_ckey_state) :
  private_ckey_state * bool :=
  let '(slot, installed) := slot_put beacon_role payload (ckey_beacon_slot state) in
  ({| ckey_server_slot := ckey_server_slot state;
      ckey_beacon_slot := slot |}, installed).

Definition ckey_take_server
  (session : bounded_session_handle) (state : private_ckey_state) :
  private_ckey_state * option ckey_payload :=
  let '(slot, payload) := slot_take server_role session (ckey_server_slot state) in
  ({| ckey_server_slot := slot;
      ckey_beacon_slot := ckey_beacon_slot state |}, payload).

Definition ckey_take_beacon
  (session : bounded_session_handle) (state : private_ckey_state) :
  private_ckey_state * option ckey_payload :=
  let '(slot, payload) := slot_take beacon_role session (ckey_beacon_slot state) in
  ({| ckey_server_slot := ckey_server_slot state;
      ckey_beacon_slot := slot |}, payload).

Definition separated_ckey_transfer
  (session : bounded_session_handle) (authenticated left right : bool) :
  private_ckey_state * option (ckey_payload * ckey_payload) :=
  let server := server_payload session authenticated left right in
  let beacon := beacon_payload session authenticated left right in
  let '(state, server_installed) := ckey_put_server server empty_ckey_state in
  if server_installed then
    let '(state, server_result) := ckey_take_server session state in
    let '(state, beacon_installed) := ckey_put_beacon beacon state in
    if beacon_installed then
      let '(state, beacon_result) := ckey_take_beacon session state in
      match server_result, beacon_result with
      | Some server_value, Some beacon_value =>
          (state, Some (server_value, beacon_value))
      | _, _ => (state, None)
      end
    else (state, None)
  else (state, None).

Theorem separated_ckey_transfer_is_one_way_and_role_oriented :
  forall session authenticated left right,
    separated_ckey_transfer session authenticated left right =
      ({| ckey_server_slot := taken_slot;
          ckey_beacon_slot := taken_slot |},
       Some (server_payload session authenticated left right,
             beacon_payload session authenticated left right)).
Proof.
  move=> session authenticated left right.
  by case: session; case: authenticated; case: left; case: right.
Qed.

(** The initial expansion has canonical halves [left] and [right]. Production gives the server [(send=left, receive=right)] and the beacon [(send=right, receive=left)]. The first server response steps [left]. *)
Definition production_initial_halves
  (tape : rom_tape) (input : pqxdh_root_input) : bool * bool :=
  let root := ideal_pqxdh_root tape PqxdhRootDerivation input in
  initial_ratchet_expansion tape root.

Definition production_role_payloads
  (session : bounded_session_handle) (authenticated : bool)
  (tape : rom_tape) (input : pqxdh_root_input) : ckey_payload * ckey_payload :=
  let '(left_chain, right_chain) := production_initial_halves tape input in
  (server_payload session authenticated left_chain right_chain,
   beacon_payload session authenticated left_chain right_chain).

Definition first_response_sequence : nat := 1%N.

Definition monolithic_first_response
  (challenge : bool) (tape : rom_tape) (input : pqxdh_root_input) : bool * bool :=
  let '(left_chain, _) := production_initial_halves tape input in
  let '(server_record_key, _, _) := ratchet_step_expansion tape left_chain in
  let ciphertext := xorb challenge server_record_key in
  let '(beacon_record_key, _, _) := ratchet_step_expansion tape left_chain in
  (ciphertext, xorb ciphertext beacon_record_key).

Definition separated_first_response
  (session : bounded_session_handle) (authenticated challenge : bool)
  (tape : rom_tape) (input : pqxdh_root_input) : bool * bool :=
  let '(left_chain, right_chain) := production_initial_halves tape input in
  let '(_, transferred) :=
    separated_ckey_transfer session authenticated left_chain right_chain in
  match transferred with
  | Some (server, beacon) =>
      if payload_authenticated server && payload_authenticated beacon then
        let '(server_record_key, _, _) :=
          ratchet_step_expansion tape (payload_send_chain server) in
        let ciphertext := xorb challenge server_record_key in
        let '(beacon_record_key, _, _) :=
          ratchet_step_expansion tape (payload_receive_chain beacon) in
        (ciphertext, xorb ciphertext beacon_record_key)
      else (false, false)
  | None => (false, false)
  end.

(** The public experiment exposes only the optional response ciphertext. [None] is the modeled rejection observation; the successful response's opened plaintext remains internal. [rom_sample] is proof-side bookkeeping for the deterministic body and is not an argument of the public package operation defined below. *)
Definition public_response_observation : Type := option bool.

Definition separated_public_response_observation
  (session : bounded_session_handle) (authenticated challenge : bool)
  (sample : rom_sample) (input : pqxdh_root_input) :
  public_response_observation :=
  if authenticated then
    Some
      (separated_first_response session authenticated challenge
        (sample_to_tape sample) input).1
  else None.

Definition monolithic_public_response_observation
  (challenge : bool) (sample : rom_sample) (input : pqxdh_root_input) :
  public_response_observation :=
  Some (monolithic_first_response challenge (sample_to_tape sample) input).1.

Theorem separated_first_response_matches_monolithic :
  forall session authenticated challenge tape input,
    authenticated = true ->
    separated_first_response session authenticated challenge tape input =
    monolithic_first_response challenge tape input.
Proof.
  move=> session authenticated challenge tape input ->.
  rewrite /separated_first_response /monolithic_first_response.
  case initial: (production_initial_halves tape input) => [left_chain right_chain].
  rewrite (separated_ckey_transfer_is_one_way_and_role_oriented
    session true left_chain right_chain) /=.
  reflexivity.
Qed.

Theorem separated_unauthenticated_response_rejects :
  forall session challenge tape input,
    separated_first_response session false challenge tape input =
      (false, false).
Proof.
  move=> session challenge tape input.
  rewrite /separated_first_response.
  case initial: (production_initial_halves tape input) => [left_chain right_chain].
  rewrite (separated_ckey_transfer_is_one_way_and_role_oriented
    session false left_chain right_chain) /=.
  reflexivity.
Qed.

Theorem public_response_rejects_unauthenticated_provenance :
  forall session challenge sample input,
    separated_public_response_observation session false challenge sample input =
      None.
Proof. reflexivity. Qed.

Theorem unauthenticated_public_responses_are_challenge_independent :
  forall session left_challenge right_challenge sample input,
    separated_public_response_observation
      session false left_challenge sample input =
    separated_public_response_observation
      session false right_challenge sample input.
Proof. reflexivity. Qed.

Theorem pure_public_response_observation_matches_monolithic :
  forall session authenticated challenge sample input,
    authenticated = true ->
    separated_public_response_observation session authenticated challenge
      sample input =
    monolithic_public_response_observation challenge sample input.
Proof.
  move=> session authenticated challenge sample input ->.
  rewrite /separated_public_response_observation
    /monolithic_public_response_observation /=.
  rewrite (separated_first_response_matches_monolithic
    session true challenge (sample_to_tape sample) input erefl).
  reflexivity.
Qed.

(** This direct finite pushforward has the security-shaped observation used by the redesigned package. It deliberately does not assert equality to the package interpreter's distribution. *)
Definition state_separated_public_response_view_game
  (session : bounded_session_handle) (input : pqxdh_root_input)
  (challenge : bool) (distinguisher : pred public_response_observation) : R :=
  \P_[uniform_rom_sample]
    [pred sample |
      distinguisher
        (separated_public_response_observation
          session true challenge sample input)].

Definition state_separated_public_response_advantage
  (session : bounded_session_handle) (input : pqxdh_root_input)
  (distinguisher : pred public_response_observation) : R :=
  `| state_separated_public_response_view_game
       session input false distinguisher -
     state_separated_public_response_view_game
       session input true distinguisher |.

Theorem separated_first_response_opens_sequence_one :
  forall session authenticated challenge tape input,
    authenticated = true ->
    first_response_sequence = 1%N /\
    (separated_first_response session authenticated challenge tape input).2 = challenge.
Proof.
  move=> session authenticated challenge tape input authenticated_true.
  split; first reflexivity.
  rewrite (separated_first_response_matches_monolithic
    session authenticated challenge tape input authenticated_true)
    /monolithic_first_response.
  case: (production_initial_halves tape input) => [left_chain right_chain] /=.
  case: (ratchet_step_expansion tape left_chain) => [[record next] nonce] /=.
  by rewrite xorb_assoc_reverse xorb_nilpotent xorb_false_r.
Qed.

Theorem state_separated_composition_uses_production_kdf_domains :
  kdf_use_info PqxdhRootDerivation = pqxdh_info /\
  kdf_use_info InitialRatchetExpansion = symmetric_ratchet_info /\
  kdf_use_info RatchetStepExpansion = symmetric_ratchet_info /\
  kdf_output_size PqxdhRootDerivation = 32%N /\
  kdf_output_size InitialRatchetExpansion = 64%N /\
  kdf_output_size RatchetStepExpansion = 76%N.
Proof. repeat split; reflexivity. Qed.

(** Publication belongs to the outer protocol, not to a callback from CD into CK. The records below are scenario snapshots rather than a reachability relation: they record that replay consumption precedes response construction, server publication follows sealing and serialization, and beacon publication follows successful open and binding checks. Rejection of a pending response preserves any prior server-side snapshot while terminally aborting the beacon. *)
Inductive beacon_publication : Type :=
| BeaconInitSent
| BeaconEstablished
| BeaconAborted.

Record publication_state : Type := {
  replay_identifier_consumed : bool;
  server_peer_published : bool;
  server_send_sequence : nat;
  server_receive_sequence : nat;
  beacon_state : beacon_publication;
  beacon_send_sequence : nat;
  beacon_receive_sequence : nat
}.

Definition registration_fresh_state : publication_state :=
  {| replay_identifier_consumed := false;
     server_peer_published := false;
     server_send_sequence := 0%N;
     server_receive_sequence := 0%N;
     beacon_state := BeaconInitSent;
     beacon_send_sequence := 0%N;
     beacon_receive_sequence := 0%N |}.

Definition server_root_accepted_state : publication_state :=
  {| replay_identifier_consumed := true;
     server_peer_published := false;
     server_send_sequence := 0%N;
     server_receive_sequence := 0%N;
     beacon_state := BeaconInitSent;
     beacon_send_sequence := 0%N;
     beacon_receive_sequence := 0%N |}.

Definition server_response_published_state : publication_state :=
  {| replay_identifier_consumed := true;
     server_peer_published := true;
     server_send_sequence := first_response_sequence;
     server_receive_sequence := 0%N;
     beacon_state := BeaconInitSent;
     beacon_send_sequence := 0%N;
     beacon_receive_sequence := 0%N |}.

Definition accepted_response_state : publication_state :=
  {| replay_identifier_consumed := true;
     server_peer_published := true;
     server_send_sequence := first_response_sequence;
     server_receive_sequence := 0%N;
     beacon_state := BeaconEstablished;
     beacon_send_sequence := 0%N;
     beacon_receive_sequence := first_response_sequence |}.

Definition rejected_response_state (prior : publication_state) : publication_state :=
  {| replay_identifier_consumed := replay_identifier_consumed prior;
     server_peer_published := server_peer_published prior;
     server_send_sequence := server_send_sequence prior;
     server_receive_sequence := server_receive_sequence prior;
     beacon_state := BeaconAborted;
     beacon_send_sequence := 0%N;
     beacon_receive_sequence := 0%N |}.

Definition response_pending (state : publication_state) : Prop :=
  beacon_state state = BeaconInitSent /\
  beacon_send_sequence state = 0%N /\
  beacon_receive_sequence state = 0%N.

Theorem failed_response_construction_consumes_only_replay_state :
  replay_identifier_consumed server_root_accepted_state = true /\
  server_peer_published server_root_accepted_state = false /\
  server_send_sequence server_root_accepted_state = 0%N /\
  server_receive_sequence server_root_accepted_state = 0%N /\
  beacon_state server_root_accepted_state = BeaconInitSent.
Proof. repeat split. Qed.

Theorem dropped_response_has_asymmetric_publication :
  server_peer_published server_response_published_state = true /\
  server_send_sequence server_response_published_state = 1%N /\
  server_receive_sequence server_response_published_state = 0%N /\
  beacon_state server_response_published_state = BeaconInitSent /\
  beacon_send_sequence server_response_published_state = 0%N /\
  beacon_receive_sequence server_response_published_state = 0%N.
Proof. repeat split. Qed.

Theorem accepted_response_has_complementary_live_counters :
  replay_identifier_consumed accepted_response_state = true /\
  server_peer_published accepted_response_state = true /\
  server_send_sequence accepted_response_state = 1%N /\
  server_receive_sequence accepted_response_state = 0%N /\
  beacon_send_sequence accepted_response_state = 0%N /\
  beacon_receive_sequence accepted_response_state = 1%N /\
  beacon_state accepted_response_state = BeaconEstablished.
Proof. repeat split. Qed.

Theorem rejected_response_terminally_aborts_beacon :
  forall prior,
    response_pending prior ->
    replay_identifier_consumed (rejected_response_state prior) =
      replay_identifier_consumed prior /\
    server_peer_published (rejected_response_state prior) =
      server_peer_published prior /\
    server_send_sequence (rejected_response_state prior) =
      server_send_sequence prior /\
    server_receive_sequence (rejected_response_state prior) =
      server_receive_sequence prior /\
    beacon_state (rejected_response_state prior) = BeaconAborted /\
    beacon_send_sequence (rejected_response_state prior) = 0%N /\
    beacon_receive_sequence (rejected_response_state prior) = 0%N.
Proof. move=> prior pending; repeat split. Qed.

(** The concrete SSProve seam below has two disjoint role slots. PUT and TAKE are internal procedures; the linked public package defined later exports only one RUN operation. *)
Definition chRoleChains : choice_type := chProd chBool chBool.
Definition chCkeyPayload : choice_type :=
  chProd chBool (chProd chBool (chProd chBool chRoleChains)).
Definition chCkeySlot : choice_type := chOption (chProd chBool chCkeyPayload).
Definition chRomSample : choice_type :=
  chProd chBool
    (chProd chBool
      (chProd chBool
        (chProd chBool
          (chProd chBool
            (chProd chBool (chProd chBool chBool)))))).
Definition chPublicResponseObservation : choice_type := chOption chBool.

(** A single private operation samples the complete eight-bit finite tape from exactly the same joint distribution used by the pure pushforward above. This avoids exposing individual coins and avoids introducing a nested-bind/product-distribution bridge. *)
Definition uniform_response_sample_op : Op :=
  existT _ chRomSample uniform_rom_sample.

Notation "'payload" := chCkeyPayload (in custom pack_type at level 2).
Notation "'payload" := chCkeyPayload (at level 2) : package_scope.
Notation "'sample" := chRomSample (in custom pack_type at level 2).
Notation "'sample" := chRomSample (at level 2) : package_scope.
Notation "'response" := chPublicResponseObservation
  (in custom pack_type at level 2).
Notation "'response" := chPublicResponseObservation
  (at level 2) : package_scope.

Definition put_server_id : nat := 80%N.
Definition take_server_id : nat := 81%N.
Definition put_beacon_id : nat := 82%N.
Definition take_beacon_id : nat := 83%N.
Definition setup_server_id : nat := 84%N.
Definition setup_beacon_id : nat := 85%N.
Definition seal_response_id : nat := 86%N.
Definition open_response_id : nat := 87%N.
Definition run_response_id : nat := 88%N.

Definition server_ckey_loc : Location := (chCkeySlot; 80%N).
Definition beacon_ckey_loc : Location := (chCkeySlot; 81%N).
Definition ckey_locs : {fset Location} :=
  fset [:: server_ckey_loc; beacon_ckey_loc].

Lemma role_ckey_locations_are_distinct :
  server_ckey_loc <> beacon_ckey_loc.
Proof.
  move=> locations_equal.
  have indices_equal : server_ckey_loc.π2 = beacon_ckey_loc.π2 :=
    f_equal (fun location : Location => location.π2) locations_equal.
  discriminate indices_equal.
Qed.

Definition ckey_put_interface : Interface :=
  [interface
    #val #[put_server_id] : 'payload → 'unit ;
    #val #[put_beacon_id] : 'payload → 'unit
  ].

Definition ckey_take_interface : Interface :=
  [interface
    #val #[take_server_id] : 'bool → 'payload ;
    #val #[take_beacon_id] : 'bool → 'payload
  ].

Definition ckey_interface : Interface :=
  [interface
    #val #[put_server_id] : 'payload → 'unit ;
    #val #[put_beacon_id] : 'payload → 'unit ;
    #val #[take_server_id] : 'bool → 'payload ;
    #val #[take_beacon_id] : 'bool → 'payload
  ].

Definition consuming_ckey : package ckey_locs [interface] ckey_interface :=
  [package
    #def #[put_server_id] (payload : 'payload) : 'unit {
      slot ← get server_ckey_loc ;;
      #assert (slot == None) ;;
      #assert (payload_role payload == server_role) ;;
      #put server_ckey_loc := Some (false, payload) ;;
      @ret 'unit Datatypes.tt
    } ;
    #def #[put_beacon_id] (payload : 'payload) : 'unit {
      slot ← get beacon_ckey_loc ;;
      #assert (slot == None) ;;
      #assert (payload_role payload == beacon_role) ;;
      #put beacon_ckey_loc := Some (false, payload) ;;
      @ret 'unit Datatypes.tt
    } ;
    #def #[take_server_id] (session : 'bool) : 'payload {
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
      slot ← get beacon_ckey_loc ;;
      #assert (isSome slot) as slot_some ;;
      let marked_payload := getSome slot slot_some in
      #assert (marked_payload.1 == false) ;;
      let payload := marked_payload.2 in
      #assert (payload_role payload == beacon_role) ;;
      #assert (payload_session payload == session) ;;
      #put beacon_ckey_loc := Some (true, zero_payload) ;;
      @ret 'payload payload
    }
  ].

Definition keying_interface : Interface :=
  [interface
    #val #[setup_server_id] : 'sample → 'unit ;
    #val #[setup_beacon_id] : 'sample → 'unit
  ].

Definition keyed_interface : Interface :=
  [interface
    #val #[seal_response_id] : 'sample → 'bool ;
    #val #[open_response_id] : 'sample × 'bool → 'bool
  ].

Definition composition_core_interface : Interface :=
  [interface
    #val #[setup_server_id] : 'sample → 'unit ;
    #val #[setup_beacon_id] : 'sample → 'unit ;
    #val #[seal_response_id] : 'sample → 'bool ;
    #val #[open_response_id] : 'sample × 'bool → 'bool
  ].

Definition response_interface : Interface :=
  [interface
    #val #[run_response_id] : 'unit → 'response
  ].

(** CK derives complementary role-local states, but it can only install them into CKEY. The server install is called before sealing; the beacon install remains available for the later delivered-response path. *)
Definition keying_package
  (session : bounded_session_handle) (authenticated : bool)
  (input : pqxdh_root_input) :
  package fset0 ckey_put_interface keying_interface :=
  [package
    #def #[setup_server_id] (sample : 'sample) : 'unit {
      #import {sig #[put_server_id] : 'payload → 'unit } as PUT_SERVER ;;
      let tape := sample_to_tape sample in
      let payloads := production_role_payloads session authenticated tape input in
      PUT_SERVER payloads.1 ;;
      @ret 'unit Datatypes.tt
    } ;
    #def #[setup_beacon_id] (sample : 'sample) : 'unit {
      #import {sig #[put_beacon_id] : 'payload → 'unit } as PUT_BEACON ;;
      let tape := sample_to_tape sample in
      let payloads := production_role_payloads session authenticated tape input in
      PUT_BEACON payloads.2 ;;
      @ret 'unit Datatypes.tt
    }
  ].

(** CD can consume each role-local payload once. It receives provenance with the chains, but has no procedure that calls back into CK or republishes protocol state. *)
Definition keyed_package
  (session : bounded_session_handle) (challenge : bool) :
  package fset0 ckey_take_interface keyed_interface :=
  [package
    #def #[seal_response_id] (sample : 'sample) : 'bool {
      #import {sig #[take_server_id] : 'bool → 'payload } as TAKE_SERVER ;;
      server ← TAKE_SERVER session ;;
      #assert (payload_authenticated server == true) ;;
      let tape := sample_to_tape sample in
      let output := ratchet_step_expansion tape (payload_send_chain server) in
      @ret 'bool (xorb challenge output.1.1)
    } ;
    #def #[open_response_id] ('(sample, ciphertext) : 'sample × 'bool) : 'bool {
      #import {sig #[take_beacon_id] : 'bool → 'payload } as TAKE_BEACON ;;
      beacon ← TAKE_BEACON session ;;
      #assert (payload_authenticated beacon == true) ;;
      let tape := sample_to_tape sample in
      let output := ratchet_step_expansion tape (payload_receive_chain beacon) in
      @ret 'bool (xorb ciphertext output.1.1)
    }
  ].

Lemma component_locations_are_state_separated :
  server_ckey_loc <> beacon_ckey_loc /\
  fdisjoint (fset0 : {fset Location}) ckey_locs /\
  fdisjoint (fset0 : {fset Location}) ckey_locs /\
  fdisjoint (fset0 : {fset Location}) (fset0 : {fset Location}).
Proof.
  split; first exact role_ckey_locations_are_distinct.
  repeat split; apply fdisjoint0s.
Qed.

(** The consumer packages are siblings and the CKEY provider is linked on the right. The resulting core imports nothing and exports only the four sequencing operations. *)
#[tactic=notac] Equations? composition_core
  (session : bounded_session_handle) (authenticated challenge : bool)
  (input : pqxdh_root_input) :
  package ckey_locs [interface] composition_core_interface :=
  composition_core session authenticated challenge input :=
  {package
    (par (keying_package session authenticated input)
         (keyed_package session challenge)) ∘ consuming_ckey
  }.
Proof.
  ssprove_valid.
  - instantiate (1 := (fset0 : {fset Location})).
    rewrite fsetU0.
    apply fsubsetxx.
  - unfold ckey_put_interface, ckey_take_interface, ckey_interface.
    rewrite -!fset_cat; simpl; fsubset_auto.
  - unfold composition_core_interface, keying_interface, keyed_interface.
    rewrite -!fset_cat; simpl; fsubset_auto.
  - apply fsub0set.
  - apply fsubsetxx.
Qed.

(** The successful driver samples the complete finite tape internally, then enforces the production success order: server install, sequence-one seal, beacon install after delivery, and beacon open. The opened plaintext is discarded before returning the optional public ciphertext. *)
Definition successful_composition_driver :
  package fset0 composition_core_interface response_interface :=
  [package
    #def #[run_response_id] (_ : 'unit) : 'response {
      #import {sig #[setup_server_id] : 'sample → 'unit } as SETUP_SERVER ;;
      #import {sig #[setup_beacon_id] : 'sample → 'unit } as SETUP_BEACON ;;
      #import {sig #[seal_response_id] : 'sample → 'bool } as SEAL ;;
      #import {sig #[open_response_id] : 'sample × 'bool → 'bool } as OPEN ;;
      sample <$ uniform_response_sample_op ;;
      SETUP_SERVER sample ;;
      ciphertext ← SEAL sample ;;
      SETUP_BEACON sample ;;
      opened_plaintext ← OPEN (sample, ciphertext) ;;
      @ret 'response (Some ciphertext)
    }
  ].

(** Rejected provenance is represented by an explicit public [None] rather than by assertion mass loss. The cryptographic core is not invoked on this branch. *)
Definition rejected_composition_driver :
  package fset0 composition_core_interface response_interface :=
  [package
    #def #[run_response_id] (_ : 'unit) : 'response {
      @ret 'response None
    }
  ].

Definition composition_driver (authenticated : bool) :
  package fset0 composition_core_interface response_interface :=
  if authenticated
  then successful_composition_driver
  else rejected_composition_driver.

(** This is the checked state-separated public package. Its type exposes only [run_response_id]; CKEY, raw role payloads, setup, seal, and open are all internal after linking. *)
#[tactic=notac] Equations? state_separated_response_package
  (session : bounded_session_handle) (authenticated challenge : bool)
  (input : pqxdh_root_input) :
  package ckey_locs [interface] response_interface :=
  state_separated_response_package session authenticated challenge input :=
  {package
    composition_driver authenticated ∘
      composition_core session authenticated challenge input
  }.
Proof.
  ssprove_valid.
  - apply fsub0set.
  - apply fsubsetxx.
Qed.

(** This stateless package only exposes the monolithic single-call body for future interpreter work. It is not contextually equivalent to the one-shot state-separated package: an unrestricted context can distinguish them by calling [RUN] twice. *)
Definition monolithic_response_package
  (challenge : bool) (input : pqxdh_root_input) :
  package fset0 [interface] response_interface :=
  [package
    #def #[run_response_id] (_ : 'unit) : 'response {
      sample <$ uniform_response_sample_op ;;
      @ret 'response
        (monolithic_public_response_observation challenge sample input)
    }
  ].

Definition state_separated_response_games
  (session : bounded_session_handle) (authenticated : bool)
  (input : pqxdh_root_input) :
  loc_GamePair response_interface :=
  fun challenge =>
    {locpackage
      state_separated_response_package
        session authenticated challenge input}.

Theorem pure_single_run_body_matches_monolithic :
  forall session authenticated challenge sample input,
    authenticated = true ->
    separated_first_response session authenticated challenge
      (sample_to_tape sample) input =
    monolithic_first_response challenge (sample_to_tape sample) input.
Proof.
  move=> session authenticated challenge sample input authenticated_true.
  apply separated_first_response_matches_monolithic.
  exact authenticated_true.
Qed.

Print Assumptions complementary_role_orientation.
Print Assumptions separated_ckey_transfer_is_one_way_and_role_oriented.
Print Assumptions separated_first_response_matches_monolithic.
Print Assumptions separated_unauthenticated_response_rejects.
Print Assumptions public_response_rejects_unauthenticated_provenance.
Print Assumptions unauthenticated_public_responses_are_challenge_independent.
Print Assumptions pure_public_response_observation_matches_monolithic.
Print Assumptions separated_first_response_opens_sequence_one.
Print Assumptions state_separated_composition_uses_production_kdf_domains.
Print Assumptions failed_response_construction_consumes_only_replay_state.
Print Assumptions dropped_response_has_asymmetric_publication.
Print Assumptions accepted_response_has_complementary_live_counters.
Print Assumptions rejected_response_terminally_aborts_beacon.
Print Assumptions component_locations_are_state_separated.
Print Assumptions pure_single_run_body_matches_monolithic.
