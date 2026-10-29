-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual response completion is independent of the omitted private uniform-count input. The proof follows the real first-record, ML signing, dynamic writer and populated-AD insertion sequence and retains every reached failure state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemCounterIndependence (Stable pure_stable bind_stable)
open RegistrationNativeKemWorldAgreement (mask)
open RegistrationWorldAgreement (State)
variable {ι KemSK Reader Response Auxiliary Encoded Value Input Output S : Type} {base : OracleSpec ι} {n : Nat}

private theorem continue_stable (projection : S → S)
    (idempotent : ∀ before, projection (projection before) = projection before)
    (action : RustM Input) (next : Input → StateT S ProbComp (RustM Output))
    (following : ∀ value, Stable projection (next value)) :
    Stable projection (match action with
      | .ok value => next value
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  cases action with
  | fail error | div => exact pure_stable projection idempotent _
  | ok value => exact following value

private theorem continueResult_stable (projection : S → S)
    (idempotent : ∀ before, projection (projection before) = projection before)
    (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT S ProbComp (RustM (core.result.Result Output pqxdh.ServerState)))
    (following : ∀ value, Stable projection (next value)) :
    Stable projection (match action with
      | .ok (.Ok value) => next value
      | .ok (.Err previous) => pure (.ok (.Err previous))
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  cases action with
  | fail error | div => exact pure_stable projection idempotent _
  | ok result => cases result with
    | Ok value => exact following value
    | Err previous => exact pure_stable projection idempotent _

private theorem capability_stable (query : PqxdhRecordLiftInterface.Capability n) :
    Stable (mask (Auxiliary := Auxiliary)) (RegistrationWorldServerCompletion.capability query) := by
  intro before
  have law := congrArg (fun work => (fun result =>
      (result.1, { before with world := (result.2, before.world.2) })) <$> work)
    (RegistrationNativeKemWorldEffects.effects_input (.inr query) before.world.1)
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map, Prod.map, id_eq,
    mask, RegistrationNativeKemWorldUniform.mask] at law ⊢
  convert law using 1

private theorem signing_stable
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    Stable (mask (n := n) (Auxiliary := Auxiliary)) (RegistrationWorldServerCompletion.signing sign encode pending) := by
  intro before
  have law := congrArg (fun work => (fun result => (result.1, { before with world := result.2 })) <$> work)
    (RegistrationNativeKemCompletionPrimitives.signing_program_input sign
      (RegistrationWorldServerPublication.program encode pending) before.world)
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, Functor.map_map, Prod.map, id_eq,
    mask, RegistrationNativeKemCompletionPrimitives.signingMask] at law ⊢
  convert law using 1

private theorem install_stable (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    Stable (mask (n := n) (Auxiliary := Auxiliary)) (RegistrationWorldServerCompletion.install control published) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div =>
      simp only [RegistrationWorldServerCompletion.install, prepared]
      exact pure_stable mask (fun _ => rfl) _
  | ok result =>
      cases result with
      | Err previous =>
          simp only [RegistrationWorldServerCompletion.install, prepared]
          exact pure_stable mask (fun _ => rfl) _
      | Ok pending =>
          rw [RegistrationWorldServerCompletion.install_native control published pending prepared]
          exact bind_stable mask _ _ (capability_stable _) (fun _ => pure_stable mask (fun _ => rfl) _)

private theorem publish_stable
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) :
    Stable (mask (n := n) (Auxiliary := Auxiliary)) (RegistrationWorldServerCompletion.publish sign encode control pending) := by
  unfold RegistrationWorldServerCompletion.publish
  apply bind_stable mask _ _ (signing_stable sign encode pending)
  intro published
  exact continueResult_stable mask (fun _ => rfl) published _ (install_stable control)

/-- The actual first-record and signed-response completion keeps its complete populated binding, source kernel, writer outcome and all failed-operation logs. -/
theorem completion_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) (before : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before =
      Prod.map id mask <$> (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run (mask before) := by
  apply bind_stable mask _ _ (RegistrationNativeKemCompletionPrimitives.record_program_input setup codec _)
  intro record
  exact continueResult_stable mask (fun _ => rfl) record _ (publish_stable sign encode control)

private theorem world_stable (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (stable : Stable mask work) :
    Stable RegistrationNativeKemServerState.maskServer (RegistrationServerSdkSource.world work) := by
  intro before
  have law := congrArg (fun run => (fun result => (result.1, { before with world := result.2 })) <$> run)
    (stable before.world)
  simp only [RegistrationServerSdkSource.world, StateT.run, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeKemServerState.maskServer, mask] at law ⊢
  convert law using 1

private theorem commit_stable (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    Stable (RegistrationNativeKemServerState.maskServer (n := n)) (RegistrationServerSdkSource.commit result) := by
  cases result with
  | fail error | div => intro before; simp only [RegistrationServerSdkSource.commit, StateT.run, map_pure,
      Prod.map, id_eq, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]
  | ok result =>
      cases result <;> intro before <;>
        simp only [RegistrationServerSdkSource.commit, StateT.run, map_pure, Prod.map, id_eq,
          RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]

private theorem initial_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable (RegistrationNativeKemServerState.maskServer (n := n))
      (RegistrationServerSdkSource.fromInitial setup codec sign encode control pending) := by
  unfold RegistrationServerSdkSource.fromInitial
  exact bind_stable _ _ _ (world_stable _ (completion_input setup codec sign encode control pending)) commit_stable

private theorem occupancy_stable (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Stable (RegistrationNativeKemServerState.maskServer (n := n))
      (RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied) := by
  cases action : lookup.resume occupied with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.afterOccupancy, action]
      exact pure_stable RegistrationNativeKemServerState.maskServer (fun _ => rfl) _
  | ok result =>
      cases result with
      | Err previous =>
          simp only [RegistrationServerSdkSource.afterOccupancy, action]
          exact pure_stable RegistrationNativeKemServerState.maskServer (fun _ => rfl) _
      | Ok pending =>
          simp only [RegistrationServerSdkSource.afterOccupancy, action]
          split
          · exact initial_stable setup codec sign encode control pending
          · exact pure_stable RegistrationNativeKemServerState.maskServer (fun _ => rfl) _

private theorem complete_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before =
      Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerSdkSource.complete setup codec checks sign encode token application).run
          (RegistrationNativeKemServerState.maskServer before) := by
  simp only [RegistrationServerSdkSource.complete, StateT.run, RegistrationNativeKemServerState.maskServer]
  cases lookupRun : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => simp only [map_pure, Prod.map, id_eq, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]
  | ok result =>
      cases result with
      | Err previous => simp only [map_pure, Prod.map, id_eq, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]
      | Ok lookup =>
          dsimp only
          cases requested : lookup.request with
          | fail error | div => simp only [map_pure, Prod.map, id_eq, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]
          | ok keyId =>
              dsimp only
              split
              · have law := bind_stable RegistrationNativeKemServerState.maskServer
                  (RegistrationServerSdkSource.world (RegistrationWorldServerCompletion.capability (.peerPresent keyId)))
                  (fun occupied => RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode before.control lookup occupied)
                  (world_stable _ (capability_stable (.peerPresent keyId)))
                  (occupancy_stable setup codec checks sign encode before.control lookup) before
                simpa only [StateT.run, StateT.monad_bind_def, StateT.bind, RegistrationNativeKemServerState.maskServer] using law
              · simp only [map_pure, Prod.map, id_eq, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent]

/-- Actual handle consumption, native lookup, complete-message sizing, occupancy, reservation, first record, ML signing and fallible publication preserve the same complete operational output under the uniform-only projection. -/
theorem build_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before =
      Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerSdkSource.build setup codec checks sign encode handle application).run
          (RegistrationNativeKemServerState.maskServer before) := by
  cases found : before.sessions[handle]? with
  | none => simp only [RegistrationServerSdkSource.build, RegistrationServerSdkSource.take, StateT.run,
      RegistrationNativeKemServerState.maskServer, found, map_pure, Prod.map, id_eq,
      RegistrationNativeKemWorldUniform.mask_idempotent]
  | some stored =>
      cases stored with
      | none => simp only [RegistrationServerSdkSource.build, RegistrationServerSdkSource.take, StateT.run,
          RegistrationNativeKemServerState.maskServer, found, map_pure, Prod.map, id_eq,
          RegistrationNativeKemWorldUniform.mask_idempotent]
      | some token =>
          cases application with
          | none => simp only [RegistrationServerSdkSource.build, RegistrationServerSdkSource.take, StateT.run,
              RegistrationNativeKemServerState.maskServer, found, map_pure, Prod.map, id_eq,
              RegistrationNativeKemWorldUniform.mask_idempotent]
          | some application =>
              simpa only [RegistrationServerSdkSource.build, RegistrationServerSdkSource.take, StateT.run,
                RegistrationNativeKemServerState.maskServer, found] using
                complete_input setup codec checks sign encode token application
                  { before with sessions := before.sessions.set handle none }

end BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform.completion_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform.completion_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform.build_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform.build_input
