-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServerPrimitives
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer

/-! The complete original free Server response build has an all-raw-replies ordinary-randomness cap. The source record and response controllers retain every failed prefix; known-kernel installation, occupancy and moved-token bookkeeping add no random draw. The only ML signing request stays an explicit free capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaProgram (Spec liftState)
open RegistrationNativeMldsaCoinPrimitives (IsCoin ordinary)
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response State Value Next : Type} {base : OracleSpec ι}
variable (source : Source) (credential : Credential source)

private def Bound (work : StateT State (OracleComp (Spec source)) Value) (count : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsCoin count

private theorem bind_bound (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next) (firstCount restCount : Nat)
    (first : Bound source work firstCount) (rest : ∀ value, Bound source (next value) restCount) :
    Bound source (work >>= next) (firstCount + restCount) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (first before) (fun result _ => rest result.1 result.2)

private theorem pure_bound (value : Value) (count : Nat) :
    Bound source (pure value : StateT State (OracleComp (Spec source)) Value) count := fun _ => by trivial

private theorem install_query (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationWorldServerCompletion.capability (.installServer keyId binding (.known kernel))).run before).IsTotalQueryBound 0 := by
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, IsTotalQueryBound, isQueryBound_map_iff,
    PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability]
  simp only [PqxdhRecordLiftWorld.installServer, StateT.run, PqxdhRecordLiftWorld.chargeEffect]
  cases present : before.world.1.server with
  | none => trivial
  | some server =>
      simp only
      split <;> trivial

/-- The original source installs its already computed kernel without any hidden seed draw. -/
theorem install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationWorldServerCompletion.install control published).run before).IsTotalQueryBound 0 := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div =>
      unfold RegistrationWorldServerCompletion.install
      rw [prepared]
      trivial
  | ok result => cases result with
    | Err previous =>
        unfold RegistrationWorldServerCompletion.install
        rw [prepared]
        trivial
    | Ok pending =>
        rw [RegistrationWorldServerCompletion.install_native control published pending prepared, StateT.run_bind]
        exact isTotalQueryBound_bind (n₁ := 0) (n₂ := 0) (install_query _ _ _ before) (fun _ => by trivial)

/-- Every free outgoing source callback pays at most its64-byte shared-cache miss; arbitrary ML replies add no ordinary draw. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n) :
    ((RegistrationNativeMldsaServer.outgoing source credential query).run before).IsQueryBoundP IsCoin 64 := by
  cases query with
  | hash request =>
      apply ordinary _ 64
      simpa only [RegistrationWorldSigning.outgoing, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        RegistrationNativeMldsaCoinPrimitives.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.1
  | sign request payload digest =>
      simp only [RegistrationNativeMldsaServer.outgoing, StateT.run, isQueryBoundP_map_iff]
      exact (RegistrationNativeMldsaCoinPrimitives.call .native (.sign credential request) before.1).mono (Nat.zero_le 64)

private theorem signing_continue {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationWorldServerPublication.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem signing_result {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationWorldServerPublication.continueResult action next).IsTotalQueryBound count := by
  cases action with
  | ok result => cases result with
    | Ok value => exact bounded value
    | Err previous => trivial
  | fail error | div => trivial

private theorem ready_total (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) :
    (RegistrationWorldServerPublication.ready encode pending).IsTotalQueryBound 0 := by
  rw [RegistrationWorldServerPublication.ready_pure]
  trivial

private theorem signing_total (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    (RegistrationWorldServerPublication.signing encode payload digest pending).IsTotalQueryBound 1 := by
  apply signing_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => signing_result _ _ 0 (ready_total encode)⟩

private theorem program_total (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    (RegistrationWorldServerPublication.program encode pending).IsTotalQueryBound 2 := by
  apply signing_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => signing_result _ _ 1 (signing_total encode _ _)⟩

private theorem simulated {Query Result : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (step : ∀ query before, ((implementation query).run before).IsQueryBoundP IsCoin 64)
    (work : OracleComp queries Result) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : State) :
    ((simulateQ implementation work).run before).IsQueryBoundP IsCoin (cap * 64) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isQueryBoundP_bind (step query before) (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)).mono
      have positive : 0 < cap := bounded.1
      omega

/-- Full response hash/sign/publication pays two source slots of at most64 ordinary draws, for every raw ML reply. -/
theorem signing (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativeMldsaServer.signing source credential encode pending).run before).IsQueryBoundP IsCoin 128 := by
  simpa only [RegistrationNativeMldsaServer.signing, StateT.run, isQueryBoundP_map_iff] using
    simulated source (RegistrationNativeMldsaServer.outgoing source credential) (outgoing source credential)
      _ 2 (program_total encode pending) before.world

private theorem publish (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    Bound source (RegistrationNativeMldsaServer.publish (n := n) (Auxiliary := Auxiliary) source credential encode control pending) 128 := by
  unfold RegistrationNativeMldsaServer.publish
  apply bind_bound source _ _ 128 0 (signing source credential encode pending)
  intro result
  cases result with
  | fail error | div => exact pure_bound source _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound source _ _
    | Ok published => exact fun before => ordinary _ 0 (install control published before)

/-- The actual record-plus-response continuation retains a literal5+2 source-slot allowance, with all optional failures. -/
theorem completionFromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativeMldsaServer.completionFromInitial source credential setup codec encode control pending).run before).IsQueryBoundP IsCoin 448 := by
  simp only [RegistrationNativeMldsaServer.completionFromInitial, StateT.run_bind]
  apply isQueryBoundP_bind (n := 320) (m := 128)
  · exact ordinary _ 320 (RegistrationNativeMldsaCoinServerPrimitives.fromInitial setup codec pending before)
  · intro result _
    cases result.1 with
    | fail error | div => trivial
    | ok answer => cases answer with
      | Err previous => trivial
      | Ok pending => exact publish source credential encode control pending result.2

private theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp (Spec source)) Value)
    (count : Nat) (bounded : Bound source work count) :
    Bound source (RegistrationNativeMldsaServer.world source work) count := by
  intro before
  simpa only [RegistrationNativeMldsaServer.world, StateT.run, isQueryBoundP_map_iff] using bounded before.world

private theorem commit (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerSdkSource.commit result).run before).IsTotalQueryBound 0 := by
  cases result with
  | fail error | div => trivial
  | ok answer => cases answer <;> trivial

private theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Bound source (RegistrationNativeMldsaServer.fromInitial (n := n) source credential setup codec encode control pending) 448 := by
  unfold RegistrationNativeMldsaServer.fromInitial
  exact bind_bound source _ _ 448 0
    (world source _ _ (completionFromInitial source credential setup codec encode control pending))
    (fun result before => ordinary _ 0 (commit result before))

/-- The actual response-dependent AD hash has at most one64-byte ROM miss, before any peer reservation. -/
private theorem nativeAdHash (pending : registration.ServerAdHash) (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerSdkSource.adHash pending).run before).IsTotalQueryBound 64 := by
  unfold RegistrationServerSdkSource.adHash RegistrationServerSdkSource.world
  simp only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  unfold RegistrationWorldServerCompletion.adHash
  cases pending.request with
  | fail error | div => trivial
  | ok request =>
      apply isTotalQueryBound_bind (n₁ := 64) (n₂ := 0)
      · simpa only [RegistrationWorldServerCompletion.capability, StateT.run, IsTotalQueryBound,
          isQueryBound_map_iff] using RegistrationNativeMldsaCoinPrimitives.hash
            (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.world.world.1
      · intro hashed
        trivial

/-- Reifying the AD hash adds no ML request and preserves its actual ordinary draw bound. -/
theorem adHash (pending : registration.ServerAdHash) (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationNativeMldsaServer.adHash source pending).run before).IsQueryBoundP IsCoin 64 :=
  ordinary _ 64 (nativeAdHash pending before)

private theorem afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Bound source (RegistrationNativeMldsaServer.afterOccupancy (n := n) source credential setup codec checks encode control lookup occupied) 512 := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_bound source _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound source _ _
    | Ok pending =>
        apply bind_bound source _ _ 64 448 (adHash source pending)
        intro hashed
        cases hashed with
        | fail error | div => exact pure_bound source _ _
        | ok result => cases result with
          | Err previous => exact pure_bound source _ _
          | Ok initial =>
              simp only
              split
              · exact fromInitial source credential setup codec encode control initial
              · exact pure_bound source _ _

private theorem peerPresent (keyId : U64) (before : RegistrationServerRootCompiler.Local n) :
    ((RegistrationWorldServerCompletion.capability (.peerPresent keyId)).run before).IsTotalQueryBound 0 := by
  simp only [RegistrationWorldServerCompletion.capability, PqxdhRecordLiftWorld.effects,
    PqxdhRecordLiftWorld.capability, StateT.run, IsTotalQueryBound, isQueryBound_map_iff, isQueryBound_pure]

private theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Bound source (RegistrationNativeMldsaServer.complete (n := n) source credential setup codec checks encode token application) 512 := by
  intro before
  simp only [RegistrationNativeMldsaServer.complete, StateT.run]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => trivial
  | ok answer => cases answer with
    | Err previous => trivial
    | Ok lookup =>
        simp only
        cases lookup.request with
        | fail error | div => trivial
        | ok keyId =>
            simp only
            split
            · exact isQueryBoundP_bind (n := 0) (m := 512)
                (world source _ 0 (fun current => ordinary _ 0 (peerPresent keyId current)) before)
                (fun result _ => afterOccupancy source credential setup codec checks encode before.control lookup result.1 result.2)
            · trivial

/-- The complete original moved-handle SDK build pays at most eight literal64-draw slots including the AD hash, with no successful-signature or cost-frame premise. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationNativeMldsaServer.build source credential setup codec checks encode handle application).run before).IsQueryBoundP IsCoin 512 := by
  simp only [RegistrationNativeMldsaServer.build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk found current => cases found with
    | none => trivial
    | some token => cases application with
      | none => trivial
      | some application => exact complete source credential setup codec checks encode token application current
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.completionFromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.completionFromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer.adHash
