-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer
import BeaconcryptCore.Computational.RegistrationNativeKemBuildUniform

/-! Actual Server response publication retains complete optional replies, chronological receipts and reached record/publication state under free ML count normalization. Closed source record and capability pieces use separately checked accounting-input laws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountRules (Correct)
open RegistrationNativeMldsaCountMap (transform)
variable {n : Nat} {ι KemSK Reader Response Auxiliary Encoded Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)

def signingProject (before : RegistrationWorldSigning.State n) : RegistrationWorldSigning.State n :=
  (RegistrationNativeMldsaWorldView.project before.1, before.2)

def localProject (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with recordRequests := [], world := (RegistrationNativeMldsaWorldView.project before.world.1, before.world.2) }

def serverProject (before : RegistrationServerFrontendCompiler.State n) : RegistrationServerFrontendCompiler.State n :=
  { before with world := localProject before.world }

private theorem signing_idempotent (before : RegistrationWorldSigning.State n) : signingProject (signingProject before) = signingProject before := by
  simp only [signingProject, RegistrationNativeMldsaWorldView.idempotent]
private theorem local_idempotent (before : RegistrationWorldAgreement.State n Auxiliary) : localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeMldsaWorldView.idempotent]
private theorem server_idempotent (before : RegistrationServerFrontendCompiler.State n) : serverProject (serverProject before) = serverProject before := by
  simp only [serverProject, local_idempotent]

private def worldLens (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) Value) :
    StateT (RegistrationWorldSigning.State n) (OracleComp (Spec source)) Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

private theorem worldLens_correct (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) Value)
    (good : Correct RegistrationNativeMldsaWorldView.project work) : Correct signingProject (worldLens source work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, (result.2, before.2))) <$> computation) (good.1 before.1)
    simp only [worldLens, StateT.run, Functor.map_map, Prod.map, id_eq, signingProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, (result.2, before.2))) <$> computation) (good.2 before.1)
    simp only [worldLens, StateT.run, transform, simulateQ_map, Functor.map_map, Prod.map, id_eq, signingProject] at same ⊢
    exact same

private def append (receipt : RegistrationSigningShared.Receipt) :
    StateT (RegistrationWorldSigning.State n) (OracleComp (Spec source)) Unit :=
  modify fun before => (before.1, before.2 ++ [receipt])

private theorem append_correct (receipt : RegistrationSigningShared.Receipt) :
    Correct signingProject (append (n := n) source receipt) := by
  constructor <;> intro before <;>
    simp only [append, StateT.run_modify, transform, simulateQ_pure, map_pure, Prod.map, id_eq,
      signingProject, RegistrationNativeMldsaWorldView.idempotent]

private theorem outgoing_sign (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload)
    (digest : CtxRomAuth.CtxDigest) :
    RegistrationNativeMldsaServer.outgoing (n := n) source credential (.sign request payload digest) = (do
      let reply ← worldLens source (RegistrationNativeMldsaProgram.call .native (.sign credential request))
      append source ⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes reply⟩, digest⟩
      pure reply) := by
  funext before
  simp only [RegistrationNativeMldsaServer.outgoing, worldLens, append, StateT.run,
    StateT.monad_bind_def, StateT.bind, bind_map_left]
  rfl

private theorem hash_stable (request : registration.HashRequest) :
    RegistrationNativeKemCounterIndependence.Stable signingProject
      (RegistrationWorldSigning.outgoing (RegistrationNativeMldsa.owned source credential) (.hash request) :
        StateT (RegistrationWorldSigning.State n) ProbComp _) := by
  intro before
  have same := congrArg (fun computation => (fun result => (result.1, (result.2, before.2))) <$> computation)
    (RegistrationNativeMldsaWorldView.effects (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) before.1)
  simp only [RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map, id_eq, signingProject] at same ⊢
  exact same

/-- Every actual Server signing callback has both free continuation laws with exact optional replies and chronological receipts. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) :
    Correct signingProject (RegistrationNativeMldsaServer.outgoing (n := n) source credential query) := by
  cases query with
  | hash request => exact RegistrationNativeMldsaCountRules.closed _ _ (hash_stable source credential request)
  | sign request payload digest =>
      rw [outgoing_sign]
      exact RegistrationNativeMldsaCountRules.bind signingProject _ _
        (worldLens_correct source _ (RegistrationNativeMldsaCountRules.call .native (.sign credential request)))
        (fun reply => RegistrationNativeMldsaCountRules.bind signingProject _ _ (append_correct source _)
          (fun _ => RegistrationNativeMldsaCountRules.pure signingProject signing_idempotent reply))

private theorem signing (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    Correct (localProject (Auxiliary := Auxiliary)) (RegistrationNativeMldsaServer.signing (n := n) source credential encode pending) := by
  have work := RegistrationNativeMldsaCountRules.simulate (signingProject (n := n)) signing_idempotent _
    (outgoing (n := n) source credential) (RegistrationWorldServerPublication.program encode pending)
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { localProject before with world := result.2 })) <$> computation)
      (work.1 before.world)
    simp only [RegistrationNativeMldsaServer.signing, StateT.run, Functor.map_map, Prod.map, id_eq, localProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { localProject before with world := result.2 })) <$> computation)
      (work.2 before.world)
    simp only [RegistrationNativeMldsaServer.signing, StateT.run, transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, localProject] at same ⊢
    exact same

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commuting : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : RegistrationNativeKemCounterIndependence.Stable first work)
    (right : RegistrationNativeKemCounterIndependence.Stable second work) :
    RegistrationNativeKemCounterIndependence.Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commuting] at following
  exact initial.trans following

private theorem record_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    RegistrationNativeKemCounterIndependence.Stable (localProject (n := n) (Auxiliary := Auxiliary))
      (simulateQ (RegistrationWorldRecords.handler setup codec) work) := by
  exact compose_stable RegistrationServerRecordWorldSource.project RegistrationNativeKemWorldAgreement.mask (fun _ => rfl) _
    (RegistrationNativeLocalView.record_program setup codec work)
    (RegistrationNativeKemCompletionPrimitives.record_program_input setup codec work)

private theorem capability_stable (query : PqxdhRecordLiftInterface.Capability n) :
    RegistrationNativeKemCounterIndependence.Stable (localProject (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.capability query) := by
  intro before
  have same := congrArg (fun computation => (fun result => (result.1,
    { localProject before with world := (result.2, before.world.2) })) <$> computation)
    (RegistrationNativeMldsaWorldView.effects (.inr query) before.world.1)
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map,
    Prod.map, id_eq, localProject] at same ⊢
  exact same

/-- Both executions perform the actual AD hash; the established count projection erases analysis counters. -/
theorem adHash_stable (pending : registration.ServerAdHash) :
    RegistrationNativeKemCounterIndependence.Stable (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.adHash pending) := by
  unfold RegistrationWorldServerCompletion.adHash
  cases pending.request with
  | fail error | div => exact RegistrationNativeKemCounterIndependence.pure_stable _ local_idempotent _
  | ok request =>
      exact RegistrationNativeKemCounterIndependence.bind_stable _ _ _ (capability_stable _)
        (fun _ => RegistrationNativeKemCounterIndependence.pure_stable _ local_idempotent _)

private theorem install_stable (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    RegistrationNativeKemCounterIndependence.Stable (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationWorldServerCompletion.install control published) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div =>
      simp only [RegistrationWorldServerCompletion.install, prepared]
      exact RegistrationNativeKemCounterIndependence.pure_stable _ local_idempotent _
  | ok result => cases result with
    | Err previous =>
        simp only [RegistrationWorldServerCompletion.install, prepared]
        exact RegistrationNativeKemCounterIndependence.pure_stable _ local_idempotent _
    | Ok pending =>
        rw [RegistrationWorldServerCompletion.install_native control published pending prepared]
        exact RegistrationNativeKemCounterIndependence.bind_stable _ _ _ (capability_stable _)
          (fun _ => RegistrationNativeKemCounterIndependence.pure_stable _ local_idempotent _)

/-- The actual native capacity callback supplies both free continuation laws for SDK occupancy and installation. -/
theorem capability (query : PqxdhRecordLiftInterface.Capability n) :
    Correct (localProject (Auxiliary := Auxiliary))
      (RegistrationNativeMldsaProgram.liftState (source := source) (RegistrationWorldServerCompletion.capability query)) :=
  RegistrationNativeMldsaCountRules.closed _ _ (capability_stable query)

private theorem publish (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    Correct (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativeMldsaServer.publish source credential encode control pending) := by
  unfold RegistrationNativeMldsaServer.publish
  apply RegistrationNativeMldsaCountRules.bind localProject _ _ (signing source credential encode pending)
  intro published
  cases published with
  | fail error | div => exact RegistrationNativeMldsaCountRules.pure localProject local_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaCountRules.pure localProject local_idempotent _
    | Ok published => exact RegistrationNativeMldsaCountRules.closed _ _ (install_stable control published)

/-- Complete actual first-record, signed-response publication and populated peer installation retain their source behavior under count normalization. -/
theorem completionFromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Correct (localProject (n := n) (Auxiliary := Auxiliary))
      (RegistrationNativeMldsaServer.completionFromInitial source credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.completionFromInitial
  apply RegistrationNativeMldsaCountRules.bind localProject _ _
    (RegistrationNativeMldsaCountRules.closed _ _ (record_stable setup codec _))
  intro record
  cases record with
  | fail error | div => exact RegistrationNativeMldsaCountRules.pure localProject local_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaCountRules.pure localProject local_idempotent _
    | Ok pending => exact publish source credential encode control pending

end BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.capability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.completionFromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.completionFromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.adHash_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer.adHash_stable
