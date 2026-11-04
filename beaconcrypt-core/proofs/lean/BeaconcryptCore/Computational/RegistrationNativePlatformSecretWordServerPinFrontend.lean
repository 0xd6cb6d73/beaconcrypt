import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinOpen
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinControl
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem accept (setup : Setup base KemSK) (checks : Checks) (selectedAccept : Nat)
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State source Platform) (result : RustM (Option Nat) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.accept (n := n) setup checks source selectedAccept reserve packet).run before)) :
    result.2.1.server.pin=before.1.server.pin := by
  simp only [RegistrationNativePlatformSecretWordFrontend.accept,StateT.run_bind,StateT.run_get,
    StateT.run_modify,pure_bind] at supported
  simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact RegistrationNativePlatformSecretWordServerPinOpen.accept _ _ setup checks source.verify packet
    before.1.server before.1.environment before.2 reached called

private theorem build [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State source Platform) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation erased helper writer reserve handle application source).run before)) :
    result.2.1.server.pin=before.1.server.pin := by
  simp only [RegistrationNativePlatformSecretWordFrontend.build,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  exact (RegistrationNativePlatformSecretWordServerPinControl.build_pin _ _ _ _ handle application
    before.1.server (before.1.environment.receipts,before.2) reached original).trans
    (RegistrationNativeSecretWordMaterialPin.take_pin handle before.1.server)

/-- Every literal corrected Word callback retains the stored Server pin; current repeated hash results do not overwrite its configured binding. -/
theorem query [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    result.2.1.server.pin=before.1.server.pin := by
  cases query with
  | inl coin =>
      exact congrArg (fun server => server.pin)
        (RegistrationNativePlatformSecretWordLiveState.ordinary_server setup source selectedOwner publicPrekey reserveFrame writer _ before result supported)
  | inr query => cases query with
    | accept packet => exact accept setup checks selectedAccept reserveRegistration packet before result supported
    | build handle application => exact build setup sign view failure allocation erased helper writer reservePeer handle application before result supported
    | finish owner packet =>
        exact congrArg (fun server => server.pin)
          (RegistrationNativePlatformSecretWordLiveState.finish_server setup wire source owner packet before result supported)
    | _ =>
        exact congrArg (fun server => server.pin)
          (RegistrationNativePlatformSecretWordLiveState.ordinary_server setup source selectedOwner publicPrekey reserveFrame writer _ before result supported)
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend.query
