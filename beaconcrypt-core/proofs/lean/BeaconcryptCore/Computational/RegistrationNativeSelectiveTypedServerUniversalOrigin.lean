-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialTypedSource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin

/-! The actual original typed Server build returns a hidden handle when its same stored Ready is selected. The source equation is instantiated by the original frontend callback, rather than supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedServerUniversalOrigin
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- A successful original typed build installs the hidden origin at its literal returned public key id. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativePublicFrontend.State source)
    (ready : RegistrationServerReferenceRoot.Ready) (stored : frontend.server.sessions[handle]? = some (some ready))
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : ((((RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.build handle application)) ×
      RegistrationNativePublicFrontend.State source) × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) ×
        CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.build handle application))).run frontend)).run before) shell world secret))
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (successful : result.1.1.1.1.1 = .ok (some (keyId, bytes)))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer keyId) = some slot := by
  rw [RegistrationNativeSelectiveMaterialTypedSource.build,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  cases returned
  exact RegistrationNativeSelectiveServerUniversalOrigin.build setup wire route sign seed scalar candidate provider service codec
    checks.reservePeer handle application frontend.server ready stored (frontend.environment, before) shell world secret native called
      keyId bytes successful selected

end BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedServerUniversalOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedServerUniversalOrigin.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedServerUniversalOrigin.build
