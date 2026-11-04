-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotFinishSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
/-! The literal corrected public frontend, adaptive program and canonical raw compiler preserve the minimal constructor-kind monitor. Both known and hidden installs match the optional slot origin of the raw material reply most recently demanded by that actual source callback. This structural property makes no alias-exclusion or cryptographic security claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



/-- Every actual corrected callback retains a clean paired monitor, including failed source allocations and insertions. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    RegistrationNativePlatformPublicSlotKind.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)) := by
  have quiet (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial request) :=
    RegistrationNativePlatformPublicSlotKind.free_safe
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation request).run before))
      (fun role => RegistrationNativePlatformPublicOrdinaryInstall.handler_free (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation role request ordinary before)
  cases query with
  | inl coin => exact quiet (.inl coin) (by simp [RegistrationNativePublicCaps.IsMaterial])
  | inr query => cases query with
    | create edPin mlPin keyId => exact quiet (.inr (.create edPin mlPin keyId)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | bundle index => exact quiet (.inr (.bundle index)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | accept packet => exact quiet (.inr (.accept packet)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | build handle application => exact RegistrationNativePlatformPublicSlotBuildSafe.build setup source sign view failure allocation reservePeer erased helper implementation handle application before
    | finish index packet => exact RegistrationNativePlatformPublicSlotFinishSafe.finish setup wire index packet before
    | hmac key bytes => exact quiet (.inr (.hmac key bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | hash bytes => exact quiet (.inr (.hash bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | serverSend keyId plaintext => exact quiet (.inr (.serverSend keyId plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | serverRaw raw => exact quiet (.inr (.serverRaw raw)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | beaconSend index plaintext => exact quiet (.inr (.beaconSend index plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | beaconRaw index raw => exact quiet (.inr (.beaconRaw index raw)) (by simp [RegistrationNativePublicCaps.IsMaterial])

/-- Arbitrary adaptive typed execution retains all actual callback replies and persistent state through the paired certificate. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : State source Platform) :
    RegistrationNativePlatformPublicSlotKind.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((simulateQ (RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation) work).run before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact RegistrationNativePlatformPublicSlotKind.pure_safe _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact RegistrationNativePlatformPublicSlotKind.bind_safe _ _
      (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query before)
      (fun reached => ih reached.1 reached.2)

/-- The original canonical-wire raw experiment in every mode inherits same-demand safety without an admission or success premise. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform) :
    RegistrationNativePlatformPublicSlotKind.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation serverKeyId bounds mode work before)) := by
  exact program setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation _ before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety.run
