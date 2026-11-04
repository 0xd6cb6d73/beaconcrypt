-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseTypedOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProtectedCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback

/-! Actual corrected source accept/finish origin failures at protected generated ML keys select an earlier successful generation attempt and a valid fresh same-cut ordinary forgery, or retain the literal shared-cache collision. Reached stored-pin validity comes from actual initialized execution. Failed generations, all admitted public fields, dynamic writers and assigned-ID finish remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProtectedCoverage (BornKey born_key)
open RegistrationNativePlatformOrdinaryMldsaTableCallback (State callback observe)
open RegistrationNativePlatformMldsaTableStop (Safe Good)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)
variable [primitive : AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativePlatformOrdinaryExperiment.handler RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial

section Actual
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The actual protected Beacon-key Init failure chooses its earlier generated row and same-cut ordinary candidate, or the actual shared-cache collision. -/
theorem accept (fallback : Credential source) (packet : registration.InitPacket)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (handle : Nat)
    (safe : Safe source credential fallback before)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source)) (owned : owner ∈ before.1.1.beacons)
    (keyProtected : packet.mldsa_public_key = owner.mldsa.publicKey)
    (supported : (.ok (some handle), after) ∈ support
      ((callback source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet))).run before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true before.1.1.server.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
        (RegistrationNativeMldsaShared.nativeProject before.1.1)))) :
    CacheHasCollision after.1.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal, ordinal < before.2.attempts ∧ BornKey source before.2 ordinal owner.mldsa.publicKey ∧
        ∃ forgery, observe source owner.mldsa.publicKey (.inr (.accept packet)) before (.ok (some handle)) after = some forgery ∧
          Good source owner.mldsa.publicKey after forgery := by
  exact RegistrationNativePlatformMldsaProtectedCoverage.accept source setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer fallback packet before after handle safe owner owned keyProtected supported absent

/-- The actual corrected protected pending-Server response failure chooses its earlier generated Server row at the same callback cut. -/
theorem finish (fallback : Credential source) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (application : Pqxdh.Bytes)
    (safe : Safe source credential fallback before)
    (selectedOwner : before.1.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = credential.publicKey)
    (supported : (.ok (some application), after) ∈ support
      ((callback source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.finish index (some packet)))).run before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before.1.1)))) :
    CacheHasCollision after.1.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal, ordinal < before.2.attempts ∧ BornKey source before.2 ordinal credential.publicKey ∧
        ∃ forgery, observe source credential.publicKey (.inr (.finish index (some packet))) before (.ok (some application)) after = some forgery ∧
          Good source credential.publicKey after forgery := by
  exact RegistrationNativePlatformMldsaProtectedCoverage.finish source setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer fallback index owner pending oneTime packet before after application safe
    selectedOwner phase keyProtected supported absent

end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.finish
