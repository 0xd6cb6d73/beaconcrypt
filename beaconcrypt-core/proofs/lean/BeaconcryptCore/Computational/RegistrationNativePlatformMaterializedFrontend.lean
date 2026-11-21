-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedOrdinary
/-! Every literal corrected public callback and adaptive continuation has its known-material versus opaque-slot free source equation. All actual allocation and writer histories, assigned identifiers, local state and persistent P are retained; no earlier complete profile identity is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedLocal (translate)
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



/-- Each actual callback has identical public results and state after materialization of only the private installed seed. -/
theorem handler_source (seeds : Seeds n) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    simulateQ (translate true seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)) =
      simulateQ (translate false seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)) := by
  have quiet (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial request) :=
    (RegistrationNativePlatformMaterializedOrdinary.handler_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation true seeds request ordinary before).trans
      (RegistrationNativePlatformMaterializedOrdinary.handler_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation false seeds request ordinary before).symm
  cases query with
  | inl coin => exact quiet (.inl coin) (by simp [RegistrationNativePublicCaps.IsMaterial])
  | inr query => cases query with
    | create edPin mlPin keyId => exact quiet (.inr (.create edPin mlPin keyId)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | bundle index => exact quiet (.inr (.bundle index)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | accept packet => exact quiet (.inr (.accept packet)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | build handle application => exact RegistrationNativePlatformMaterializedBuild.build_source setup source sign view failure allocation erased helper implementation reservePeer seeds handle application before
    | finish index packet => exact RegistrationNativePlatformMaterializedFinish.finish_source setup wire index packet seeds before
    | hmac key bytes => exact quiet (.inr (.hmac key bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | hash bytes => exact quiet (.inr (.hash bytes)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | serverSend keyId plaintext => exact quiet (.inr (.serverSend keyId plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | serverRaw raw => exact quiet (.inr (.serverRaw raw)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | beaconSend index plaintext => exact quiet (.inr (.beaconSend index plaintext)) (by simp [RegistrationNativePublicCaps.IsMaterial])
    | beaconRaw index raw => exact quiet (.inr (.beaconRaw index raw)) (by simp [RegistrationNativePublicCaps.IsMaterial])

/-- Adaptive typed execution retains its whole current frontend and platform state under the source materialization equation. -/
theorem program_source (seeds : Seeds n) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : State source Platform) :
    simulateQ (translate true seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation) work).run before)) =
      simulateQ (translate false seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation) work).run before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [handler_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation seeds query before]
      apply bind_congr
      intro reached
      exact ih reached.1 reached.2

/-- The same equation holds for the original full raw ledger compiler in every mode. -/
theorem run_source (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform) :
    simulateQ (translate true seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation serverKeyId bounds mode work before)) =
      simulateQ (translate false seeds) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation serverKeyId bounds mode work before)) :=
  program_source setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation seeds _ before
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend.run_source
