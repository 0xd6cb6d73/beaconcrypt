-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding
/-! Literal startup and terminal CTX-cache, crypto-produced-frame and raw-counter decisions retain the actual corrected tree through the external-coin embedding. Only separately billed uniform/native/Env-coin coordinates are masked in the private intermediate World. The proved data observation ignores exactly those coordinates; dynamic writer failures and persistent platform state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)

noncomputable def client (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    OracleComp RegistrationNativeRetainedService.Spec (Bool × Platform) := do
  let initialized ← simulateQ RegistrationNativePublicRetained.coins
    ((RegistrationNativePublicStartupFrame.startup (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
      PqxdhRecordLiftWorld.initial)
  match initialized.1 with
  | none => pure (false, previous)
  | some started =>
      (fun result => (decision result.1.1 (RegistrationNativePlatformPublicWorldObservation.recordView result.2.world), result.1.2.2)) <$>
        (simulateQ (RegistrationNativePublicRetained.compiler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
          (RegistrationNativeMldsa.owned source started.credential))
          (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
            (RegistrationNativePlatformPublicRetainedRecordProfile.observed (n := n) setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary publicValue started previous))).run
          (RegistrationNativePublicRetained.clear { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 })

/-- Every actual generated-startup ledger/P decision is the same free retained-service program, for arbitrary future full108/key replies. -/
theorem client_source (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    RegistrationNativePlatformPublicRetainedRecordProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous =
      client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous := by
  unfold RegistrationNativePlatformPublicRetainedRecordProfile.client client
  apply bind_congr
  intro initialized
  cases initialized.1 with
  | none => rfl
  | some started =>
      simp only []
      rw [RegistrationNativePlatformPublicRetainedRecord.embedded]
      simp only [Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordEmbeddedProfile.client_source
