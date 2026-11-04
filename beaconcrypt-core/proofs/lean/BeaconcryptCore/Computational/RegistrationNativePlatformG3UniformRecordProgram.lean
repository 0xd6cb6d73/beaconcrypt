-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueGame
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto
/-! The complete warm sampler is an explicit private reduction prefix of one actual gated native reference client. Its original produced/raw event is the actual initialized opaque-source event. No average of conditional absolute advantages is renamed as one advantage. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : Value × RegistrationNativeLedger.State → List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool)


structure Sample (KemSK : Type) (cap : Nat) where
  seed : PqxdhJointIdentity.IdentitySeed
  scalar : PqxdhJointGapDh.ScalarBytes
  unused : RegistrationNativeG3Tables.MaterialTable cap
  profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK
  candidate : PqxdhKemIndCca.MlKemSharedSecret
  materials : RegistrationNativeG3Tables.MaterialTable cap

noncomputable def sample (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :
    ProbComp (Sample KemSK (budget.cap 4 + budget.cap 5)) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let unused ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let parameters ← RegistrationNativePlatformG3UniformOpaqueGame.draws setup budget selected
  pure ⟨seed,scalar,unused,parameters.1,parameters.2.1,parameters.2.2⟩

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (parameters : Sample KemSK (budget.cap 4 + budget.cap 5)) :=
  RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source parameters.seed parameters.scalar parameters.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) bounds mode adversary

noncomputable def program (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) := do
  let parameters ← simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected)
  after setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous parameters

/-- The complete original event is the all-real observation of one whole-prefix client, with the actual dynamic platform behavior. -/
theorem real_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    Prod.fst <$> RegistrationNativePlatformG3UniformOpaqueGame.game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (RegistrationNativePlatformG3UniformOpaqueRecord.decision observe) budget selected previous =
      RegistrationNativePlatformG3UniformOpaqueRecord.event source observe <$>
        RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
          (program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous) := by
  unfold RegistrationNativePlatformG3UniformOpaqueRecord.event
  rw [program,RegistrationNativePlatformRecordPrefix.real_source setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
    (sample setup budget selected) _ (RegistrationNativePlatformG3UniformOpaqueRecord.outcomeEvent source observe)]
  unfold RegistrationNativePlatformG3UniformOpaqueGame.game sample
  simp only [map_bind,bind_assoc,pure_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  apply bind_congr
  intro unused
  apply bind_congr
  intro parameters
  rw [RegistrationNativePlatformG3UniformOpaqueRecord.actual_source]
  unfold after
  rw [RegistrationNativePlatformSelectiveReferenceCrypto.real_transport]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram.real_source
