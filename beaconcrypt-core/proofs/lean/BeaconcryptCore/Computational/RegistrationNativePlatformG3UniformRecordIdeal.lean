-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal
/-! The one whole-prefix warm reference client retains its native ideal baselines. Independent prefix sampling is interpreted on the actual reached private state; no cache reset or runtime/reduction counter identity is used. LR retains the explicit hidden-test qualifier pending broad designation attachment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal
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
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
open RegistrationNativePlatformG3UniformRecordProgram (program after)

noncomputable def run (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :=
  RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
    (program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds .P adversary budget selected previous)

/-- Exact fairness for the native test bit and physically hidden admitted tests after the complete warm prefix. -/
theorem lor (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) :
    𝒟[RegistrationNativeLorEntropy.winningView setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId budget filter guess target <$>
      run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous] {true} =
      2⁻¹ * 𝒟[RegistrationNativeLorEntropy.eligibleView setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId budget filter target <$>
        run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous] {true} := by
  simp only [run,RegistrationNativeRecordPackage.ctx_source,program,Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true,CborRawRecordOriginFlatten.interpret_bind]
  apply RegistrationNativeLorStartup.bind_half
  rintro ⟨⟨⟨parameters,shell⟩,control⟩,secret⟩ _
  have fair := RegistrationNativePlatformSelectiveReferenceReachedIdeal.lor setup checks wire source parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) bounds adversary shell control secret route budget filter guess target
  simpa only [RegistrationNativePlatformSelectiveReferenceReachedIdeal.run,after,Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true] using fair

/-- The complete same-run selector mass has one fresh-byte baseline, with no target-game summation. -/
theorem fresh_bytes (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : RegistrationNativeCanonicalSelector.Target budget) :
    𝒟[RegistrationNativeWeightedRecordView.winning setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId budget claim target <$>
      run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[RegistrationNativeWeightedRecordView.selection setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId budget claim target <$>
          run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous] {true} := by
  simp only [run,RegistrationNativeRecordPackage.ctx_source,program,Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true,CborRawRecordOriginFlatten.interpret_bind]
  apply RegistrationNativeWeightedStartup.bind_weighted
  rintro ⟨⟨⟨parameters,shell⟩,control⟩,secret⟩ _
  have bound := RegistrationNativePlatformSelectiveReferenceReachedIdeal.fresh_bytes setup checks wire source parameters.seed parameters.scalar parameters.candidate (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate) selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.materials) bounds adversary shell control secret route budget claim target
  simpa only [RegistrationNativePlatformSelectiveReferenceReachedIdeal.run,after,Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true] using bound
end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal.lor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal.fresh_bytes
