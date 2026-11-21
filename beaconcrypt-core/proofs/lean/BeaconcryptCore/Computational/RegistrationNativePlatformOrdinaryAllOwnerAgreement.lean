-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal

/-! All protected successful finishes share one initialized dynamic-writer execution, actual source partner stages in each strict before-finish prefix, equal roots and complementary initializer contents. Only the single original origin/cache exception or actual finite-recipient marker is excluded; there is no perfect-correctness or separately sampled owner-world premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformInitializedAgreement (opened)
open RegistrationNativePlatformOrdinaryCausalAgreement (Outcome)
variable {n : Nat} {E Platform Value ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : AdapterSealPrimitive.Operations]
/-- One response signing stage in the strict prefix before this exact successful finish, with equal Root, complementary initializers and reached unsigned binding/application contents. This non-injective partner need not finish publication or installation. -/
def Partner (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes) : Prop :=
  ∃ leading trailing serverCall,
    calls=leading++(⟨.inr (.finish index (some packet)),beforeFinish,.ok (some application),afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole)::trailing ∧
    serverCall∈leading ∧ ∃ receipt serverIndex serverInput,
    ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) view failure allocation erased
      (AdapterRecordRawBytes.helper rawAllocation serializer) serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt,
    serverCall.query = .inr (.build serverIndex serverInput) ∧
    Outcome source crypto setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) representation created owner pending oneTime index packet application
      (opened beforeFinish.1) stage.token stage.initial stage.plaintext

/-- Every protected successful finish for every owner in this one actual execution has those same-run staged contents. -/
def AllOwners (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (credential : RegistrationNativeMldsa.Credential source)
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) : Prop :=
  ∀ index pending packet owner oneTime beforeFinish afterFinish application,
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls →
    beforeFinish.1.beacons[index]? = some owner → owner.phase = .initSent pending oneTime →
    pending.binding.server_pin.public_key = credential.publicKey →
    Partner crypto setup checks wire representation created view failure allocation erased rawAllocation serializer calls index pending packet owner oneTime beforeFinish afterFinish application

/-- The actual initialized joint analysis covers all owners simultaneously, outside its one original origin/cache exception and actual finite-recipient marker. -/
theorem path (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (RegistrationNativePlatformKemInitializedJournal.History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer bounds mode adversary previous budget functional))
    (history : RegistrationNativePlatformKemInitializedJournal.History n source Value Platform) (returned : result.2.1.1.1.1 = some history)
    (execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer previous history result.2.1.1.1.2 result.2.1.2)
    (good : ¬ RegistrationNativePlatformOrdinaryMldsaOriginJournal.BadCalls execution.initial.credential execution.calls)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache execution.finalNative)) (marker : result.2.2 ≠ true) :
    AllOwners crypto setup checks wire representation execution.initial.created view failure allocation erased rawAllocation serializer execution.initial.credential execution.calls := by
  intro index pending packet owner oneTime beforeFinish afterFinish application member found phase protectedKey
  have issued := RegistrationNativePlatformOrdinaryMldsaOriginJournal.finish_issued execution.initial.credential execution.calls good index packet application
    beforeFinish afterFinish member owner pending oneTime found phase protectedKey
  exact RegistrationNativePlatformOrdinaryCausalAgreement.path setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer bounds mode adversary previous crypto correct budget bounded functional
      result supported history returned execution index pending packet owner oneTime beforeFinish afterFinish application member found phase issued collisionFree marker

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement.path
