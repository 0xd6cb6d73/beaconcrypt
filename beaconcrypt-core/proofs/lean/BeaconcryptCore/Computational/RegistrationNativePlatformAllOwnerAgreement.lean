-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCausalAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginJournal

/-! Every protected successful finish in one actual corrected initialized execution has staged same-run source contents and root-or-primitive-recipient-failure agreement, outside the one global origin-or-cache exception. All owner witnesses use the same execution and final cache; no separately sampled per-owner worlds are combined. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformInitializedAgreement (opened)
open RegistrationNativePlatformCausalAgreement (Outcome)
variable {n : Nat} {E Platform Value ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : AdapterSealPrimitive.Operations]
variable (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
variable (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
variable (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))

/-- One earlier actual source stage with all actual reached completion contents. Root agreement retains the explicit actual primitive-failure alternative. -/
def Partner (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish : Whole) (application : Pqxdh.Bytes) : Prop :=
    ∃ serverCall ∈ calls, ∃ receipt serverIndex serverInput,
      ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased (AdapterRecordRawBytes.helper rawAllocation serializer)
        serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt,
      serverCall.query = .inr (.build serverIndex serverInput) ∧
      ∃ matched : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime stage.token
        beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1),
      Outcome crypto setup checks wire route representation created owner pending oneTime index packet application (opened beforeFinish.1)
        stage.token beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1) matched stage.initial stage.plaintext

/-- All protected successful finishes in this single path, with the same actual final shared cache. -/
def AllOwners (credential : RegistrationNativeMldsa.Credential source)
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole) : Prop :=
  ∀ index pending packet owner oneTime beforeFinish afterFinish application,
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls →
    beforeFinish.1.beacons[index]? = some owner → owner.phase = .initSent pending oneTime →
    pending.binding.server_pin.public_key = credential.publicKey →
    Partner crypto setup checks wire route representation created view failure allocation erased rawAllocation serializer
      calls final index pending packet owner oneTime beforeFinish application

/-- The single reached origin exception discharges prior issuance simultaneously for every protected finish and every owner on the same actual initialized path. -/
theorem path (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (correct : view.Correct) (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer erased (AdapterRecordRawBytes.helper rawAllocation serializer) writer) (initial.state, previous) calls final)
    (good : ¬ RegistrationNativePlatformMldsaOriginJournal.BadCalls initial.credential calls)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final.1)) :
    AllOwners crypto setup checks wire route representation initial.created view failure allocation erased rawAllocation serializer initial.credential calls final := by
  intro index pending packet owner oneTime beforeFinish afterFinish application member found phase keyProtected
  have issued := RegistrationNativePlatformMldsaOriginJournal.finish_issued initial.credential calls good index packet application
    beforeFinish afterFinish member owner pending oneTime found phase keyProtected
  exact RegistrationNativePlatformCausalAgreement.path crypto setup checks wire route representation ensureInit identityIndex serverKeyId initial startup
    view correct failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer previous calls final reached index pending packet owner oneTime
      beforeFinish afterFinish application member found phase issued collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerAgreement.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerAgreement.path
