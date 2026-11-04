-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions
import BeaconcryptCore.Computational.RegistrationNativeKemActualHandlePersistence
import BeaconcryptCore.Computational.RegistrationNativePlatformActualMatchedTuple
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemTokenRoot
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistoryPath
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemActualBlocks

/-! A moved token and reached pending owner in the selected single runtime determine the same actual Root collector and original Beacon public tuple. The source pin/authentication, earlier bundle and digest/cache chronology are derived from one complete initialized execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemRows
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {Platform E : Type}
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)

open RegistrationNativeStageTrace (Call)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
local notation "coins" => RegistrationNativePlatformMldsaProgram.coins

/-- Every retained owner at every actual source callback selects its identical genuine row in this one initialized recipient experiment. -/
theorem selected (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform)
    (path : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.1.1.2 result.2.1.2)
    (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (member : call ∈ path.calls)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (found : call.before.1.beacons[index]? = some owner) :
    ∃ target : Fin budget.create, call.before.1.pool.keys[owner.kemHandle]? = some (result.1 target).1 ∧
      (result.1 target).1.1 = owner.kemPublic := by
  obtain ⟨_leading, _trailing, _split, before, called, following⟩ := path.reached.member call member
  have facts := RegistrationNativePlatformOrdinaryAgreementFacts.initialized setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId path.initial path.startup previous call.before _ before
  obtain ⟨pair, atOwner, publicKey⟩ := facts.1.2 owner (List.mem_of_getElem? found)
  have finalRow := RegistrationNativePlatformOrdinaryPoolLookup.path setup checks wire route representation path.initial.created path.initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.cons call called _ _ following) owner.kemHandle pair atOwner
  rw [← path.poolEq] at finalRow
  have birth := RegistrationNativePlatformOrdinaryKemExceptions.resource (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded .birth
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at birth
  have birthBound : ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous).IsQueryBoundP
      RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert birth using 1
    rfl
  obtain ⟨target, same⟩ := RegistrationNativeKemRecipientLogSource.handle setup functional _ budget.create birthBound result supported owner.kemHandle pair finalRow
  exact ⟨target, by rw [same]; exact atOwner, by rw [same]; exact publicKey⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemRows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemRows.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemRows.selected
