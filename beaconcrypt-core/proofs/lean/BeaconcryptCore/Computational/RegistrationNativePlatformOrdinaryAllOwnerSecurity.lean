-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! Simultaneous native equal-root, both-initializer and complete source contents agreement is bounded on the literal initialized dynamic-writer runtime. Actual source histories are preserved when only private finite-row monitoring is erased; one final cache term, actual ordinary EUF reductions and qCreate*qAccept ordinary KEM failure remain. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value AD PT CT : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
variable (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
local notation "helper" => AdapterRecordRawBytes.helper rawAllocation serializer
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


/-- Simultaneous source contents are required for every actual full-state realization of this retained same-run source history. Actual initialized support separately derives such a realization. -/
def Holds (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (result : ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK)) : Prop :=
  match result.1.1 with
  | none => True
  | some history => ∀ execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.1.2 result.2,
    RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation execution.initial.created view failure allocation erased
      rawAllocation serializer execution.initial.credential execution.calls

variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)

include bounded in
/-- Each actual initialized joint-analysis result has simultaneous owner agreement outside the original origin/cache union and that same run's recipient marker. -/
theorem coverage (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional))
    (origin : ¬ RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1, result.2.1.2))
    (marker : result.2.2 ≠ true) :
    Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      rawAllocation serializer writer previous crypto (result.2.1.1.1, result.2.1.2) := by
  unfold Holds
  cases returned : result.2.1.1.1.1 with
  | none => trivial
  | some history =>
    intro execution
    have clean : ¬ (RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) history.initial.credential history.calls ∨
      CacheHasCollision (RegistrationNativeWorldCache.cache (RegistrationNativeKemServerState.toNative history.state result.2.1.2))) := by
      simpa only [RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision, returned] using origin
    have credentialEq : history.initial.credential = execution.initial.credential :=
      congrArg RegistrationNativePlatformKemCountedProfile.Initial.credential execution.initialEq
    have good : ¬ RegistrationNativePlatformOrdinaryMldsaOriginJournal.BadCalls execution.initial.credential execution.calls := by
      intro bad
      apply clean
      apply Or.inl
      rw [execution.callsEq, credentialEq]
      exact (RegistrationNativeKemClientObservation.bad_calls execution.initial.credential execution.calls).mpr bad
    have collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache execution.finalNative) := by
      intro collision
      apply clean
      apply Or.inr
      rw [execution.stateEq]
      exact collision
    exact RegistrationNativePlatformOrdinaryAllOwnerAgreement.path crypto setup checks wire route representation ensureInit identityIndex serverKeyId
      view correct failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer bounds mode adversary previous budget bounded functional
        result supported history returned execution good collisionFree marker

include bounded in
/-- Removing only the finite-row monitor and private capability log recovers the literal complete original Native source-history event probability. -/
theorem source_probability (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional)}[
      ¬ Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto
        (result.2.1.1.1, result.2.1.2)] =
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemHistorySource.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous)}[
      ¬ Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto result] := by
  let work := (RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous
  have births := RegistrationNativePlatformOrdinaryKemExceptions.resource (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded .birth
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at births
  have birthBound : work.IsQueryBoundP RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert births using 1
    rfl
  have law := (RegistrationNativeKemCountedRecipientSource.source setup functional work budget.create birthBound).prEvent_eq
    (fun result => ¬ Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto result)
  have logged := RegistrationNativeKemRecipientLogSource.erasure setup functional work budget.create
  rw [← logged, prEvent_map] at law
  dsimp only [work] at law
  rw [RegistrationNativePlatformOrdinaryKemHistorySource.source_history] at law
  simpa only [prEvent_map, RegistrationNativeKemRecipientLogSource.erase,
    RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment] using law.symm

/-- The universal receipt statement is nonvacuous on actual initialized source support: the same run supplies a full native path with simultaneous contents. -/
theorem realized (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (result : ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK))
    (supported : result ∈ support (RegistrationNativePlatformOrdinaryKemHistorySource.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous))
    (good : Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto result)
    (history : History n source Value Platform) (returned : result.1.1 = some history) :
    ∃ execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.1.2 result.2,
      RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation execution.initial.created view failure allocation erased
        rawAllocation serializer execution.initial.credential execution.calls := by
  have evaluated := supported
  rw [← RegistrationNativePlatformOrdinaryKemHistorySource.source_history] at evaluated
  have matching : ((some history, result.1.2), result.2) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) PqxdhLiveKemBirth.empty) := by
    change ((result.1.1, result.1.2), result.2) ∈ _ at evaluated
    rw [returned] at evaluated
    exact evaluated
  obtain ⟨execution⟩ := RegistrationNativePlatformOrdinaryKemHistoryPath.actual setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous history result.1.2 result.2 matching
  have all : ∀ execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer previous history result.1.2 result.2,
      RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation execution.initial.created view failure allocation erased
        rawAllocation serializer execution.initial.credential execution.calls := by
    simpa only [Holds, returned] using good
  exact ⟨execution, all execution⟩

include bounded functional in
/-- Failure of simultaneous equal-root, both-initializer and full source-content agreement on the literal initialized runtime pays one original cache charge, the ordinary EUF family and qCreate*qAccept*δKEM. -/
theorem bound (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct) :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemHistorySource.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous)}[
      ¬ Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto result] ≤
      (Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [← source_probability setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer
    bounds mode adversary previous budget bounded functional crypto]
  apply le_trans _ (RegistrationNativePlatformOrdinaryKemExceptions.exceptions_bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional)
  apply prEvent_mono_of_support
  intro result supported failed
  by_contra outside
  have good := coverage setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer
    bounds mode adversary previous budget bounded functional crypto correct result supported
      (fun origin => outside (Or.inl origin)) (fun marker => outside (Or.inr marker))
  exact failed good

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.coverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.source_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.source_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity.realized
