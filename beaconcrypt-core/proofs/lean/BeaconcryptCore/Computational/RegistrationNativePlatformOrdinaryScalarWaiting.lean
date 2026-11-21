-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster
/-! The eager challenge remains unused before the selected successful birth and cannot affect later creations after that position. Actual corrected callback roster receipts preserve this dichotomy with the same external platform state and dynamic source writers. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def Away (selected : Nat) (query : TypedSpec.Domain) (before : State n KemSK source) : Prop :=
  ∀ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) → before.beacons.length ≠ selected

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ordinary" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


local notation "eager" => RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- The actual corrected callback away from selected birth is exactly the original callback, including its same stateful platform actions. -/
theorem away_handler (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (query : TypedSpec.Domain)
    (before : State n KemSK source) (away : Away selected query before) :
    ((eager selected scalar query).run before) = ((ordinary query).run before) := by
  cases query with
  | inl coin => rfl
  | inr command =>
    cases command
    case create edPin mlPin keyId =>
      have localEq := RegistrationNativeScalarOrdinary.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        route representation created credential selected scalar (.inr (.create edPin mlPin keyId)) before (away edPin mlPin keyId rfl)
      change simulateQ RegistrationNativePlatformMldsaProgram.coins
        ((RegistrationNativeScalarEager.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
          route representation created source credential selected scalar (.inr (.create edPin mlPin keyId))).run before) = _
      rw [localEq]
      rfl
    all_goals rfl

/-- Every supported actual callback away from selected birth keeps that owner index waiting. -/
theorem away_short (selected : Nat) (query : TypedSpec.Domain) (before after : State n KemSK source)
    (previous next : Platform) (reply : TypedSpec.Range query) (short : before.beacons.length ≤ selected)
    (away : Away selected query before)
    (present : ((reply, after), next) ∈ support (((ordinary query).run before).run previous)) :
    after.beacons.length ≤ selected := by
  by_cases isCreate : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId)
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := isCreate
    have bounds := RegistrationNativePlatformOrdinaryScalarRoster.step_lengths setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before after previous next reply present
    have different := away edPin mlPin keyId rfl
    omega
  · push Not at isCreate
    rw [RegistrationNativePlatformOrdinaryScalarRoster.noncreate_length setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query isCreate before after previous next reply present]
    exact short

/-- After selected birth every future eager callback is the same actual dynamic runtime callback, with the complete native/platform pair retained. -/
theorem done_program (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (work : OracleComp TypedSpec Value)
    (before : State n KemSK source) (previous : Platform) (done : selected < before.beacons.length) :
    (((simulateQ ordinary work).run before).run previous) =
      (((simulateQ (eager selected scalar) work).run before).run previous) := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have away : Away selected query before := fun _ _ _ _ => by omega
    rw [away_handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer selected scalar query before away]
    apply OracleComp.bind_congr_of_forall_mem_support
    rintro ⟨⟨reply, current⟩, platform⟩ present
    have kept := (RegistrationNativePlatformOrdinaryScalarRoster.step_lengths setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before current previous platform reply present).1
    exact ih reply current platform (by omega)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.away_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.away_handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.away_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.away_short

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.done_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting.done_program
