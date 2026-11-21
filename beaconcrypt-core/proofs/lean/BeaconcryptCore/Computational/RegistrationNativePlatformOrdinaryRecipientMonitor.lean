-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources

/-! The complete initialized corrected Platform profile has one actual finite recipient-error monitor with its original qCreate and qAccept bill. All admitted raw queries, startup failures, stateful source writers, exact primitive costs, final platform state and private recipient rows are retained. This primitive monitor is separate from the source Root/agreement coverage theorem. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

omit primitives in
private theorem encapsulate_predicate : RegistrationNativeKemResourceCaps.Counted (KemSK := KemSK) .encapsulate =
    RegistrationNativeKemCountedRecipient.Charged := by
  funext query
  rcases query with uniform | (pool | key)
  · rfl
  · cases pool <;> rfl
  · rfl

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source) (functional : FunctionalDecapsulation setup.kem)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (budget : Budget) (previous : Platform)

noncomputable def program :=
  (RegistrationNativePlatformOrdinaryKemProfile.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous

noncomputable def experiment := RegistrationNativeKemCountedRecipientSource.experiment setup functional
  (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary previous) budget.create

variable (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))

include bounded in
/-- Erasing only the private recipient analysis recovers the complete actual initialized source profile and final platform state. -/
theorem source_profile (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    EvalDistEq
      ((RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure
        allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous)
      ((fun result => RegistrationNativePlatformKemCountedProfile.observe event result.2.1) <$>
        experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget previous) := by
  have birth := RegistrationNativePlatformOrdinaryKemResources.initialized (n := n) (source := source) setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer .birth ensureInit identityIndex serverKeyId bounds mode adversary budget bounded previous
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at birth
  have birthBound : (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous).IsQueryBoundP
      RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert birth using 1 <;> rfl
  have law := (RegistrationNativeKemCountedRecipientSource.source setup functional
    (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary previous) budget.create birthBound).map (RegistrationNativePlatformKemCountedProfile.observe event)
  unfold program at law
  rw [RegistrationNativePlatformOrdinaryKemProfile.source_profile] at law
  simpa only [Functor.map_map, experiment, program] using law

include bounded in
/-- The original complete raw budget charges qCreate actual recipient rows and qAccept actual encapsulations, with no perfect-correctness assumption. -/
theorem bound :
    Pr{let result ← (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget previous)}[result.2.2 = true] ≤
      budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  have encaps := RegistrationNativePlatformOrdinaryKemResources.initialized (n := n) (source := source) setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer .encapsulate ensureInit identityIndex serverKeyId bounds mode adversary budget bounded previous
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_encapsulate] at encaps
  have encapsBound : (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous).IsQueryBoundP
      RegistrationNativeKemCountedRecipient.Charged budget.accept := by
    convert encaps using 1 <;> first
      | rfl
      | exact encapsulate_predicate.symm
  exact RegistrationNativeKemCountedRecipientSource.bound setup functional _ budget.create budget.accept encapsBound
include bounded in
/-- Every reached private recipient handle in the complete initialized analysis selects one exact genuine finite-family row. -/
theorem handle
    (result : (Fin budget.create → RegistrationNativeKemCountedRecipientSample.Draw KemSK) ×
      (((Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeKemServerState.State n source) × Platform) ×
        PqxdhLiveKemBirth.Pool KemSK) × Bool))
    (supported : result ∈ support (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget previous))
    (handle : Nat) (pair : RegistrationNativeKemCountedReservedRows.Pair KemSK)
    (found : result.2.1.2.keys[handle]? = some pair) : ∃ target, (result.1 target).1 = pair := by
  have birth := RegistrationNativePlatformOrdinaryKemResources.initialized (n := n) (source := source) setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer .birth ensureInit identityIndex serverKeyId bounds mode adversary budget bounded previous
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at birth
  have birthBound : (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous).IsQueryBoundP
      RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert birth using 1 <;> rfl
  exact RegistrationNativeKemCountedRecipientSource.handle setup functional _ budget.create birthBound result supported handle pair found

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.source_profile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRecipientMonitor.handle
