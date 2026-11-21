-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecipientMonitor
import BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource

/-! The complete initialized corrected Platform has one private same-run capability log, actual recipient row family and sticky failure marker. Erasure recovers the literal original source profile; all raw modes, adaptive callers, platform state and genuine primitive costs remain. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source) (functional : FunctionalDecapsulation setup.kem)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (budget : Budget) (previous : Platform)


abbrev Output (n : Nat) (source : RegistrationNativeMldsa.Source) (Value Platform : Type) :=
  (Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeKemServerState.State n source) × Platform)

noncomputable def experiment := RegistrationNativeKemRecipientLogSource.experiment setup functional
  (RegistrationNativePlatformRecipientMonitor.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary previous) budget.create

variable (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))

include bounded in
/-- Erasing only private analysis fields recovers the complete literal initialized source event and its actual final Platform state. -/
theorem source_profile (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    EvalDistEq
      ((RegistrationNativePlatformExperiment.profile (n := n) coins setup checks wire route representation source ensureInit identityIndex serverKeyId view failure
        allocation reserveRegistration reservePeer erased helper writer bounds mode adversary event).run previous)
      ((fun result => RegistrationNativePlatformKemCountedProfile.observe event
        (RegistrationNativeKemRecipientLogSource.erase result).2.1) <$>
        experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous) := by
  have law := RegistrationNativePlatformRecipientMonitor.source_profile (n := n) setup checks wire route representation source functional ensureInit identityIndex
    serverKeyId view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous bounded event
  have erasure := RegistrationNativeKemRecipientLogSource.erasure setup functional
    (RegistrationNativePlatformRecipientMonitor.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous) budget.create
  change RegistrationNativeKemRecipientLogSource.erase <$>
      experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous =
    RegistrationNativePlatformRecipientMonitor.experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure
      allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous at erasure
  rw [← erasure] at law
  simpa only [Functor.map_map] using law

include bounded in
/-- The full initialized same-run marker retains the exact qCreate*qAccept honest-recipient failure bill. -/
theorem bound :
    Pr{let result ← (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous)}[result.2.2 = true] ≤
      budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  have checked := RegistrationNativePlatformRecipientMonitor.bound (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId
    view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous bounded
  have erasure := RegistrationNativeKemRecipientLogSource.erasure setup functional
    (RegistrationNativePlatformRecipientMonitor.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous) budget.create
  change RegistrationNativeKemRecipientLogSource.erase <$>
      experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous =
    RegistrationNativePlatformRecipientMonitor.experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure
      allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous at erasure
  rw [← erasure, prEvent_map] at checked
  exact checked

/-- Every bad encapsulation reply retained in the complete initialized actual capability log sets its final marker. -/
theorem sound
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Output n source Value Platform) budget.create)
    (supported : result ∈ support (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous))
    (entry : (query : (RegistrationNativeKemCountedProgram.Spec KemSK).Domain) × (RegistrationNativeKemCountedProgram.Spec KemSK).Range query)
    (member : entry ∈ result.2.1.1.2)
    (bad : RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional result.1 entry.1 entry.2) :
    result.2.2 = true :=
  RegistrationNativeKemRecipientLogSource.sound setup functional _ budget.create result supported entry member bad

def LogBad {Out : Type} {count : Nat}
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK Out count) : Prop :=
  ∃ entry ∈ result.2.1.1.2, RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional result.1 entry.1 entry.2

include bounded in
/-- The initialized probability of any actual bad logged recipient reply has the same finite bill, including aliased public keys. -/
theorem failure_bound :
    Pr{let result ← (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous)}[LogBad setup functional result] ≤
      budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  apply le_trans _ (bound (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous bounded)
  apply prEvent_mono_of_support
  intro result supported bad
  obtain ⟨entry, member, invalid⟩ := bad
  exact sound setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous result supported entry member invalid

include bounded in
/-- A private handle returned by this complete initialized execution selects an exact row in the very same logged recipient family. -/
theorem handle
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Output n source Value Platform) budget.create)
    (supported : result ∈ support (experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous))
    (handle : Nat) (pair : RegistrationNativeKemCountedReservedRows.Pair KemSK)
    (found : result.2.1.2.keys[handle]? = some pair) : ∃ target, (result.1 target).1 = pair := by
  have erasure := RegistrationNativeKemRecipientLogSource.erasure setup functional
    (RegistrationNativePlatformRecipientMonitor.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous) budget.create
  have erasedSupport : RegistrationNativeKemRecipientLogSource.erase result ∈ support
      (RegistrationNativePlatformRecipientMonitor.experiment (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure
        allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous) := by
    unfold RegistrationNativePlatformRecipientMonitor.experiment
    rw [← erasure, support_map]
    exact Set.mem_image_of_mem _ supported
  exact RegistrationNativePlatformRecipientMonitor.handle (n := n) setup checks wire route representation source functional ensureInit identityIndex serverKeyId view failure
    allocation reserveRegistration reservePeer erased helper writer bounds mode adversary budget previous bounded
    (RegistrationNativeKemRecipientLogSource.erase result) erasedSupport handle pair found

end BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.source_profile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.sound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.failure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.failure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecipientLog.handle
