-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! The selected dynamic-writer runtime has one initialized joint origin, cache and recipient-marker bound. The chronological origin/cache event is transported from the literal source journal, and the actual finite recipient marker is charged once using the original qCreate and qAccept bills. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

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


variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
include bounded in
/-- The actual source history has the exact original per-API KEM bills after erasing only its private journal. -/
theorem resource (kind : RegistrationNativeKemResourceFootprint.Kind) :
    ((RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous).IsQueryBoundP
      (RegistrationNativeKemResourceCaps.Counted kind) (RegistrationNativePlatformKemHandlerResources.allowance kind budget) := by
  apply (isQueryBoundP_iff_of_map_eq (p := RegistrationNativeKemResourceCaps.Counted kind)
    (RegistrationNativePlatformOrdinaryKemInitializedJournal.erasure (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous)).mpr
  exact RegistrationNativePlatformOrdinaryKemResources.initialized (n := n) (source := source) setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer kind ensureInit identityIndex serverKeyId bounds mode adversary budget bounded previous

variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
omit primitives in
private theorem encapsulate_predicate : RegistrationNativeKemResourceCaps.Counted (KemSK := KemSK) .encapsulate =
    RegistrationNativeKemCountedRecipient.Charged := by
  funext query
  rcases query with uniform | (pool | key)
  · rfl
  · cases pool <;> rfl
  · rfl

include bounded in
/-- One actual common marker covers every recipient reply with qCreate*qAccept ordinary primitive failure rate. -/
theorem marker_bound :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional)}[result.2.2 = true] ≤
      budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  have encaps := resource (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded .encapsulate
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_encapsulate] at encaps
  apply RegistrationNativeKemRecipientLogSource.bound
  convert encaps using 1
  exact encapsulate_predicate.symm

def OriginCollision
    (result : ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK)) : Prop :=
  match result.1.1 with
  | none => False
  | some history => RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) history.initial.credential history.calls ∨
      CacheHasCollision (RegistrationNativeWorldCache.cache (RegistrationNativeKemServerState.toNative history.state result.2))

/-- The initialized projected history's one origin-or-final-cache exception is exactly the existing original Native union game, retaining the unchanged adaptive raw compilation. -/
theorem origin_native :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemHistorySource.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous)}[OriginCollision source result] =
    Pr{let failed ← (RegistrationNativePlatformOrdinaryMldsaOriginJournal.game (n := n) source setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[failed = true] := by
  classical
  unfold RegistrationNativePlatformOrdinaryKemHistorySource.native RegistrationNativePlatformOrdinaryMldsaOriginJournal.game
  simp only [prEvent_bind_eq_tsum]
  apply tsum_congr
  intro initialized
  cases initialized with
  | none => simp only [prEvent_pure, OriginCollision, ite_false, Bool.false_eq_true]
  | some initial =>
    apply congrArg (fun probability => _ * probability)
    have projected := RegistrationNativeObservedStageTrace.full_project RegistrationNativePlatformOrdinaryKemClientJournal.observe
      (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) ((initial.state, previous), [])
    have law := congrArg (fun distribution => Pr{let result ← distribution}[
      RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) initial.credential result.2.2 ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)]) projected
    have callBad (calls : List (Call TypedSpec (RegistrationNativeExperiment.State n KemSK source × Platform))) :
        RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) initial.credential
          (calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOrdinaryKemClientJournal.observe)) ↔
          RegistrationNativePlatformOrdinaryMldsaOriginJournal.BadCalls initial.credential calls :=
      RegistrationNativeKemClientObservation.bad_calls initial.credential calls
    simp only [prEvent_map, Prod.map, id_eq, callBad, List.map_nil] at law
    simp only [bind_pure_comp, prEvent_map, OriginCollision, RegistrationNativePlatformKemCountedProfile.ofInitial,
      RegistrationNativeKemServerState.native_roundtrip, decide_eq_true_eq,
      RegistrationNativePlatformOrdinaryMldsaOriginJournal.flagged_iff] at ⊢
    exact law.symm


include bounded in
/-- The private finite recipient family's initialized origin/cache observation has exactly the original Native chronological union-game probability. -/
theorem origin_probability :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional)}[
      OriginCollision source (result.2.1.1.1, result.2.1.2)] =
    Pr{let failed ← (RegistrationNativePlatformOrdinaryMldsaOriginJournal.game (n := n) source setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[failed = true] := by
  let work := (RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous
  have births := resource (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded .birth
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at births
  have birthBound : work.IsQueryBoundP RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert births using 1
    rfl
  have law := (RegistrationNativeKemCountedRecipientSource.source setup functional work budget.create birthBound).prEvent_eq (OriginCollision source)
  have logged := RegistrationNativeKemRecipientLogSource.erasure setup functional work budget.create
  rw [← logged, prEvent_map] at law
  dsimp only [work] at law
  rw [RegistrationNativePlatformOrdinaryKemHistorySource.source_history, origin_native] at law
  simpa only [prEvent_map, RegistrationNativeKemRecipientLogSource.erase,
    RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment] using law.symm

include bounded in
/-- The same initialized recipient execution pays the single original Native cache charge and actual ordinary generated-key EUF family for its origin/cache exception. -/
theorem origin_bound :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional)}[OriginCollision source (result.2.1.1.1, result.2.1.2)] ≤
      Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  rw [origin_probability (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional]
  exact RegistrationNativePlatformOrdinaryMldsaOriginJournal.compiled source setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

include bounded in
/-- The original chronological origin/cache union and the actual same-execution recipient marker share one cache charge. -/
theorem exceptions_bound :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget functional)}[
      OriginCollision source (result.2.1.1.1, result.2.1.2) ∨ result.2.2 = true] ≤
      (Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  apply (prEvent_or_le _ _ _).trans
  exact add_le_add (origin_bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional)
    (marker_bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous budget bounded functional)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.resource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.resource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.marker_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.marker_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.origin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.exceptions_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions.exceptions_bound
