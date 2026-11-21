-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemExceptions
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemResources
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal

/-! The all-owner staged agreement failure is stated on the complete original initialized native source journal with actual credentials, dynamic writers and private state. The bound excludes no admitted raw mode and charges one final cache collision, the actual ordinary ML-DSA reductions and qCreate*qAccept ordinary KEM failure. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative
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


/-- Failure of simultaneous staged contents on the literal original full-state native source journal. This game has no finite-recipient monitor or substituted credentials. -/
noncomputable def game (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none => pure false
    | some initial => (fun result => decide (¬ RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation initial.created view failure allocation erased
        rawAllocation serializer initial.credential result.2.2)) <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer))
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
          (adversary initial.public))).run ((initial.state, previous), [])

/-- The actual full native journal is one of the initialized retained history's proved realizations, so its failure is covered by the universal same-history failure event. -/
theorem cover (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) :
    Pr{let failed ← (game (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      rawAllocation serializer writer bounds mode adversary previous crypto)}[failed = true] ≤
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemHistorySource.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous)}[
      ¬ RegistrationNativePlatformOrdinaryAllOwnerSecurity.Holds setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer previous crypto result] := by
  classical
  unfold game RegistrationNativePlatformOrdinaryKemHistorySource.native
  simp only [prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro initialized
  by_cases possible : initialized ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  · apply mul_le_mul' le_rfl
    cases initialized with
    | none => simp only [prEvent_pure, RegistrationNativePlatformOrdinaryAllOwnerSecurity.Holds, not_true_eq_false, ite_false, Bool.false_eq_true, le_refl]
    | some initial =>
      dsimp only
      have projected := RegistrationNativeObservedStageTrace.full_project RegistrationNativePlatformOrdinaryKemClientJournal.observe
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
          (adversary initial.public)) ((initial.state, previous), [])
      simp only [List.map_nil] at projected
      rw [← projected]
      simp only [bind_pure_comp, decide_eq_true_eq, Functor.map_map, Prod.map, id_eq]
      apply prEvent_mono_of_support
      intro result supported failed clean
      let history : History n source Value Platform :=
        ⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial, result.1, RegistrationNativeKemServerState.ofNative result.2.1.1,
          result.2.2.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformOrdinaryKemClientJournal.observe)⟩
      have reached := RegistrationNativeStageTrace.path
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
          (adversary initial.public)) (initial.state, previous) result supported
      let execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.2 result.2.1.1.pool :=
        ⟨initial, possible, result.2.2, result.2.1.1, reached, rfl, rfl, rfl, rfl⟩
      change ∀ execution : RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer previous history result.2.1.2 result.2.1.1.pool,
        RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation execution.initial.created view failure allocation erased
          rawAllocation serializer execution.initial.credential execution.calls at clean
      exact failed (clean execution)
  · simp only [prEvent_eq_zero_of_not_mem_support _ possible, zero_mul, le_refl]

variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)

include bounded functional in
/-- Every protected successful finish, for every owner of the actual initialized native runtime, has its same-run staged Root/initializer/content partner except with one cache charge, the actual ordinary EUF family and qCreate*qAccept*δKEM. -/
theorem bound (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct) :
    Pr{let failed ← (game (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      rawAllocation serializer writer bounds mode adversary previous crypto)}[failed = true] ≤
      (Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  exact (cover setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
    rawAllocation serializer writer bounds mode adversary previous crypto).trans
      (RegistrationNativePlatformOrdinaryAllOwnerSecurity.bound setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer bounds mode adversary previous budget bounded functional crypto correct)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative.cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative.bound
