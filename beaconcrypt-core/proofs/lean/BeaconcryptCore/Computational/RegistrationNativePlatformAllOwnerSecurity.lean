-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerAgreement

/-! The complete initialized corrected source execution simultaneously supplies actual staged contents and root-or-primitive-failure agreement for every protected successful finish, except with one final-cache collision and the ordinary finite generated-key EUF loss. The private analysis journal erases exactly to the original source marker. Primitive recipient-failure probabilities are retained separately. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformAllOwnerAgreement (AllOwners)
open RegistrationNativePlatformMldsaOriginJournal (BadCalls)
variable {n : Nat} {E Platform V ι KemSK AD PT CT : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : AdapterSealPrimitive.Operations]
variable (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
variable (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "helper" => AdapterRecordRawBytes.helper rawAllocation serializer

/-- Every possible analysis-journal output derives simultaneous contents outside its actual origin-or-final-cache exception. -/
theorem continued (correct : view.Correct) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) :
    Pr{let result ← (simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation
      initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer)) work).run ((initial.state, previous), [])}[
      ¬ AllOwners crypto setup checks wire route representation initial.created view failure allocation erased rawAllocation serializer initial.credential result.2.2 result.2.1] ≤
    Pr{let result ← (simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation
      initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer)) work).run ((initial.state, previous), [])}[
      BadCalls initial.credential result.2.2 ∨ CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)] := by
  apply prEvent_mono_of_support
  intro result supported failed
  by_contra outside
  have good : ¬ BadCalls initial.credential result.2.2 := fun bad => outside (Or.inl bad)
  have collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1) := fun collision => outside (Or.inr collision)
  have reached := RegistrationNativeStageTrace.path _ work (initial.state, previous) result supported
  exact failed (RegistrationNativePlatformAllOwnerAgreement.path crypto setup checks wire route representation view failure allocation erased rawAllocation serializer
    ensureInit identityIndex serverKeyId initial startup correct reserveRegistration reservePeer writer previous result.2.2 result.2.1 reached good collisionFree)

variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V) (previous : Platform)

noncomputable def game (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none => pure false
    | some initial => (fun result => @decide (¬ AllOwners crypto setup checks wire route representation initial.created view failure allocation erased rawAllocation serializer
        initial.credential result.2.2 result.2.1) (Classical.propDecidable _)) <$>
        (simulateQ (RegistrationNativeStageTrace.handler
          (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created initial.credential
            view failure allocation reserveRegistration reservePeer erased helper writer))
          (adversary initial.public)).run ((initial.state, previous), [])

/-- Actual startup averaging covers failure of simultaneous staged contents by the one original origin-or-final-cache exception. -/
theorem cover (correct : view.Correct) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    Pr{let failed ← game (n := n) source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer adversary previous ensureInit identityIndex serverKeyId}[failed = true] ≤
    Pr{let failed ← RegistrationNativePlatformMldsaOriginJournal.game (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId}[failed = true] := by
  classical
  unfold game RegistrationNativePlatformMldsaOriginJournal.game
  simp only [prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro initialized
  by_cases possible : initialized ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  · apply mul_le_mul' le_rfl
    cases initialized with
    | none => exact le_rfl
    | some initial =>
        simpa only [prEvent_map, decide_eq_true_eq, RegistrationNativePlatformMldsaOriginJournal.flagged_iff, RegistrationNativeWorldCache.cache] using
          continued source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer
            correct ensureInit identityIndex serverKeyId initial possible previous (adversary initial.public)
  · simp only [prEvent_eq_zero_of_not_mem_support _ possible, zero_mul, le_refl]

/-- Simultaneous actual source contents and root-or-recipient-failure agreement pay one final-cache collision and the unchanged ordinary primitive EUF family. -/
theorem typed (correct : view.Correct) (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (game (n := n) source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer adversary previous
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (cap + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId)) := by
  apply (cover source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer
    adversary previous correct ensureInit identityIndex serverKeyId).trans
  exact RegistrationNativePlatformMldsaOriginJournal.typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous adversary cap bounded ensureInit identityIndex serverKeyId

/-- Simultaneous actual source contents and root-or-recipient-failure agreement pay one final-cache collision and the unchanged ordinary primitive EUF family. -/
theorem compiled (correct : view.Correct) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (game (n := n) source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  apply (cover source crypto setup checks wire route representation view failure allocation reserveRegistration reservePeer erased rawAllocation serializer writer
    (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue)) previous correct ensureInit identityIndex serverKeyId).trans
  exact RegistrationNativePlatformMldsaOriginJournal.compiled source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

end BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.continued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.continued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAllOwnerSecurity.compiled
