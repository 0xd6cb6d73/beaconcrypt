-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEagerContinuation
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup

/-! Actual effectful startup supplies the selected-first public-key invariant. Erasing only the generation ghost reconstructs the same startup and complete private source table. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEagerStartup
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaDynamicEagerStartup (startup erase fixed)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK)

/-- The complete actual dynamic selected-first experiment is bounded by the fixed-key native stopping experiment. -/
theorem bound (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V) (previous : Platform)
    (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativePlatformMldsaDynamicGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous selected ensureInit identityIndex serverKeyId)).run {}}[
      result.1.isSome = true] ≤
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId challenge.publicKey)).run {}}[
      result.1.isSome = true] := by
  simp only [RegistrationNativePlatformMldsaDynamicGame.program, RegistrationNativePlatformMldsaStoppedGame.program,
    simulateQ_bind, StateT.run_bind]
  rw [← erase source setup selected tape ensureInit identityIndex serverKeyId, bind_map_left]
  change Pr{let result ← (startup source setup selected tape ensureInit identityIndex serverKeyId >>= fun started =>
    (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativePlatformMldsaDynamicGame.continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary selected previous started.1)).run started.2)}[
        result.1.isSome = true] ≤ _
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro started possible
  rcases started with ⟨⟨initialized, ghost⟩, pool⟩
  cases initialized with
  | none =>
      simp only [RegistrationNativePlatformMldsaDynamicGame.continued, RegistrationNativePlatformMldsaStoppedGame.continued,
        Prod.map, id_eq, simulateQ_pure, StateT.run_pure]
      rfl
  | some initial =>
      simpa only [Prod.map, id_eq] using
        RegistrationNativePlatformMldsaDynamicEagerContinuation.bound source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary
          previous selected tape challenge chosen initial ghost pool
          (fixed source setup selected tape challenge chosen ensureInit identityIndex serverKeyId ((some initial, ghost), pool) possible)
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEagerStartup


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEagerStartup.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEagerStartup.bound
