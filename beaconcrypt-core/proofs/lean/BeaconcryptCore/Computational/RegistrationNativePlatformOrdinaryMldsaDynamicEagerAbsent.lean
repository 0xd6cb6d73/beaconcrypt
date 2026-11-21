-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicEagerStartup
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerFailure

/-! A failed selected generation attempt makes the dynamically learned-key candidate event impossible, including all later adaptive callbacks and failed native startup branches. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicEagerAbsent
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaEuf (Forgery)
open RegistrationNativeMldsaGhostEagerFailure (Empty)
open RegistrationNativeMldsaStop (freeze)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)

private theorem continued_none (previous : Platform) (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none) (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source))
    (ghost : RegistrationNativeMldsaGenerationGhost.State) (pool : Pool source) (empty : Empty source (ghost, pool))
    (result : Option Forgery × Pool source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativePlatformOrdinaryMldsaDynamicGame.continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary selected previous (some initial, ghost))).run pool)) :
    result.1 = none := by
  let native := RegistrationNativePlatformOrdinaryMldsaCountStop.handler (n := n) setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let observer := RegistrationNativePlatformOrdinaryMldsaCountStop.observe (n := n) (KemSK := KemSK) (Platform := Platform) (source := handleSource source)
  let callback := fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (native query)
  let dynamic := RegistrationNativeMldsaGhostEagerExecution.dynamic source observer
  let before := ((initial.state, previous), (ghost, pool))
  have coupled := RegistrationNativeMldsaGhostEagerStop.program source selected tape native observer
    RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public) ((initial.state, previous), ghost) none pool
  simp only [RegistrationNativePlatformOrdinaryMldsaDynamicGame.continued, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have reached : RegistrationNativeMldsaGhostEagerStop.arrange source inner ∈ support
      ((simulateQ (freeze callback dynamic RegistrationNativeMldsaTableStop.defaultReply) (adversary initial.public)).run (before, none)) := by
    rw [← coupled, support_map]
    exact ⟨inner, possible, rfl⟩
  have law := RegistrationNativeMldsaStop.freeze_property callback dynamic RegistrationNativeMldsaTableStop.defaultReply
    (fun current => Empty source current.2) (fun _ _ => False)
    (fun query current output good possible => RegistrationNativeMldsaGhostEagerFailure.execute_empty source selected tape failed
      (native query) current good output possible)
    (by
      intro query current output forgery good possible captured
      have after := RegistrationNativeMldsaGhostEagerFailure.execute_empty source selected tape failed
        (native query) current good output possible
      simp only [dynamic, RegistrationNativeMldsaGhostEagerExecution.dynamic, after.2, Option.bind_none] at captured
      cases captured)
    (adversary initial.public) before none empty (by intro candidate impossible; cases impossible)
    (RegistrationNativeMldsaGhostEagerStop.arrange source inner) reached
  cases selected : inner.1.2.2 with
  | none => exact selected
  | some forgery => exact (law.2 forgery selected).elim

omit primitive in
private theorem startup_empty (selected : Nat) (tape : List (Option (Credential source)))
    (failed : tape[selected]? = some none) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (result : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaDynamicEagerStartup.startup source setup selected tape ensureInit identityIndex serverKeyId)) :
    Empty source (result.1.2, result.2) := by
  have joint : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (RegistrationNativeMldsaGhostEager.handler source selected tape)
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)).run ({}, {})) := by
    rw [RegistrationNativeMldsaGhostEager.source_program, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativeMldsaGhostEagerFailure.program_empty source selected tape failed
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) ({}, {}) ⟨rfl, rfl⟩ _ joint

/-- Failure of the selected actual generator makes the complete ordinal-only candidate event vanish. -/
theorem zero (previous : Platform) (selected : Nat) (tape : List (Option (Credential source))) (failed : tape[selected]? = some none)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativePlatformOrdinaryMldsaDynamicGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId)).run {}}[
      result.1.isSome = true] = 0 := by
  apply prEvent_eq_zero_of_forall_mem_support
  intro result supported hit
  simp only [RegistrationNativePlatformOrdinaryMldsaDynamicGame.program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨started, startup, continued⟩ := supported
  have empty := startup_empty source setup selected tape failed ensureInit identityIndex serverKeyId started startup
  rcases started with ⟨⟨initialized, ghost⟩, pool⟩
  cases initialized with
  | none =>
      simp only [RegistrationNativePlatformOrdinaryMldsaDynamicGame.continued, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at continued
      cases continued
      cases hit
  | some initial =>
      have absent := continued_none source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected tape failed initial ghost pool empty result continued
      rw [absent] at hit
      cases hit
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicEagerAbsent


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicEagerAbsent.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicEagerAbsent.zero
