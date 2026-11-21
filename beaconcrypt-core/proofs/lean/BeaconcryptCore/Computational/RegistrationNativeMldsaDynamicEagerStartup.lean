-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerContinuation

/-! Actual effectful startup supplies the selected-first public-key invariant. Erasing only the generation ghost reconstructs the same startup and complete private source table. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK)

noncomputable def startup (selected : Nat) (tape : List (Option (Credential source)))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    ProbComp ((Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) × Pool source) :=
  (simulateQ (RegistrationNativeMldsaEager.handler source tape)
    (RegistrationNativeMldsaGenerationGhost.run source selected
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {})).run {}

/-- Erasing only actual public generation tracking retains the complete original startup and private table. -/
theorem erase (selected : Nat) (tape : List (Option (Credential source)))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Prod.map Prod.fst id <$> startup (n := n) source setup selected tape ensureInit identityIndex serverKeyId =
      (simulateQ (RegistrationNativeMldsaEager.handler source tape)
        (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId)).run {} := by
  have same := congrArg (fun program => (simulateQ (RegistrationNativeMldsaEager.handler source tape) program).run ({} : Pool source))
    (RegistrationNativeMldsaGenerationGhost.erase source selected
      (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {})
  change (fun result : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) × Pool source => (result.1.1, result.2)) <$> _ = _
  simpa only [startup, simulateQ_map, StateT.run_map] using same

/-- Every actual startup outcome derives the selected-key invariant, including failed initialization. -/
theorem fixed (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (result : (Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × RegistrationNativeMldsaGenerationGhost.State) × Pool source)
    (supported : result ∈ support (startup source setup selected tape ensureInit identityIndex serverKeyId)) :
    RegistrationNativeMldsaGhostEager.Fixed source challenge.publicKey (result.1.2, result.2) := by
  have joint : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (RegistrationNativeMldsaGhostEager.handler source selected tape)
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId)).run ({}, {})) := by
    rw [RegistrationNativeMldsaGhostEager.source_program, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativeMldsaGhostEager.program_fixed source selected tape challenge chosen
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) ({}, {})
    ⟨rfl, by intro key impossible; cases impossible⟩ _ joint

/-- The complete actual dynamic selected-first experiment is bounded by the fixed-key native stopping experiment. -/
theorem bound (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (selected : Nat) (tape : List (Option (Credential source)))
    (challenge : Credential source) (chosen : tape[selected]? = some (some challenge))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativeMldsaDynamicGame.program (n := n) source setup checks wire route representation adversary selected ensureInit identityIndex serverKeyId)).run {}}[
      result.1.isSome = true] ≤
    Pr{let result ← (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId challenge.publicKey)).run {}}[
      result.1.isSome = true] := by
  simp only [RegistrationNativeMldsaDynamicGame.program, RegistrationNativeMldsaStoppedGame.program,
    simulateQ_bind, StateT.run_bind]
  rw [← erase source setup selected tape ensureInit identityIndex serverKeyId, bind_map_left]
  change Pr{let result ← (startup source setup selected tape ensureInit identityIndex serverKeyId >>= fun started =>
    (simulateQ (RegistrationNativeMldsaEager.handler source tape)
      (RegistrationNativeMldsaDynamicGame.continued source setup checks wire route representation adversary selected started.1)).run started.2)}[
        result.1.isSome = true] ≤ _
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro started possible
  rcases started with ⟨⟨initialized, ghost⟩, pool⟩
  cases initialized with
  | none =>
      simp only [RegistrationNativeMldsaDynamicGame.continued, RegistrationNativeMldsaStoppedGame.continued,
        Prod.map, id_eq, simulateQ_pure, StateT.run_pure]
      rfl
  | some initial =>
      simpa only [Prod.map, id_eq] using
        RegistrationNativeMldsaDynamicEagerContinuation.bound source setup checks wire route representation adversary
          selected tape challenge chosen initial ghost pool
          (fixed source setup selected tape challenge chosen ensureInit identityIndex serverKeyId ((some initial, ghost), pool) possible)
end BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerStartup.bound
