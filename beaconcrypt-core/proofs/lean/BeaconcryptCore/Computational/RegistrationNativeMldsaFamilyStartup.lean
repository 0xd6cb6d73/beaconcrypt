-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover
import BeaconcryptCore.Computational.RegistrationNativeMldsaStartupOrdinal

/-! The finite generation family starts at the actual effectful native constructor and first ML generation attempt. Its coordinate laws retain every failed startup prefix; successful startup derives simultaneous row/live/cache provenance and the actual initial attempt count. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaGhostFamily (Family)
open PqxdhServerAuthExperiment (Setup)
variable {n cap : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKid : Std.U64)

noncomputable def start : ProbComp ((Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Family cap) × Pool source) :=
  RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaGhostFamily.run source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) (fun _ => {})) {}

/-- Erasing the simultaneous public ghosts retains actual complete source startup, including optional failure and true primitive counts. -/
theorem erase : (fun result => (result.1.1, result.2)) <$> start (n := n) (cap := cap) source setup ensureInit identityIndex serverKid =
    RegistrationNativeMldsaTableProgram.evaluate source (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {} := by
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program {})
    (RegistrationNativeMldsaGhostFamily.erase source
      (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKid) (fun _ : Fin cap => {}))
  simpa only [start, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] using same

/-- Each selected coordinate has the literal original single-ordinal effectful startup distribution. -/
theorem coordinate (index : Fin cap) :
    (fun result => ((result.1.1, result.1.2 index), result.2)) <$> start (n := n) source setup ensureInit identityIndex serverKid =
      RegistrationNativeMldsaTableProgram.evaluate source
        (RegistrationNativeMldsaGenerationGhost.run source index.val
          (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {}) {} := by
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program {})
    (RegistrationNativeMldsaGhostFamily.coordinate source index
      (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKid) (fun _ => {}))
  simpa only [start, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] using same

/-- Successful actual startup derives every simultaneous protected-cut invariant and counts its initial Server generation as attempt zero. -/
theorem initialized (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (ghosts : Family cap) (pool : Pool source)
    (supported : ((some initial, ghosts), pool) ∈ support (start source setup ensureInit identityIndex serverKid)) :
    ∃ fallback, RegistrationNativeMldsaFamilyCover.Safe source initial.credential fallback (initial.state, (ghosts, pool)) ∧ pool.attempts = 1 := by
  have original : (some initial, pool) ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {}) := by
    rw [← erase (n := n) (cap := cap) source setup ensureInit identityIndex serverKid, support_map]
    exact ⟨((some initial, ghosts), pool), supported, rfl⟩
  obtain ⟨fallback, good⟩ := RegistrationNativeMldsaProtectedInvariant.initialized source setup ensureInit identityIndex serverKid
    (some initial, pool) original initial rfl
  have attempts := RegistrationNativeMldsaStartupOrdinal.server_ordinal source setup ensureInit identityIndex serverKid
    (some initial, pool) original initial rfl
  refine ⟨fallback, ⟨good, ?_⟩, attempts.2.2⟩
  intro index
  have chosen : ((some initial, ghosts index), pool) ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaGenerationGhost.run source index.val
        (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {}) {}) := by
    rw [← coordinate (n := n) source setup ensureInit identityIndex serverKid index, support_map]
    exact ⟨((some initial, ghosts), pool), supported, rfl⟩
  apply RegistrationNativeMldsaGhostRows.program_safe source index.val
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) (some initial, (ghosts index, pool))
  rw [RegistrationNativeMldsaGhostRows.source_program, support_map]
  exact ⟨((some initial, ghosts index), pool), chosen, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup.initialized
