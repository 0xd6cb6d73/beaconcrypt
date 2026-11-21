-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyCover
import BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyStartup

/-! The unchanged actual constructor and initial ML generation initialize the corrected finite-family invariant. The arbitrary initial external state is retained literally; the stored pin's full ML public key is derived from the actual source startup configuration. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyStartup
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaGhostFamily (Family)
open PqxdhServerAuthExperiment (Setup)
variable {n cap : Nat} {ι KemSK Platform : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKid : Std.U64)

/-- Actual successful source startup derives all simultaneous corrected native/platform invariants and the initial generation attempt count. -/
theorem initialized (previous : Platform)
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (ghosts : Family cap) (pool : Pool source)
    (supported : ((some initial, ghosts), pool) ∈ support (RegistrationNativeMldsaFamilyStartup.start source setup ensureInit identityIndex serverKid)) :
    ∃ fallback, RegistrationNativePlatformOrdinaryMldsaFamilyCover.Safe source initial.credential fallback ((initial.state, previous), (ghosts, pool)) ∧ pool.attempts = 1 := by
  obtain ⟨fallback, good, attempts⟩ := RegistrationNativeMldsaFamilyStartup.initialized source setup ensureInit identityIndex serverKid initial ghosts pool supported
  have original : (some initial, pool) ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKid) {}) := by
    rw [← RegistrationNativeMldsaFamilyStartup.erase (n := n) (cap := cap) source setup ensureInit identityIndex serverKid, support_map]
    exact ⟨((some initial, ghosts), pool), supported, rfl⟩
  exact ⟨fallback, ⟨good.1, (RegistrationNativePlatformServerPinTrace.table_initialized setup source ensureInit identityIndex serverKid (some initial, pool) original initial rfl).2,
    good.2⟩, attempts⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyStartup.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyStartup.initialized
