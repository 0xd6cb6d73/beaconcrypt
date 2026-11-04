-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant

/-! The actual opaque table inherits the original initialized source execution's shared-cache receipt invariant. Source startup and complete adaptive execution are transported through the reached private table; the cache and native unsigned signing receipts are literally retained by credential restoration. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableCached
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaTableProgram (evaluate)
variable {Value : Type} {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

/-- Every actual table run after actual effectful initialization has the original native cached signing receipts, without a history-validity premise. -/
theorem run (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaProfile.run setup checks wire route representation initial.created initial.credential
        bounds mode work initial.state) started.2)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.1.2.2) := by
  obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex
    serverKeyId started startup initial member
  let actualInitial := RegistrationNativeMldsaMap.initial (restore source key started.2) initial
  have restoredStartup : some actualInitial ∈ support
      (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId) := by
    rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKeyId, support_map]
    refine ⟨started, startup, ?_⟩
    have selected : started.1 = some initial := member
    simp only [RegistrationNativeMldsaTableStart.restored, selected, Option.bind_some, server.1, Option.map_some]
    rfl
  have restoredRun := RegistrationNativeMldsaTableRun.run source setup checks wire route representation
    initial.created initial.credential key bounds mode work initial.state started.2 server owners
  have reached : RegistrationNativeMldsaTableRun.observeRun source key result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation actualInitial.created source
        actualInitial.credential bounds mode work actualInitial.state) := by
    dsimp only [actualInitial, RegistrationNativeMldsaMap.initial]
    rw [RegistrationNativeMldsaOpaque.restore_live source key started.2 initial.credential key server]
    rw [← restoredRun, support_map]
    exact ⟨result, supported, rfl⟩
  have valid := RegistrationNativeMldsaInvariant.initialized_run setup checks wire route representation
    ensureInit identityIndex serverKeyId actualInitial restoredStartup bounds mode work
    (RegistrationNativeMldsaTableRun.observeRun source key result) reached
  exact valid

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableCached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCached.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCached.run
