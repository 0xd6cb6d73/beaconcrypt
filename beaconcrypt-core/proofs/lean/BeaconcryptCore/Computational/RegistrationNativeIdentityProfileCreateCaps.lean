-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The existing whole-adversary NativeInterface.Respects contract gives a whole ordinary joint-client identity creation bound. The literal secrecy ledger never inserts a create query, and actual native startup adds no indexed Beacon identity. This is a structural all-replies cap, rather than a final-event budget assertion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMainCreateCapsCore (Creates)
open PqxdhDeploymentInterface (FreshBounds Budget)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem wrap_create (bounds : FreshBounds) (full : Fin 14) :
    PqxdhDeploymentCompileSecrecy.wrapCost bounds (1 : Fin 12) full = if full = (1 : Fin 14) then 1 else 0 := by
  fin_cases full <;> rfl

theorem wrap_create_sum (bounds : FreshBounds) (budget : Budget) :
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds (1 : Fin 12) full * budget.cap full) = budget.create := by
  simp [wrap_create, PqxdhDeploymentInterface.Budget.cap]

/-- The literal raw native CE compiler transports its original create cap into the ordinary joint-source creation class. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : RegistrationNativeIdentityMain.State n KemSK source) :
    (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work before).IsQueryBoundP
      Creates budget.create := by
  rw [RegistrationNativeIdentityMain.run, isQueryBoundP_map_iff]
  apply RegistrationNativeIdentityMainCreateCaps.program_bound setup checks wire route representation created credential _ budget.create _ before
  simpa only [wrap_create_sum] using RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire
    created.server.server.metadata.sender bounds mode work budget bounded (1 : Fin 12)

/-- One fixed original native command budget for every public startup instance bounds the complete actual joint client before finite multi-user routing. -/
theorem client_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (budget : Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput)) :
    (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
      identityIndex serverKeyId bounds mode adversary event).IsQueryBoundP Creates budget.create := by
  unfold RegistrationNativeIdentityMainProfile.client
  rw [← Nat.zero_add budget.create]
  apply isQueryBoundP_bind (n := 0) (m := budget.create) (RegistrationNativeIdentityMainCreateCapsCore.coins_zero _)
  intro initialized _
  cases initialized with
  | none => exact isQueryBoundP_pure Creates false budget.create
  | some initial =>
      apply isQueryBoundP_bind (n := budget.create) (m := 0)
        (run_bound setup checks wire route representation initial.created initial.credential bounds mode
          (adversary initial.public) budget (bounded initial.public) (RegistrationNativeIdentityMainProfile.fromInitial initial))
      intro result _
      apply isQueryBoundP_bind (n := 0) (m := 0) (RegistrationNativeIdentityMainCreateCapsCore.emit_zero _)
      intro _ _
      exact isQueryBoundP_pure Creates _ 0

end BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.wrap_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.wrap_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.run_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps.client_bound
