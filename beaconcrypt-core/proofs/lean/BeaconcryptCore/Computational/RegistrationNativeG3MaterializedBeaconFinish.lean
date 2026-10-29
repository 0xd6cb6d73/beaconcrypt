-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix

/-! The actual typed Beacon finish has the complete known108/materialized44 source equation. Mandatory authentication and root preparation use the derived common prefix equation; the sole material completion uses the exact finite first-open result. Terminal-before-parse consumption and every owner/environment/private failure state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG3MaterializedFrontend (ServiceSpec State)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {ι KemSK KeyState Auxiliary : Type} {base : OracleSpec ι}

/-- The original arbitrary-pin finish preserves its full native result and all reached owner/environment/key/receipt/World fields under materialized public references, with no caller-supplied source, cache or use premise. -/
theorem finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : EnvState Auxiliary) (before : State n KeyState) :
    (simulateQ (localImpl true setup.source writer sign seeds service fallback)
      (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env)).run before =
      (simulateQ (localImpl false setup.source writer sign seeds service fallback)
        (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env)).run before := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => rfl
  | freshWithCoins oneTime => rfl
  | established completed => rfl
  | aborted aborted => rfl
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure, simulateQ_pure]
      | div => simp only [moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [moved, simulateQ_bind, StateT.run_bind, ]
          rw [RegistrationNativeG3MaterializedBeaconPrefix.preparation_source setup source writer sign seeds service fallback packet owner env]
          apply bind_congr
          rintro ⟨⟨⟨prepared, current⟩, environment⟩, privateState⟩
          cases prepared with
          | fail error => rfl
          | div => rfl
          | ok prepared => cases prepared with
            | none => rfl
            | some ready =>
                exact RegistrationNativeG3MaterializedBeaconComplete.complete setup.source writer sign seeds service fallback
                  owner current ready environment privateState

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconFinish.finish
