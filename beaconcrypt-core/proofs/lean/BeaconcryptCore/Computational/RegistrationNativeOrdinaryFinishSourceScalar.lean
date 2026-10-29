-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFinish

/-! The real native one-owner finishing controller changes lifecycle state while retaining its private prekey scalar. This is proved from the actual mutable-owner AST, including authentication failure, abort and failed installation, before restoring any public owner view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Phase Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeOwner (M)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private def Keeps (work : M n KemSK Auxiliary mlSource Value) : Prop :=
  ∀ before env result, result ∈ support ((work.run before).run env) →
    result.1.2.prekeyScalar = before.prekeyScalar

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK Auxiliary mlSource Value) := by
  intro before env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : M n KemSK Auxiliary mlSource Value)
    (next : Value → M n KemSK Auxiliary mlSource Next) (first : Keeps work)
    (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before env middle reached)

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK Auxiliary mlSource Value) := by
  intro before env result supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨reached, _member, equal⟩ := supported
  cases equal
  rfl

private theorem phase_keeps (phase : Phase) :
    Keeps ((modify fun current : Owner mlSource => { current with phase := phase }) : M n KemSK Auxiliary mlSource Unit) := by
  intro before env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem abort_keeps (owner : Owner mlSource) :
    Keeps (RegistrationBeaconReferenceNativeOwner.abort owner : M n KemSK Auxiliary mlSource Unit) :=
  bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _)

private theorem abort_return_keeps (owner : Owner mlSource) (value : Value) :
    Keeps (RegistrationBeaconReferenceNativeOwner.abort owner *> pure value : M n KemSK Auxiliary mlSource Value) :=
  bind_keeps _ _ (abort_keeps owner) (fun _ => pure_keeps _)

private theorem after_keeps (owner : Owner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    Keeps (RegistrationBeaconReferenceNativeOwner.after owner result :
      M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))) := by
  cases result with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | Err error => exact abort_return_keeps owner _
    | Ok completed =>
        apply bind_keeps _ _ (lift_keeps _)
        intro installed
        cases installed with
        | false => exact abort_return_keeps owner _
        | true => exact bind_keeps _ _ (phase_keeps _) (fun _ => pure_keeps _)

/-- Every actual native finish result retains its input scalar, with no assumption on oracle replies or successful completion. -/
theorem finish_scalar (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner mlSource) (packet : Option registration.ResponsePacket) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × Owner mlSource) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationBeaconReferenceNativeOwner.finish (n := n) setup mlSource wire packet).run owner).run env)) :
    result.1.2.prekeyScalar = owner.prekeyScalar := by
  simp only [RegistrationBeaconReferenceNativeOwner.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase <;> simp only [phase] at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl }
  case initSent pending oneTime =>
    cases moved : pending.aborted_state <;> simp only [moved] at supported
    all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl }
    case ok aborted =>
      refine (bind_keeps _ _ (phase_keeps (.aborted aborted)) ?_) owner env result supported
      intro _
      apply bind_keeps _ _ (lift_keeps _)
      intro authenticated
      cases authenticated with
      | fail error | div => exact abort_return_keeps owner _
      | ok result => cases result with
        | Err error => exact abort_return_keeps owner _
        | Ok accepted =>
            apply bind_keeps _ _ (lift_keeps _)
            intro agreed
            cases agreed with
            | fail error | div => exact abort_return_keeps owner _
            | ok effect => cases effect with
              | BeaconComplete completed =>
                  exact bind_keeps _ _ (lift_keeps _) (fun opened => after_keeps owner opened)
              | _ => exact abort_return_keeps owner _

/-- Restoring the erased scalar from the actual input reconstructs the entire returned owner, rather than only its KEM fields. -/
theorem finish_restore (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner mlSource) (packet : Option registration.ResponsePacket) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × Owner mlSource) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationBeaconReferenceNativeOwner.finish (n := n) setup mlSource wire packet).run owner).run env)) :
    RegistrationBeaconReferenceCompiler.restoreOwner owner.prekeyScalar
      (RegistrationBeaconReferenceCompiler.eraseOwner result.1.2) = result.1.2 := by
  rw [← finish_scalar setup wire owner packet env result supported]
  exact RegistrationBeaconReferenceCompiler.restore_erase _

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar.finish_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar.finish_scalar
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar.finish_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceScalar.finish_restore
