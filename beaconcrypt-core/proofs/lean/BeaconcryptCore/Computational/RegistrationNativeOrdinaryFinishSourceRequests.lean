-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster

/-! The actual public finishing command does not add native record-request analysis markers to its mutable environment. Agreement retains that field by its actual callback footprint; raw material, authentication and lifecycle continuations lift their existing oracle programs without restoring a captured environment. This preservation law can be used by the initialized full-client invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State) source

private def Keeps (work : M n KemSK mlSource Value) : Prop :=
  ∀ owner env result, result ∈ support ((work.run owner).run env) →
    result.2.recordRequests = env.recordRequests

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK mlSource Value) := by
  intro owner env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : M n KemSK mlSource Value) (next : Value → M n KemSK mlSource Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owner env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owner env middle reached)

private theorem oracle_keeps (work : OracleComp (Spec n KemSK) Value) :
    Keeps (StateT.lift (StateT.lift work) : M n KemSK mlSource Value) := by
  intro owner env result supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, reached, equal⟩ := supported
  cases equal
  obtain ⟨reply, _member, same⟩ := reached
  cases same
  rfl

private theorem get_keeps : Keeps (get : M n KemSK mlSource (SelectedOwner mlSource)) := by
  intro owner env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem owner_keeps (update : SelectedOwner mlSource → SelectedOwner mlSource) :
    Keeps (modify update : M n KemSK mlSource Unit) := by
  intro owner env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem abort_keeps (owner : SelectedOwner mlSource) :
    Keeps (RegistrationBeaconReferenceFinish.abort owner : M n KemSK mlSource Unit) :=
  bind_keeps _ _ (oracle_keeps _) (fun _ => pure_keeps _)

private theorem abort_return_keeps (owner : SelectedOwner mlSource) (value : Value) :
    Keeps (RegistrationBeaconReferenceFinish.abort owner *> pure value : M n KemSK mlSource Value) :=
  bind_keeps _ _ (abort_keeps owner) (fun _ => pure_keeps _)

private theorem complete_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready) :
    Keeps (RegistrationBeaconReferenceFinish.complete source owner ready : M n KemSK mlSource (RustM (Option Pqxdh.Bytes))) := by
  apply bind_keeps _ _ (oracle_keeps _)
  intro completed
  cases completed with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | Err error => exact abort_return_keeps owner _
    | Ok result => exact bind_keeps _ _ (owner_keeps _) (fun _ => pure_keeps _)

private theorem after_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    Keeps (RegistrationBeaconReferenceNativeContinuation.afterPrepared source owner result : M n KemSK mlSource (RustM (Option Pqxdh.Bytes))) := by
  cases result with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | none => exact abort_return_keeps owner _
    | some ready => exact complete_keeps source owner ready

private theorem agreement_keeps (setup : Setup base KemSK) (owner : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Keeps (StateT.lift (RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated) :
      M n KemSK mlSource (RustM (Option RegistrationBeaconReferenceRoot.Ready))) := by
  intro current env result supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, reached, equal⟩ := supported
  cases equal
  exact RegistrationBeaconReferenceAgreementScope.agreement_keeps setup owner oneTime authenticated env returned.2 returned.1 reached

private theorem phase_keeps (setup : Setup base KemSK) (owner : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Keeps (RegistrationBeaconReferenceNativePhase.phase setup owner oneTime authenticated : M n KemSK mlSource (RustM (Option Pqxdh.Bytes))) :=
  bind_keeps _ _ (agreement_keeps setup owner oneTime authenticated) (fun result => after_keeps setup.source owner result)

/-- The actual complete one-owner public controller retains its input record-request analysis field on every supported outcome. -/
theorem reference_keeps (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner mlSource) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationBeaconReferenceFinish.finish (n := n) setup mlSource packet).run owner).run env)) :
    result.2.recordRequests = env.recordRequests := by
  rw [RegistrationBeaconReferenceNativeFinish.reference_factor] at supported
  have kept : Keeps (RegistrationBeaconReferenceNativeFinish.incoming (n := n) (KemSK := KemSK) setup mlSource packet) := by
    apply bind_keeps _ _ get_keeps
    intro current
    cases phase : current.phase <;> dsimp only
    all_goals try { exact pure_keeps _ }
    case initSent pending oneTime =>
      cases moved : pending.aborted_state <;> dsimp only
      all_goals try { exact pure_keeps _ }
      case ok aborted =>
        apply bind_keeps _ _ (owner_keeps _)
        intro _
        apply bind_keeps _ _ (oracle_keeps _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_return_keeps current _
        | ok result => cases result with
          | Err error => exact abort_return_keeps current _
          | Ok accepted => exact phase_keeps setup current oneTime accepted
  exact kept owner env result supported

/-- Selected and ordinary roster finishes both preserve the same environment field; materializing preparation does not change this initialized-state obligation. -/
theorem finish_keeps (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (roster : RegistrationNativePublicOwners.State mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State mlSource) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup mlSource index packet).run roster).run env)) :
    result.2.recordRequests = env.recordRequests := by
  cases found : roster[index]? with
  | none =>
      simp only [RegistrationNativePublicOwners.finish, StateT.run, found,
        mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      cases scalar : owner.scalar <;>
        simp only [RegistrationNativePublicOwners.finish, StateT.run, found, scalar, support_map] at supported
      case none =>
        obtain ⟨reached, member, equal⟩ := supported
        cases equal
        exact reference_keeps setup packet owner.view env reached member
      case some scalar =>
        obtain ⟨reached, member, equal⟩ := supported
        cases equal
        exact reference_keeps setup packet owner.view env reached
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member)

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests.reference_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests.reference_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests.finish_keeps
