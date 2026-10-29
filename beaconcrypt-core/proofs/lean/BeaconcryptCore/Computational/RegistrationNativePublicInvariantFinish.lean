-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners

/-! Public finish never constructs a new pending capability. It retains the old owner on early failure or moves to aborted/established after consumption, independently of every root/material reply. Coherence is therefore preserved in the open reference client, before choosing its real or ideal root interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
open RegistrationNativeBeaconCoherence (PhaseCoherent)
open RegistrationNativePublicInvariantOwners (Coherent coherent_iff)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State) source

private def Keeps (work : M n KemSK source Value) : Prop :=
  ∀ owner env result, PhaseCoherent owner.phase → result ∈ support ((work.run owner).run env) →
    PhaseCoherent result.1.2.phase

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Value) := by
  intro owner env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid

private theorem bind_keeps (work : M n KemSK source Value) (next : Value → M n KemSK source Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owner env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle valid reached) continued

private theorem env_keeps (work : StateT (EnvState RegistrationServerRoleBackend.State) (OracleComp (Spec n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK source Value) := by
  intro owner env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid

private theorem get_keeps : Keeps (get : M n KemSK source (SelectedOwner source)) := by
  intro owner env result valid supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid

private theorem phase_keeps (phase : RegistrationNativeBeaconFrontend.Phase) (coherent : PhaseCoherent phase) :
    Keeps ((modify fun owner : SelectedOwner source => { owner with phase }) : M n KemSK source Unit) := by
  intro owner env result _valid supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact coherent

private theorem abort_keeps (owner : SelectedOwner source) :
    Keeps (RegistrationBeaconReferenceFinish.abort owner : M n KemSK source Unit) :=
  bind_keeps _ _ (env_keeps _) (fun _ => pure_keeps _)

private theorem abort_return_keeps (owner : SelectedOwner source) (value : Value) :
    Keeps (RegistrationBeaconReferenceFinish.abort owner *> pure value : M n KemSK source Value) :=
  bind_keeps _ _ (abort_keeps owner) (fun _ => pure_keeps _)

private theorem complete_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) :
    Keeps (RegistrationBeaconReferenceFinish.complete setup.source owner ready : M n KemSK source (RustM (Option Pqxdh.Bytes))) := by
  apply bind_keeps _ _ (env_keeps _)
  intro completed
  cases completed with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | Err error => exact abort_return_keeps owner _
    | Ok completed => exact bind_keeps _ _ (phase_keeps (.established completed) trivial) (fun _ => pure_keeps _)

private theorem after_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    Keeps (RegistrationBeaconReferenceNativeContinuation.afterPrepared setup.source owner result : M n KemSK source (RustM (Option Pqxdh.Bytes))) := by
  cases result with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | none => exact abort_return_keeps owner _
    | some ready => exact complete_keeps setup owner ready

private theorem root_phase_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Keeps (RegistrationBeaconReferenceNativePhase.phase setup owner oneTime authenticated : M n KemSK source (RustM (Option Pqxdh.Bytes))) :=
  bind_keeps _ _ (env_keeps _) (fun result => after_keeps setup owner result)

/-- Actual one-owner public finish preserves phase coherence on every open-oracle outcome. -/
theorem reference_coherent (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (valid : PhaseCoherent owner.phase) (supported : result ∈ support
      (((RegistrationBeaconReferenceFinish.finish (n := n) setup source packet).run owner).run env)) :
    PhaseCoherent result.1.2.phase := by
  rw [RegistrationBeaconReferenceNativeFinish.reference_factor] at supported
  have kept : Keeps (RegistrationBeaconReferenceNativeFinish.incoming (n := n) (KemSK := KemSK) setup source packet) := by
    apply bind_keeps _ _ get_keeps
    intro current
    cases phase : current.phase <;> dsimp only
    all_goals try { exact pure_keeps _ }
    case initSent pending oneTime =>
      cases moved : pending.aborted_state <;> dsimp only
      all_goals try { exact pure_keeps _ }
      case ok aborted =>
        apply bind_keeps _ _ (phase_keeps (.aborted aborted) trivial)
        intro _
        apply bind_keeps _ _ (env_keeps _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_return_keeps current _
        | ok result => cases result with
          | Err error => exact abort_return_keeps current _
          | Ok accepted => exact root_phase_keeps setup current oneTime accepted
  exact kept owner env result valid supported

private theorem write_coherent (roster : RegistrationNativePublicOwners.State source)
    (valid : Coherent roster) (index : Nat) (current : RegistrationNativePublicOwners.Owner source)
    (view : SelectedOwner source) (coherent : PhaseCoherent view.phase) :
    Coherent (roster.set index { current with view }) := by
  apply (coherent_iff _).mpr
  intro selected member
  rcases List.mem_or_eq_of_mem_set member with original | rfl
  · exact (coherent_iff roster).mp valid selected original
  · exact coherent

/-- Selected and ordinary roster finish retain all coherent pending capabilities without restricting their root/material services. -/
theorem finish_coherent (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (valid : Coherent roster) (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run roster).run env)) :
    Coherent result.1.2 := by
  cases found : roster[index]? with
  | none =>
      simp only [RegistrationNativePublicOwners.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | some owner =>
      cases scalarEq : owner.scalar <;>
        simp only [RegistrationNativePublicOwners.finish, StateT.run, found, scalarEq, support_map] at supported
      case none =>
        obtain ⟨reached, member, equal⟩ := supported
        have kept := reference_coherent setup packet owner.view env reached (valid index owner found) member
        cases equal
        simpa only [scalarEq] using write_coherent roster valid index owner reached.1.2 kept
      case some scalar =>
        obtain ⟨reached, member, equal⟩ := supported
        have kept := reference_coherent setup packet owner.view env reached (valid index owner found)
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member)
        cases equal
        simpa only [scalarEq] using write_coherent roster valid index owner reached.1.2 kept

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish.reference_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish.reference_coherent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish.finish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantFinish.finish_coherent
