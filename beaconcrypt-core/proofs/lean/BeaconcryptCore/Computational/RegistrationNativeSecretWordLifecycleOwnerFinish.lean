-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish

/-! Actual selected-owner finish consumes InitSent before parsing or authenticating a response. Every subsequent native root/open/install continuation retains a terminal phase. Existing terminal owners reject without restoring InitSent; optional failures keep their actual reached state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State) source

private def Keeps (work : M n KemSK source Value) : Prop :=
  ∀ owner env result, Terminal owner.phase → result ∈ support ((work.run owner).run env) →
    Terminal result.1.2.phase

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

private theorem phase_keeps (phase : RegistrationNativeBeaconFrontend.Phase) (terminal : Terminal phase) :
    Keeps ((modify fun owner : SelectedOwner source => { owner with phase }) : M n KemSK source Unit) := by
  intro owner env result _valid supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact terminal

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

private noncomputable def afterAuthentication (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (owner : SelectedOwner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) : M n KemSK source (RustM (Option Pqxdh.Bytes)) := do
  let authenticated ← StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.effect
    (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
      (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))))
  match authenticated with
  | .fail error => RegistrationBeaconReferenceFinish.abort owner *> pure (.fail error)
  | .div => RegistrationBeaconReferenceFinish.abort owner *> pure .div
  | .ok (.Err _) => RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none)
  | .ok (.Ok accepted) => RegistrationBeaconReferenceNativePhase.phase setup owner oneTime accepted

private theorem after_keeps_terminal (setup : Setup base KemSK) (owner : SelectedOwner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Keeps (afterAuthentication (n := n) setup source owner pending oneTime packet) := by
  apply bind_keeps _ _ (env_keeps _)
  intro authenticated
  cases authenticated with
  | fail error | div => exact abort_return_keeps owner _
  | ok result => cases result with
    | Err error => exact abort_return_keeps owner _
    | Ok accepted => exact root_phase_keeps setup owner oneTime accepted

/-- Every finish from an already terminal actual owner remains terminal on all returned branches. -/
theorem reference_terminal (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (valid : Terminal owner.phase) (supported : result ∈ support
      (((RegistrationBeaconReferenceFinish.finish (n := n) setup source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
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
        exact bind_keeps _ _ (phase_keeps (.aborted aborted) trivial) (fun _ =>
          after_keeps_terminal setup current pending oneTime packet)
  exact kept owner env result valid supported

/-- Passing the native aborted-state move irrevocably consumes InitSent before optional packet admission, including malformed None and every later crypto/open/install failure. -/
theorem reference_consumes (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationBeaconReferenceFinish.finish (n := n) setup source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  rw [RegistrationBeaconReferenceNativeFinish.reference_factor] at supported
  simp only [RegistrationBeaconReferenceNativeFinish.incoming, StateT.run_bind, StateT.run_get,
    pure_bind, sent, moved, StateT.run_modify] at supported
  exact (after_keeps_terminal setup owner pending oneTime packet)
    { owner with phase := .aborted aborted } env result trivial supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish.reference_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish.reference_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish.reference_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish.reference_consumes
