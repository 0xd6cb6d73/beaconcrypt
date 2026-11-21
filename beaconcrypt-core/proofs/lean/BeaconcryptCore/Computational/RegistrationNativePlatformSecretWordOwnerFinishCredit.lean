-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCredit
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal)
variable {n : Nat} {I KemSK Auxiliary A B J : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source} {spec : OracleSpec J}
private abbrev M (spec : OracleSpec J) (Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp spec))
private def Keeps (work : M spec Auxiliary source A) : Prop :=
  ∀ owner env result, Terminal owner.phase → result ∈ support ((work.run owner).run env) → Terminal result.1.2.phase
private theorem pure_keeps (value : A) : Keeps (pure value : M spec Auxiliary source A) := by
  intro owner env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : M spec Auxiliary source A) (next : A → M spec Auxiliary source B)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owner env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle valid reached) continued
private theorem env_keeps (work : StateT (EnvState Auxiliary) (OracleComp spec) A) :
    Keeps (StateT.lift work : M spec Auxiliary source A) := by
  intro owner env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid
private theorem phase_keeps (phase : RegistrationNativeBeaconFrontend.Phase) (terminal : Terminal phase) :
    Keeps ((modify fun owner : SelectedOwner source => {owner with phase}) : M spec Auxiliary source Unit) := by
  intro owner env result _valid supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact terminal
private theorem abort_keeps (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp spec))
    (owner : SelectedOwner source) :
    Keeps (RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner : M spec Auxiliary source Unit) :=
  bind_keeps _ _ (env_keeps _) (fun _ => pure_keeps _)
private theorem after_keeps (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp spec))
    (owner : SelectedOwner source) (reply : RustM RegistrationNativePairedBeaconService.Result) :
    Keeps (RegistrationNativePlatformBeaconMaterialFrontend.after environment owner reply : M spec Auxiliary source _) := by
  have aborted (value : RustM (Option Pqxdh.Bytes)) :
      Keeps (RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner *> pure value : M spec Auxiliary source _) :=
    bind_keeps _ _ (abort_keeps environment owner) (fun _ => pure_keeps _)
  cases reply with
  | fail error | div => exact aborted _
  | ok selected => cases selected with
    | Err error => exact aborted _
    | Ok completed => exact bind_keeps _ _ (phase_keeps (.established completed) trivial) (fun _ => pure_keeps _)
private theorem program_keeps (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice :
      M (PqxdhRecordLiftInterface.EnvEffects n) Auxiliary source _) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.program
  apply bind_keeps _ _ (env_keeps _)
  intro _
  split
  · exact bind_keeps _ _ (env_keeps _) (fun _ => bind_keeps _ _ (env_keeps _) (fun result => after_keeps _ owner result))
  · exact bind_keeps _ _ (env_keeps _) (fun result => after_keeps _ owner result)
private theorem chosen_keeps (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationNativeSecretWordMessage.BeaconReady)
    (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer
      (RegistrationNativeSecretWordInterface.effect (KemSK := KemSK)) owner (ready.eval RegistrationNativeSecretWordMessage.zero) choice :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source _) := by
  intro current env result valid supported
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.chosen, StateT.run] at supported
  exact program_keeps crypto writer owner _ choice current env result valid
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported)
private theorem complete_keeps (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationNativeSecretWordMessage.BeaconReady) :
    Keeps (RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source _) := by
  unfold RegistrationNativePlatformSecretWordFinish.complete
  apply bind_keeps _ _ (env_keeps _)
  intro choice
  cases choice with
  | none => exact bind_keeps _ _ (abort_keeps _ owner) (fun _ => pure_keeps _)
  | some choice => exact chosen_keeps crypto writer owner ready choice
private theorem prepared_keeps (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (reply : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) :
    Keeps (RegistrationNativePlatformSecretWordFinish.afterPrepared crypto writer owner reply :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source _) := by
  cases reply with
  | fail error | div => exact bind_keeps _ _ (abort_keeps _ owner) (fun _ => pure_keeps _)
  | ok selected => cases selected with
    | none => exact bind_keeps _ _ (abort_keeps _ owner) (fun _ => pure_keeps _)
    | some ready => exact complete_keeps crypto writer owner ready
private theorem phase_keeps' (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Keeps (RegistrationNativePlatformSecretWordFinish.phase setup wire owner oneTime authenticated :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source _) :=
  bind_keeps _ _ (env_keeps _) (fun result => prepared_keeps _ _ owner result)
private noncomputable def afterAuthentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (core.result.Result registration.AuthenticatedResponse pqxdh.BeaconAborted)) :
    M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match reply with
  | .fail error => RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner *> pure (.fail error)
  | .div => RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner *> pure .div
  | .ok (.Err _) => RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner *> pure (.ok none)
  | .ok (.Ok accepted) => RegistrationNativePlatformSecretWordFinish.phase setup wire owner oneTime accepted
private theorem authenticated_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (core.result.Result registration.AuthenticatedResponse pqxdh.BeaconAborted)) :
    Keeps (afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire owner oneTime reply) := by
  cases reply with
  | fail error | div => exact bind_keeps _ _ (abort_keeps _ owner) (fun _ => pure_keeps _)
  | ok selected => cases selected with
    | Err error => exact bind_keeps _ _ (abort_keeps _ owner) (fun _ => pure_keeps _)
    | Ok authenticated => exact phase_keeps' setup wire owner oneTime authenticated
private noncomputable def suffix (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) : M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let authenticated ← StateT.lift (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
    (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
      (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))))
  afterAuthentication setup wire owner oneTime authenticated
private theorem suffix_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) : Keeps (suffix (n := n) (Auxiliary := Auxiliary) setup wire owner pending oneTime packet) :=
  bind_keeps _ _ (env_keeps _) (fun reply => authenticated_keeps setup wire owner oneTime reply)
attribute [local irreducible] RegistrationNativeSecretWordBeaconCompiler.agreement RegistrationResponseExecutor.begin
  RegistrationAuthenticationCompiler.callbacks
/-- The corrected incoming controller cannot revive an already terminal owner. -/
theorem finish_terminal (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (valid : Terminal owner.phase)
    (supported : result ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  cases ownerPhase : owner.phase <;> simp only [Terminal, ownerPhase] at valid
  all_goals simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind,
    ownerPhase, StateT.run_pure, mem_support_pure_iff] at supported
  all_goals cases supported; simp only [ownerPhase, Terminal]
/-- The actual pending move consumes the Beacon attempt before authentication, record opening or installation, including every failure. -/
theorem finish_consumes (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, sent, moved,
    StateT.run_modify] at supported
  change result ∈ support (((suffix setup wire owner pending oneTime packet).run {owner with phase := .aborted aborted}).run env) at supported
  exact suffix_keeps setup wire owner pending oneTime packet {owner with phase := .aborted aborted} env result trivial supported
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_consumes
