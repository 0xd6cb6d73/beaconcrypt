-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase

/-! The literal symbolic incoming controller consumes InitSent before optional response authentication. Root preparation, material opening and installation preserve a terminal phase on every later branch. This is a direct controller proof, independent of any old lifecycle-query cap or source-game substitution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal)
variable {n : Nat} {ι KemSK Auxiliary Value Next Index : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source} {spec : OracleSpec Index}

private abbrev M (spec : OracleSpec Index) (Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp spec))

private def Keeps (work : M spec Auxiliary source Value) : Prop :=
  ∀ owner env result, Terminal owner.phase → result ∈ support ((work.run owner).run env) → Terminal result.1.2.phase

private theorem pure_keeps (value : Value) : Keeps (pure value : M spec Auxiliary source Value) := by
  intro owner env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid

private theorem bind_keeps (work : M spec Auxiliary source Value) (next : Value → M spec Auxiliary source Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owner env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle valid reached) continued

private theorem env_keeps (work : StateT (EnvState Auxiliary) (OracleComp spec) Value) :
    Keeps (StateT.lift work : M spec Auxiliary source Value) := by
  intro owner env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid

private theorem phase_keeps (phase : RegistrationNativeBeaconFrontend.Phase) (terminal : Terminal phase) :
    Keeps ((modify fun owner : SelectedOwner source => { owner with phase }) : M spec Auxiliary source Unit) := by
  intro owner env result _valid supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact terminal

private theorem material_abort (owner : SelectedOwner source) :
    Keeps (RegistrationNativeSecretWordBeaconMaterial.abort owner : RegistrationNativeSecretWordBeaconMaterial.OwnerM n Auxiliary source Unit) :=
  bind_keeps _ _ (env_keeps _) (fun _ => pure_keeps _)

private theorem material_complete (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (owner : SelectedOwner source)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) :
    Keeps (RegistrationNativeSecretWordBeaconMaterial.complete hkdf owner ready : RegistrationNativeSecretWordBeaconMaterial.OwnerM n Auxiliary source _) := by
  apply bind_keeps _ _ (env_keeps _)
  intro completed
  have aborted (value : RustM (Option Pqxdh.Bytes)) :
      Keeps (RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure value : RegistrationNativeSecretWordBeaconMaterial.OwnerM n Auxiliary source _) :=
    bind_keeps _ _ (material_abort owner) (fun _ => pure_keeps _)
  cases completed with
  | fail error | div => exact aborted _
  | ok reply => cases reply with
    | Err error => exact aborted _
    | Ok completed => exact bind_keeps _ _ (phase_keeps (.established completed) trivial) (fun _ => pure_keeps _)

private theorem complete_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) :
    Keeps (RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source _) := by
  intro current env result valid supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordInterface.paired _ supported
  exact material_complete setup.source owner ready current env result valid original

private theorem abort_keeps (owner : SelectedOwner source) :
    Keeps (RegistrationNativeSecretWordBeaconCompiler.abort owner :
      M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source Unit) :=
  bind_keeps _ _ (env_keeps _) (fun _ => pure_keeps _)

private noncomputable def afterPrepared (setup : Setup base KemSK) (owner : SelectedOwner source)
    (prepared : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) :
    M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match prepared with
  | .fail error => RegistrationNativeSecretWordBeaconCompiler.abort owner *> pure (.fail error)
  | .div => RegistrationNativeSecretWordBeaconCompiler.abort owner *> pure .div
  | .ok none => RegistrationNativeSecretWordBeaconCompiler.abort owner *> pure (.ok none)
  | .ok (some ready) => RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready

private theorem after_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (prepared : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) :
    Keeps (afterPrepared (n := n) (Auxiliary := Auxiliary) setup owner prepared) := by
  cases prepared with
  | fail error | div => exact bind_keeps _ _ (abort_keeps owner) (fun _ => pure_keeps _)
  | ok reply => cases reply with
    | none => exact bind_keeps _ _ (abort_keeps owner) (fun _ => pure_keeps _)
    | some ready => exact complete_keeps setup owner ready

private noncomputable def preparationAfter (setup : Setup base KemSK) (owner : SelectedOwner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    M (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Auxiliary source (RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) := do
  let accepted ← StateT.lift (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
    (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
      (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))
  match accepted with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok authenticated) => StateT.lift (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)

private theorem preparation_keeps (setup : Setup base KemSK) (owner : SelectedOwner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    Keeps (preparationAfter (n := n) (Auxiliary := Auxiliary) setup owner pending oneTime packet) := by
  apply bind_keeps _ _ (env_keeps _)
  intro accepted
  cases accepted with
  | fail error | div => exact pure_keeps _
  | ok reply => cases reply with
    | Err error => exact pure_keeps _
    | Ok authenticated => exact env_keeps _

attribute [local irreducible] RegistrationNativeSecretWordBeaconCompiler.agreement
  RegistrationResponseExecutor.begin RegistrationAuthenticationCompiler.callbacks

private theorem preparation_consumes (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : (RustM (Option RegistrationNativeSecretWordMessage.BeaconReady) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finishPreparation (n := n) setup source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind,
    StateT.run_get, pure_bind, sent, moved, StateT.run_set] at supported
  change result ∈ support (((preparationAfter setup owner pending oneTime packet).run { owner with phase := .aborted aborted }).run env) at supported
  exact preparation_keeps setup owner pending oneTime packet { owner with phase := .aborted aborted } env result trivial supported

/-- An already terminal actual symbolic owner never returns to InitSent through an incoming command. -/
theorem finish_terminal (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (valid : Terminal owner.phase)
    (supported : result ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  cases phase : owner.phase <;> simp only [phase, Terminal] at valid
  all_goals
    simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get,
      pure_bind, phase, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    simp only [phase, Terminal]

/-- Passing the actual aborted-state move consumes the role before optional packet admission, including malformed None and all later failures. -/
theorem finish_consumes (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run env)) :
    Terminal result.1.2.phase := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get,
    pure_bind, sent, moved, mem_support_bind_iff] at supported
  obtain ⟨middle, prepared, continued⟩ := supported
  have terminal := preparation_consumes setup packet owner env pending oneTime aborted sent moved middle prepared
  exact after_keeps setup owner middle.1.1 middle.1.2 middle.2 result terminal continued

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish.finish_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish.finish_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish.finish_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish.finish_consumes
