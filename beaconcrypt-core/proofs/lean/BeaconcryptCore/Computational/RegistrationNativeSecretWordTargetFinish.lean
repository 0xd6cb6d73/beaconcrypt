-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication

/-! The actual symbolic incoming controller only changes an owner's lifecycle phase. Its retained KEM handle and public key survive authentication rejection, failed preparation, arbitrary material replies, raw opening and installation failures. Both ordinary message translation and the selected owner preserve the same roster metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationNativeSecretWordTargetPublication (key)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private abbrev OwnerM (Value : Type) := StateT (SelectedOwner source)
  (StateT (EnvState Auxiliary) (OracleComp (LocalSpec n KemSK))) Value

private def Keys (owner : SelectedOwner source) := (owner.kemHandle, owner.kemPublic)

private def Keeps (work : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) Value) : Prop :=
  ∀ owner env result, result ∈ support ((work.run owner).run env) → Keys result.1.2 = Keys owner

private theorem pure_keeps (value : Value) : Keeps (pure value : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) Value) := by
  intro owner env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) Value)
    (next : Value → OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) Next)
    (first : Keeps work) (later : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owner env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first owner env middle reached)

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (LocalSpec n KemSK)) Value) :
    Keeps (StateT.lift work : OwnerM (source := source) Value) := by
  intro owner env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, equal⟩ := supported
  cases equal
  rfl

private theorem get_keeps : Keeps (get : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (SelectedOwner source)) := by
  intro owner env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem modify_keeps (phase : RegistrationNativeBeaconFrontend.Phase) :
    Keeps (modify (fun current => { current with phase }) : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) Unit) := by
  intro owner env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private def responseOption (packet : Option registration.ResponsePacket) : core.option.Option registration.ResponsePacket :=
  match packet with | none => .None | some packet => .Some packet

private theorem preparation_keeps (setup : Setup base KemSK) (packet : Option registration.ResponsePacket) :
    Keeps (RegistrationNativeSecretWordBeaconCompiler.finishPreparation (n := n) (Auxiliary := Auxiliary) setup source packet) := by
  intro owner env result supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind,
    StateT.run_get, pure_bind] at supported
  cases phase : owner.phase <;> simp only [phase] at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl }
  rename_i pending oneTime
  cases aborted : pending.aborted_state with
  | fail error | div =>
      simp only [aborted, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok control =>
      simp only [aborted, StateT.run_bind, StateT.run_set, pure_bind] at supported
      let later : OwnerM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
          (RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) := do
        let checked ← StateT.lift (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
          (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
            (RegistrationResponseExecutor.begin pending (responseOption packet)))))
        match checked with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok (.Err _) => pure (.ok none)
        | .ok (.Ok authenticated) => StateT.lift (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)
      have valid : Keeps later := by
        apply bind_keeps _ _ (lift_keeps _)
        intro checked
        cases checked with
        | fail error | div => exact pure_keeps _
        | ok checked => cases checked with
          | Err error => exact pure_keeps _
          | Ok authenticated => exact lift_keeps _
      apply valid { owner with phase := .aborted control } env result
      simp only [later, responseOption, StateT.run_bind]
      convert supported using 1; rfl

private theorem abort_keeps (owner : SelectedOwner source) :
    Keeps (RegistrationNativeSecretWordBeaconCompiler.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _)

private theorem material_abort_key (owner before : SelectedOwner source) (value : Value)
    (env : EnvState Auxiliary) (result : (Value × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativeSecretWordBeaconMaterial.abort (n := n) owner *> pure value).run before).run env)) :
    Keys result.1.2 = Keys before := by
  change result ∈ support ((fun _ => ((value, before), env)) <$>
    (RegistrationNativeSecretWordBeaconMaterial.effect (.inr (.advanceOwner owner.worldOwner .aborted)))) at supported
  rw [support_map] at supported
  obtain ⟨reply, _, equal⟩ := supported
  cases equal
  rfl

private theorem material_keeps (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner source) (ready : RegistrationNativeSecretWordMessage.BeaconReady) :
    Keeps (RegistrationNativeSecretWordBeaconCompiler.complete (n := n) (Auxiliary := Auxiliary) (KemSK := KemSK) hkdf owner ready) := by
  intro current env result supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.complete, StateT.run] at supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  have law : ∀ (before : SelectedOwner source) (initial : EnvState Auxiliary) reached,
      reached ∈ support (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) hkdf owner ready).run before).run initial) →
        Keys reached.1.2 = Keys before := by
    intro before initial reached member
    simp only [RegistrationNativeSecretWordBeaconMaterial.complete, StateT.run_bind, StateT.run_lift,
      bind_pure_comp, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨finished, _, tail⟩ := member
    cases finished with
    | fail error | div => exact material_abort_key owner before _ initial reached tail
    | ok finished => cases finished with
      | Err error => exact material_abort_key owner before _ initial reached tail
      | Ok completed =>
          cases tail
          rfl
  exact law current env result native

/-- The complete actual symbolic incoming controller preserves its retained KEM pair metadata on every branch. -/
theorem finish_key (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run env)) :
    (result.1.2.kemHandle, result.1.2.kemPublic) = (owner.kemHandle, owner.kemPublic) := by
  have law : Keeps (RegistrationNativeSecretWordBeaconCompiler.finish (n := n) (Auxiliary := Auxiliary) setup source packet) := by
    unfold RegistrationNativeSecretWordBeaconCompiler.finish
    apply bind_keeps _ _ get_keeps
    intro current
    cases phase : current.phase <;> dsimp only
    all_goals try exact pure_keeps _
    rename_i pending oneTime
    cases pending.aborted_state <;> try exact pure_keeps _
    apply bind_keeps _ _ (preparation_keeps setup packet)
    intro prepared
    cases prepared with
    | fail error | div => exact bind_keeps _ _ (abort_keeps current) (fun _ => pure_keeps _)
    | ok prepared => cases prepared with
      | none => exact bind_keeps _ _ (abort_keeps current) (fun _ => pure_keeps _)
      | some ready => exact material_keeps setup.source current ready
  exact law owner env result supported

/-- Both selected and ordinary incoming wrappers preserve every roster handle and PQ key. -/
theorem finish_keys (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env)) :
    result.1.2.map key = owners.map key := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      simp only [found, support_map] at supported
      obtain ⟨middle, reached, equal⟩ := supported
      have original : middle ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner.view).run env) := by
        cases choice : owner.scalar with
        | none =>
            simp only [choice] at reached
            convert reached using 1
            rfl
        | some scalar =>
            simp only [choice] at reached
            exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
      have kept := finish_key setup packet owner.view env middle original
      cases equal
      rw [List.map_set]
      change (owners.map key).set index (middle.1.2.kemHandle, middle.1.2.kemPublic) = _
      rw [kept]
      have present : (owners.map key)[index]? = some (key owner) := by simp only [List.getElem?_map, found, Option.map_some]
      obtain ⟨below, current⟩ := List.getElem?_eq_some_iff.mp present
      change (owners.map key).set index (key owner) = _
      rw [← current]
      exact List.set_getElem_self below

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish.finish_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish.finish_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish.finish_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish.finish_keys
