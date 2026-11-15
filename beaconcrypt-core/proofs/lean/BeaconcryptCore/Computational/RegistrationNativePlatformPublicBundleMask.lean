-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask
/-! The real stateful-writer bundle commutes with private scalar restoration, including failed writes and all signing effects. The public prekey is checked against the reached canonical roster, rather than assuming publication success. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBundleMask
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformPublicMask
open RegistrationNativePublicOwnerRestore (mask)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
variable {n : Nat} {I KemSK Auxiliary E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def after (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (oneTime : ScalarBytes) : RegistrationNativePlatformGenericBundle.M source Auxiliary m (RustM (Option (alloc.vec.Vec U8))) := do
  let published ← RegistrationNativePlatformBeaconPublication.begin
    (fun query => RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    (RegistrationNativePlatformGenericBundle.encoderWith writer) ⟨owner.pin.binding⟩
    (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
    RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
    let _ ← RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
    pure (.ok (some finished.encoded))

private theorem after_equivariant (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (oneTime : ScalarBytes) (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding) :
    Equivariant selected scalar publicPrekey (after (Auxiliary := Auxiliary) implementation writer setup index owner oneTime) := by
  unfold after
  apply bind_equivariant selected scalar publicPrekey _ _
    (RegistrationNativePlatformPublicPublicationMask.publication implementation writer setup index owner _ _ _ _ selected scalar publicPrekey)
  intro published
  cases published with
  | fail error | div => exact pure_equivariant selected scalar publicPrekey _
  | ok result => cases result with
    | Err previous => exact pure_equivariant selected scalar publicPrekey _
    | Ok finished =>
      apply bind_equivariant selected scalar publicPrekey
      · rw [RegistrationNativeBeaconFrontend.updatePhase, legacy_modify]
        apply current_equivariant selected scalar publicPrekey index
        intro current
        by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]
      · intro updated
        apply bind_equivariant selected scalar publicPrekey _ _ (legacy_lift selected scalar publicPrekey implementation _)
        intro advanced
        exact pure_equivariant selected scalar publicPrekey _

omit [LawfulMonad m] in
private theorem after_alter (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (oneTime : ScalarBytes) (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (valid : index = selected → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey) :
    after (Auxiliary := Auxiliary) implementation writer setup index (alter selected scalar publicPrekey index owner) oneTime =
      after implementation writer setup index owner oneTime := by
  by_cases chosen : index = selected
  · simp only [alter, chosen, ite_true]
    unfold after RegistrationNativeBeaconFrontend.inputs RegistrationNativeBeaconFrontend.outgoing
    simp only [valid chosen]
  · simp only [alter, chosen, ite_false]

private theorem bundle_program (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary) :
    ((RegistrationNativePlatformGenericBundle.bundle implementation setup source
      (RegistrationNativePlatformGenericBundle.encoderWith writer) index).run owners).run env =
    match owners[index]? with
    | none => pure ((.ok none, owners), env)
    | some owner => match owner.phase with
      | .fresh => ((RegistrationNativePlatformGenericBundle.liftLegacy implementation
          (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar) >>=
          after implementation writer setup index owner).run owners).run env
      | .freshWithCoins scalar => ((after implementation writer setup index owner scalar).run owners).run env
      | _ => pure ((.ok none, owners), env) := by
  simp only [RegistrationNativePlatformGenericBundle.bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases owners[index]? with
  | none => rfl
  | some owner =>
    cases phase : owner.phase <;> simp only [phase, after, StateT.run_bind]
    case fresh =>
      apply bind_congr
      rintro ⟨⟨oneTime, middleOwners⟩, middleEnv⟩
      apply bind_congr
      rintro ⟨⟨published, lastOwners⟩, lastEnv⟩
      cases published with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
    case freshWithCoins oneTime =>
      apply bind_congr
      rintro ⟨⟨published, lastOwners⟩, lastEnv⟩
      cases published with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
    all_goals rfl

attribute [local irreducible] after RegistrationNativeBeaconFrontend.sample

theorem bundle_mask (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index selected : Nat) (scalar : ScalarBytes)
    (publicPrekey : PeerEncoding) (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (valid : ∀ owner, owners[selected]? = some owner → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey) :
    Prod.map (Prod.map id (mask selected scalar publicPrekey)) id <$>
      ((RegistrationNativePlatformGenericBundle.bundle implementation setup source
        (RegistrationNativePlatformGenericBundle.encoderWith writer) index).run owners).run env =
      ((RegistrationNativePlatformGenericBundle.bundle implementation setup source
        (RegistrationNativePlatformGenericBundle.encoderWith writer) index).run (mask selected scalar publicPrekey owners)).run env := by
  rw [bundle_program, bundle_program, lookup]
  cases found : owners[index]? with
  | none => simp only [Option.map_none, map_pure, Prod.map_def, id_eq]
  | some owner =>
    simp only [Option.map_some]
    have phase : (alter selected scalar publicPrekey index owner).phase = owner.phase := by
      by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]
    have fixed : index = selected → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey := by
      intro chosen
      exact valid owner (chosen ▸ found)
    rw [phase]
    cases phaseRun : owner.phase <;> dsimp only
    case fresh =>
      have law := bind_equivariant selected scalar publicPrekey
        (RegistrationNativePlatformGenericBundle.liftLegacy implementation
          (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))
        (after (Auxiliary := Auxiliary) implementation writer setup index owner)
        (legacy_sample selected scalar publicPrekey implementation _)
        (fun oneTime => after_equivariant implementation writer setup index owner oneTime selected scalar publicPrekey)
      have continuation : after (Auxiliary := Auxiliary) implementation writer setup index (alter selected scalar publicPrekey index owner) =
          after implementation writer setup index owner := funext fun oneTime => after_alter implementation writer setup index owner oneTime selected scalar publicPrekey fixed
      rw [continuation]
      exact law owners env
    case freshWithCoins oneTime =>
      rw [after_alter implementation writer setup index owner oneTime selected scalar publicPrekey fixed]
      exact after_equivariant implementation writer setup index owner oneTime selected scalar publicPrekey owners env
    all_goals simp only [map_pure, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBundleMask

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBundleMask.bundle_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBundleMask.bundle_mask
