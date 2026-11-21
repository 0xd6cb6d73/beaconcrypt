-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicScalarLaws

/-! Actual outgoing publication does not read the prekey scalar. Its complete signature, receipt, pending-state and World callbacks commute with reconstruction of that single private coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicBundleScalar
open RegistrationNativeBeaconFrontend
open RegistrationNativePublicScalarMap (Equivariant alter change)
open RegistrationNativePublicScalarLaws
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem outgoing_equivariant (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Equivariant selected scalar (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_equivariant selected scalar _
  · exact pure_equivariant selected scalar _
  · simp only [outgoing]
    split
    · exact bind_equivariant selected scalar _ _ (log_equivariant selected scalar index _ _) (fun _ => pure_equivariant selected scalar _)
    · exact pure_equivariant selected scalar _

noncomputable def after (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      updatePhase index (.initSent finished.pending oneTime)
      let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem after_equivariant (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Equivariant selected scalar (after (n := n) (Auxiliary := Auxiliary) setup source wire index owner oneTime) := by
  unfold after
  apply bind_equivariant selected scalar _ _ (program_equivariant selected scalar _ (outgoing_equivariant setup source index owner selected scalar) _)
  intro published
  cases published with
  | fail error | div => exact pure_equivariant selected scalar _
  | ok result => cases result with
    | Err previous => exact pure_equivariant selected scalar _
    | Ok finished => exact bind_equivariant selected scalar _ _ (phase_equivariant selected scalar index _) (fun _ =>
        bind_equivariant selected scalar _ _ (lift_equivariant selected scalar _) (fun _ => pure_equivariant selected scalar _))

private theorem after_alter (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) :
    after (n := n) (Auxiliary := Auxiliary) setup source wire index (alter selected scalar index owner) oneTime =
      after setup source wire index owner oneTime := by
  by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]
  rfl

private theorem bundle_program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owners : State source) (env : EnvState Auxiliary) :
    ((bundle (n := n) setup source wire index).run owners).run env =
      match owners[index]? with
      | none => pure ((.ok none, owners), env)
      | some owner => match owner.phase with
        | .fresh => ((sample PqxdhJointGapDh.sampleScalar >>= after setup source wire index owner).run owners).run env
        | .freshWithCoins scalar => ((after setup source wire index owner scalar).run owners).run env
        | _ => pure ((.ok none, owners), env) := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases owners[index]? with
  | none => rfl
  | some owner => cases phase : owner.phase <;> simp only [phase] <;> rfl

attribute [local irreducible] after RegistrationNativeBeaconFrontend.sample

/-- Every successful or failed actual native bundle commutes with selected scalar restoration. -/
theorem bundle_scalar (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Equivariant selected scalar (bundle (n := n) (Auxiliary := Auxiliary) setup source wire index) := by
  intro owners env
  rw [bundle_program, bundle_program, RegistrationNativePublicScalarMap.lookup]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [Option.map_some]
      have phase : (alter selected scalar index owner).phase = owner.phase := by
        by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]
      rw [phase]
      cases phaseRun : owner.phase <;> dsimp only
      case fresh =>
          have law := bind_equivariant selected scalar (sample PqxdhJointGapDh.sampleScalar)
            (after (n := n) (Auxiliary := Auxiliary) setup source wire index owner)
            (sample_equivariant selected scalar _) (fun oneTime => after_equivariant setup source wire index owner oneTime selected scalar)
          have continuation : after (n := n) (Auxiliary := Auxiliary) setup source wire index (alter selected scalar index owner) =
              after setup source wire index owner := funext fun oneTime => after_alter setup source wire index owner oneTime selected scalar
          rw [continuation]
          exact law owners env
      case freshWithCoins oneTime =>
          rw [after_alter]
          exact after_equivariant setup source wire index owner oneTime selected scalar owners env
      all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePublicBundleScalar
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicBundleScalar.bundle_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicBundleScalar.bundle_scalar
