-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect

/-! Actual Beacon metadata admission is independent of the opaque KEM word. The executable prepared record therefore retains the same raw pin, DH validity, assigned ID and populated AD, while evaluation restores only the private shared field used by the next root reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare
open PqxdhBeaconPhase2Preparation (Bytes)
open RegistrationNativeSecretWordBeaconCollect (Spec Input collect realize)
variable {I D K X Response : Type}
variable (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)

structure Prepared (Response : Type) where
  collected : Input Response
  metadata : PqxdhBeaconPhase2Shared.Metadata

def eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (pending : Prepared Response) :
    PqxdhPhase2DhMetadata.Prepared Response :=
  ⟨RegistrationNativeSecretWordBeaconCollect.eval candidate pending.collected, pending.metadata⟩

noncomputable def prepare (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Bytes) : OracleComp (Spec I D K X Response) (Option (Prepared Response)) := do
  let collected ← collect identity oneTime kem raw
  pure (collected.bind fun value =>
    (PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control value.plain).map fun metadata => ⟨value, metadata⟩)

/-- The actual entire optional preparation restores from the opaque-word program without altering metadata or any reached primitive effect. -/
theorem prepare_realization (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ (realize candidate) (PqxdhPhase2DhMetadata.prepare (completedBinding := completedBinding) (X := X) (Response := Response) control identity oneTime kem raw) =
      Option.map (eval candidate) <$> prepare (completedBinding := completedBinding) control identity oneTime kem raw := by
  simp only [PqxdhPhase2DhMetadata.prepare, prepare, simulateQ_bind,
    RegistrationNativeSecretWordBeaconCollect.collect_realization, bind_map_left, map_bind]
  apply bind_congr
  intro collected
  cases collected with
  | none => simp only [Option.map_none, Option.bind_none, simulateQ_pure, map_pure]
  | some value =>
      simp only [Option.map_some, Option.bind_some, simulateQ_pure, map_pure,
        RegistrationNativeSecretWordBeaconCollect.eval, RegistrationNativeSecretWordBeaconPrefix.admitted_setShared,
        Option.map_map, Function.comp_def, eval]

/-- Arbitrary subsequent stateful interpretation preserves the full reached environment in the concrete opaque-word preparation law. -/
theorem prepare_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec I D K X Response) m) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ (implementation ∘ₛ realize candidate)
      (PqxdhPhase2DhMetadata.prepare (completedBinding := completedBinding) (X := X) (Response := Response) control identity oneTime kem raw) =
      Option.map (eval candidate) <$> simulateQ implementation (prepare (completedBinding := completedBinding) control identity oneTime kem raw) := by
  rw [QueryImpl.simulateQ_compose, prepare_realization, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare.prepare_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare.prepare_realization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare.prepare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrepare.prepare_program
