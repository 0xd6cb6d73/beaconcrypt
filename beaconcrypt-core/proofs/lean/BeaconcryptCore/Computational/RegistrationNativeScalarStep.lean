-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarWaiting

/-! The optional selected constructor prefix composes with the adaptive induction. A refusal keeps the target waiting; a successful preparation reaches a literal total birth, after which the complete eager source is exactly ordinary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarStep
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeExperiment (State)
variable {n : Nat} {ι KemSK Value X : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem beacon_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : X) (before : State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (pure value : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State X)).run before = pure (value, before) := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  rfl

/-- The actual optional-prefix outcome preserves the complete adaptive scalar interchange, using the induction hypothesis only on still-waiting refusals. -/
theorem after_step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RustM (Option (RegistrationNativeBeaconFrontend.Prepared source)))
    (before : State n KemSK source) (chosen : before.beacons.length = selected)
    (next : RustM (Option Nat) → OracleComp TypedSpec Value)
    (waiting : ∀ reply (current : State n KemSK source), current.beacons.length ≤ selected →
      (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) (next reply)).run current =ᵈ
        (do let scalar ← PqxdhJointGapDh.sampleScalar
            (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) (next reply)).run current)) :
    (do let result ← (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarBirth.after setup source edPin keyId
            (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar) prepared)).run before
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) (next result.1)).run result.2) =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) prepared)).run before
          (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) (next result.1)).run result.2) := by
  cases prepared with
  | fail error =>
      simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
      exact waiting (.fail error) before (by omega)
  | div =>
      simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
      exact waiting .div before (by omega)
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
        exact waiting (.ok none) before (by omega)
    | some prepared =>
        simp only [RegistrationNativeScalarBirth.after, RegistrationNativeScalarEagerLocal.dummy, bind_assoc, pure_bind,
          RegistrationNativeScalarEagerLocal.sample_bind]
        have moved := RegistrationNativeScalarSource.scalar_eager setup checks representation created before
          (fun scalar current => do
            let result ← (RegistrationNativeExperiment.beacon setup checks representation created
              (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.identity scalar)).run current
            (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) (next result.1)).run result.2)
        refine moved.trans ?_
        apply _root_.EvalDistEq.bind_right
        intro scalar
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro drawn drawnSupport
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro born bornSupport
        rw [RegistrationNativeScalarOrdinary.done_program setup checks wire route representation created credential selected scalar
          (next born.1) born.2
          (RegistrationNativeScalarWaiting.birth_done setup checks representation created selected edPin keyId prepared scalar before chosen
            drawn drawnSupport born bornSupport)]

end BeaconcryptCore.Computational.RegistrationNativeScalarStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarStep.after_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarStep.after_step
