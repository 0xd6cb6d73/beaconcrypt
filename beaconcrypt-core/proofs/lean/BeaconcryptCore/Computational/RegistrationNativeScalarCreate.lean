-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEagerLocal

/-! A selected native constructor and every subsequent adaptive continuation have the same law after replacing its scalar by an early private sample. Actual failure probabilities, complete World state and original dummy-draw accounting are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Prepared sample appendBorn)
variable {n : Nat} {ι KemSK Value X : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem beacon_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (value : X)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (pure value : M n KemSK source RegistrationServerRoleBackend.State X)).run before = pure (value, before) := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  rfl

/-- Actual prefix refusal leaves the early scalar unused; successful preparation substitutes only the original counted draw's returned scalar. -/
theorem after_eager (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RustM (Option (Prepared source))) (before : RegistrationNativeExperiment.State n KemSK source)
    (next : RustM (Option Nat) → RegistrationNativeExperiment.State n KemSK source → ProbComp Value) :
    (do let result ← (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarBirth.after setup source edPin keyId (sample PqxdhJointGapDh.sampleScalar) prepared)).run before
        next result.1 result.2) =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) prepared)).run before
          next result.1 result.2) := by
  cases prepared with
  | fail error =>
      simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | div =>
      simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
        exact (OracleComp.EvalDistEq.bind_const _ _).symm
    | some prepared =>
        simp only [RegistrationNativeScalarBirth.after, RegistrationNativeScalarEagerLocal.dummy, bind_assoc, pure_bind,
          RegistrationNativeScalarEagerLocal.sample_bind]
        simpa only [bind_assoc] using
          (RegistrationNativeScalarSource.scalar_eager setup checks representation created before
            (fun scalar current => do
              let result ← (RegistrationNativeExperiment.beacon setup checks representation created
                (appendBorn setup source edPin keyId prepared.pin prepared.credentials prepared.identity scalar)).run current
              next result.1 result.2))

/-- The complete actual selected constructor commutes with its independent private challenge draw, with arbitrary full native continuation. -/
theorem create_eager (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (selected : Nat)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) (chosen : before.beacons.length = selected)
    (next : RustM (Option Nat) → RegistrationNativeExperiment.State n KemSK source → ProbComp Value) :
    (do let result ← (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before
        next result.1 result.2) =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before
          next result.1 result.2) := by
  simp only [RegistrationNativeScalarBirth.source,
    RegistrationNativeScalarEagerLocal.target_source setup checks representation created source selected _ edPin mlPin keyId before chosen,
    bind_assoc]
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap
    PqxdhJointGapDh.sampleScalar
    ((simulateQ PqxdhRecordLiftWorld.effects
      (RegistrationNativeScalarLeading.program source edPin mlPin keyId)).run before.server.world.world.1)
    (fun scalar earlier => do
      let result ← (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) earlier.1)).run
          (RegistrationBeaconReferenceNativeEffects.embed before earlier.2)
      next result.1 result.2)).symm
  apply _root_.EvalDistEq.bind_right
  intro earlier
  exact after_eager setup checks representation created edPin keyId earlier.1
    (RegistrationBeaconReferenceNativeEffects.embed before earlier.2) next

end BeaconcryptCore.Computational.RegistrationNativeScalarCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarCreate.after_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarCreate.after_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarCreate.create_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarCreate.create_eager
