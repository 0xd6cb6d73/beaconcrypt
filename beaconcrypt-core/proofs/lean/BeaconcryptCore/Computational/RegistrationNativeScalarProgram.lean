-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarStep

/-! The selected generated scalar may be sampled before an arbitrary complete native program. The proof derives the still-waiting and already-created cases from actual source roster receipts, retaining failed creates and all original source effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeExperiment (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Complete adaptive typed source execution has the same full output and native poststate after moving the selected generated scalar into a private early draw. -/
theorem eager (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (work : OracleComp TypedSpec Value) (before : State n KemSK source)
    (short : before.beacons.length ≤ selected) :
    (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      by_cases target : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) ∧ before.beacons.length = selected
      · obtain ⟨edPin, mlPin, keyId, rfl, chosen⟩ := target
        change (do
            let result ← (RegistrationNativeExperiment.beacon setup checks representation created
              (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before
            (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) (next result.1)).run result.2) =ᵈ
          (do let scalar ← PqxdhJointGapDh.sampleScalar
              let result ← (RegistrationNativeExperiment.beacon setup checks representation created
                (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before
              (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) (next result.1)).run result.2)
        simp only [RegistrationNativeScalarBirth.source,
          RegistrationNativeScalarEagerLocal.target_source setup checks representation created source selected _ edPin mlPin keyId before chosen,
          bind_assoc]
        refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
          ((simulateQ PqxdhRecordLiftWorld.effects
            (RegistrationNativeScalarLeading.program source edPin mlPin keyId)).run before.server.world.world.1)
          (fun scalar earlier => do
            let result ← (RegistrationNativeExperiment.beacon setup checks representation created
              (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) earlier.1)).run
                (RegistrationBeaconReferenceNativeEffects.embed before earlier.2)
            (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar)
              (next result.1)).run result.2)).symm
        apply _root_.EvalDistEq.bind_right
        intro earlier
        exact RegistrationNativeScalarStep.after_step setup checks wire route representation created credential selected edPin keyId earlier.1
          (RegistrationBeaconReferenceNativeEffects.embed before earlier.2) chosen next ih
      · have away : RegistrationNativeScalarWaiting.Away selected query before := by
          intro edPin mlPin keyId actual same
          exact target ⟨edPin, mlPin, keyId, actual, same⟩
        simp only [RegistrationNativeScalarWaiting.away_handler setup checks wire route representation created credential selected _ query before away]
        refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
          ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)
          (fun scalar result => (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar)
            (next result.1)).run result.2)).symm
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro result supported
        exact ih result.1 result.2
          (RegistrationNativeScalarWaiting.away_short setup checks wire route representation created credential selected query before result short away supported)

end BeaconcryptCore.Computational.RegistrationNativeScalarProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarProgram.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarProgram.eager
