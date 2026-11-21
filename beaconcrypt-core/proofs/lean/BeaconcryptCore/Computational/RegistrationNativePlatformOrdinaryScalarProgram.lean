-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep
/-! Eager selected-prekey sampling preserves the complete actual corrected adaptive runtime law, including persistent external P. All other dynamic registration and ordinary callbacks remain literal; the waiting/past-birth cases use actual source roster receipts. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarProgram
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ordinary" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


local notation "eagerHandler" => RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer



/-- Full adaptive actual typed execution has the same joint result/native/P distribution after moving the selected scalar to a private early draw. -/
theorem eager (selected : Nat) (work : OracleComp TypedSpec Value) (before : State n KemSK source)
    (previous : Platform) (short : before.beacons.length ≤ selected) :
    (((simulateQ ordinary work).run before).run previous) =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          ((simulateQ (eagerHandler selected scalar) work).run before).run previous) := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases target : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) ∧ before.beacons.length = selected
    · obtain ⟨edPin, mlPin, keyId, rfl, chosen⟩ := target
      rw [RegistrationNativePlatformOrdinaryScalarStep.ordinary_create_run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer edPin mlPin keyId before previous]
      simp only [RegistrationNativePlatformOrdinaryScalarStep.eager_create_run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer selected, bind_map_left]
      simp only [RegistrationNativeScalarBirth.source,
        RegistrationNativeScalarEagerLocal.target_source setup checks representation created source selected _ edPin mlPin keyId before chosen, bind_assoc]
      refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
        ((simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativeScalarLeading.program source edPin mlPin keyId)).run before.server.world.world.1)
        (fun scalar earlier => do
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) earlier.1)).run
              (RegistrationBeaconReferenceNativeEffects.embed before earlier.2)
          ((simulateQ (eagerHandler selected scalar) (next result.1)).run result.2).run previous)).symm
      apply _root_.EvalDistEq.bind_right
      intro earlier
      exact RegistrationNativePlatformOrdinaryScalarStep.after_step setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer selected edPin keyId earlier.1
        (RegistrationBeaconReferenceNativeEffects.embed before earlier.2) previous chosen next ih
    · have away : RegistrationNativePlatformOrdinaryScalarWaiting.Away selected query before := by
        intro edPin mlPin keyId actual same
        exact target ⟨edPin, mlPin, keyId, actual, same⟩
      simp only [RegistrationNativePlatformOrdinaryScalarWaiting.away_handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer selected _ query before away]
      refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
        (((ordinary query).run before).run previous)
        (fun scalar result => ((simulateQ (eagerHandler selected scalar) (next result.1.1)).run result.1.2).run result.2)).symm
      apply OracleComp.EvalDistEq.bind_congr_of_support
      rintro ⟨⟨reply, current⟩, platform⟩ present
      exact ih reply current platform
        (RegistrationNativePlatformOrdinaryScalarWaiting.away_short setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selected query before current previous platform reply short away present)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarProgram.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarProgram.eager
