-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative

/-! Root-free native callbacks do not read the private reference memo. Resetting only that memo commutes with their complete execution; the World, generated-key pool and chronological signing receipts are retained in the comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev Frame (n : Nat) (KemSK : Type) :=
  PqxdhRecordLiftWorld.State n × PqxdhLiveKemBirth.Pool KemSK × List RegistrationSigningShared.Receipt

def drop (before : Private n KemSK) : Frame n KemSK := (before.world, before.pool, before.extra.2)

def put (memo : RegistrationNativeReferenceInterpreter.State) (before : Frame n KemSK) : Private n KemSK :=
  ⟨before.1, before.2.1, (memo, before.2.2)⟩

def reset (memo : RegistrationNativeReferenceInterpreter.State) (before : Private n KemSK) : Private n KemSK :=
  put memo (drop before)

/-- The frame projection preserves every coordinate other than the named reference memo. -/
theorem drop_put (memo : RegistrationNativeReferenceInterpreter.State) (before : Frame n KemSK) :
    drop (put memo before) = before := rfl

/-- Restoring the original memo and complete frame reconstructs the whole literal private state. -/
theorem put_drop (before : Private n KemSK) : put before.extra.1 (drop before) = before := rfl

/-- A root-free native callback commutes with changing only the private reference memo. -/
theorem query_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (before : Private n KemSK) :
    Prod.map id (reset memo) <$> (trusted setup wire route sign seed scalar query).run before =
      (trusted setup wire route sign seed scalar query).run (reset memo before) := by
  cases query with
  | inl query =>
      simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
        RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query,
        RegistrationNativePublicSourceCallbacks.implementation, RegistrationNativeKemReferenceEffects.implementation,
        RegistrationNativeKemReferenceWorld.handler, RegistrationNativeKemReferenceWorld.effect,
        RegistrationNativeKemReferenceWorld.withWorld, StateT.run, reset, drop, put,
        Functor.map_map, Prod.map_def, id_eq]
  | inr query =>
      simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
        RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query,
        RegistrationNativePublicSourceCallbacks.implementation, RegistrationNativeKemReferenceEffects.implementation,
        RegistrationNativeKemReferenceWorld.handler, RegistrationNativeKemReferenceWorld.kem,
        StateT.run, reset, drop, put, map_bind, map_pure, Prod.map_def, id_eq]

/-- Resetting the inaccessible memo commutes with every adaptive root-free native program. -/
theorem program_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (before : Private n KemSK) :
    Prod.map id (reset memo) <$> (simulateQ (trusted setup wire route sign seed scalar) work).run before =
      (simulateQ (trusted setup wire route sign seed scalar) work).run (reset memo before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (reset memo)
    (query_reset setup wire route sign seed scalar memo) work before

/-- The complete retained frame is independent of the input memo, with the whole original adaptive program unchanged. -/
theorem program_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (before : Private n KemSK) :
    Prod.map id drop <$> (simulateQ (trusted setup wire route sign seed scalar) work).run before =
      Prod.map id drop <$> (simulateQ (trusted setup wire route sign seed scalar) work).run (reset memo before) := by
  have actual := congrArg (fun distribution => Prod.map id drop <$> distribution)
    (program_reset setup wire route sign seed scalar memo work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, reset, drop, put] using actual

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.drop_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.drop_put
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.put_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.put_drop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.query_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.query_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.program_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.program_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame.program_frame
