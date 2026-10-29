-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo

/-! Root-free native Beacon programs cannot inspect the private reference memo. The provider receives only the live KEM pool and its own state, so the same memo erasure law holds for arbitrary indexed decapsulation and all adaptive native continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState pack unpack implementation)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeProviderBeaconPreparation (Frame drop)
open RegistrationBeaconReferenceCompiler (trustedLift)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def put (memo : RegistrationNativeReferenceInterpreter.State) (before : Frame n KemSK ProviderState) :
    NativeState n KemSK ProviderState :=
  (RegistrationNativeOrdinaryFinishSourceFrame.put memo before.1, before.2)

def reset (memo : RegistrationNativeReferenceInterpreter.State) (before : NativeState n KemSK ProviderState) :
    NativeState n KemSK ProviderState := put memo (drop before)

theorem query_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : NativeState n KemSK ProviderState) :
    Prod.map id (reset memo) <$> (trusted setup wire route sign seed scalar provider query).run before =
      (trusted setup wire route sign seed scalar provider query).run (reset memo before) := by
  have framed : RegistrationNativeProviderAcceptMemo.Framed
      (match query with
      | .inl effect => .inr (.inl (.inr (.inr effect)))
      | .inr kem => .inr (.inr kem)) := by
    cases query <;> trivial
  have actual := RegistrationNativeProviderAcceptMemo.query_reset setup wire route sign seed scalar provider false
    (match query with
    | .inl effect => .inr (.inl (.inr (.inr effect)))
    | .inr kem => .inr (.inr kem)) framed memo (unpack before)
  have mapped := congrArg (fun distribution => Prod.map id pack <$> distribution) actual
  cases query <;>
    simpa only [trusted, QueryImpl.apply_compose, trustedLift, RegistrationBeaconReferenceCompiler.effect,
      RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query, implementation,
      StateT.run, Functor.map_map, Prod.map_def, id_eq, reset, put, drop,
      pack, unpack, RegistrationNativeProviderAcceptMemo.reset,
      RegistrationNativePublicSourceEffects.toPrivate, RegistrationNativePublicSourceEffects.fromPrivate,
      RegistrationNativeOrdinaryFinishSourceFrame.put, RegistrationNativeOrdinaryFinishSourceFrame.drop] using mapped

/-- Memo erasure commutes with every actual adaptive root-free native program, retaining the entire provider state. -/
theorem program_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : NativeState n KemSK ProviderState) :
    Prod.map id (reset memo) <$> (simulateQ (trusted setup wire route sign seed scalar provider) work).run before =
      (simulateQ (trusted setup wire route sign seed scalar provider) work).run (reset memo before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (reset memo)
    (query_reset setup wire route sign seed scalar provider memo) work before

/-- The observed native frame is independent of the input memo; no operational coordinate is erased. -/
theorem program_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$> (simulateQ (trusted setup wire route sign seed scalar provider) work).run before =
      Prod.map id drop <$> (simulateQ (trusted setup wire route sign seed scalar provider) work).run (reset memo before) := by
  have actual := congrArg (fun distribution => Prod.map id drop <$> distribution)
    (program_reset setup wire route sign seed scalar provider memo work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, reset, drop, put,
    RegistrationNativeOrdinaryFinishSourceFrame.put, RegistrationNativeOrdinaryFinishSourceFrame.drop] using actual

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.query_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.query_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.program_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.program_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame.program_frame
