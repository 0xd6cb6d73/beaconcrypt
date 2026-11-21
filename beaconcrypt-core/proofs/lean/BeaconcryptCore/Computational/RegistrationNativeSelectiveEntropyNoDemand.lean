-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyEffects
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocation

/-! A source program with no material demand uses exactly the original backend, retaining the selective cache verbatim. The actual native constructor supplies this zero-demand receipt internally. This restricted operational equation is not asserted for build, finish or the whole selective game. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativeSelectiveAllocationJoint (dropLocal drop)
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run interpret_map)
variable {n : Nat} {ι KemSK ProviderState Value Secret Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every zero-demand adaptive local program retains the exact original backend execution and unchanged additional cache. -/
theorem program_base (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) 0)
    (before : State n KemSK ProviderState) :
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) work).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have other := bounded.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [RegistrationNativeSelectiveHiddenInterpreter.query_other setup wire sign seed scalar candidate provider query other]
      simp only [RegistrationNativeSelectiveHiddenInterpreter.onBase, StateT.run, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (by simpa using bounded.2 result.1) (result.2, before.2)

/-- Closing a zero-demand actual frontend program projects only the untouched extra cache and keeps every original World effect. -/
theorem close_base (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
    (bounded : (work.run before.1).IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) 0) :
    Prod.map id dropLocal <$> (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work).run before =
      (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider work).run (dropLocal before) := by
  rw [RegistrationNativeSelectiveEntropyEffects.close_run, program_base setup wire sign seed scalar candidate provider _ bounded]
  simp only [RegistrationNativeHiddenEnvironmentEffects.close_run, Functor.map_map, dropLocal, Prod.map, id_eq]

/-- The same source equation retains the actual full cursor, Protocol control and arbitrary private record-service state. -/
theorem lower_base (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source)
    (bounded : (work.run before.1.1.1.1).IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) 0) :
    Prod.map id drop <$> (lower service codec route
      (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work)).run before =
      (lower service codec route (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider work)).run (drop before) := by
  have projected := congrArg (fun (program : OracleComp (PqxdhRecordLiftInterface.WorldSpec n)
      (Value × RegistrationNativeHiddenEnvironment.State n KemSK ProviderState source)) =>
    (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
      CborRawRecordOriginFlatten.interpret service codec route program before.1.1.2 before.1.2 before.2)
    (close_base setup wire sign seed scalar candidate provider work before.1.1.1 bounded)
  rw [interpret_map] at projected
  simpa only [lower_run, Functor.map_map, drop, dropLocal, Prod.map, id_eq] using projected

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.program_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.program_base
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.close_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.close_base
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.lower_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand.lower_base
