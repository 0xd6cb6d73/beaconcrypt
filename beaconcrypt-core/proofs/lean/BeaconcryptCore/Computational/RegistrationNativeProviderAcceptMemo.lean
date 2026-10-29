-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderLocal

/-! Ordinary provider-source effects and indexed KEM operations never inspect the private prepared-root memo. Resetting only that analysis memo commutes with these concrete callbacks and their full adaptive continuations. Material demand is deliberately outside this frame law because it reads the memo. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider State)
open RegistrationNativeProviderSource (localImpl routed_source)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def reset (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) : State n KemSK ProviderState :=
  ({ before.1 with roots := memo }, before.2)

theorem effect_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State n KemSK ProviderState) :
    (localImpl setup wire route sign seed scalar provider selected (.inr (.inl (.inr (.inr query))))).run before =
      (fun result => (result.1, ({ before.1 with world := result.2 }, before.2))) <$>
        (PqxdhRecordLiftWorld.effects query).run before.1.world := by
  simp only [localImpl, RegistrationNativeProviderSource.localHandler,
    RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
    RegistrationNativeProviderInterpreter.handler, RegistrationNativePublicInterpreter.handler,
    RegistrationNativePublicInterpreter.common]
  rw [RegistrationNativeProviderSource.withBase_source]
  unfold RegistrationNativePublicInterpreter.effect
  rw [RegistrationNativePublicSourceEffects.close_world]
  simp only [Functor.map_map]
  rfl

theorem effect_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (memo : RegistrationNativeReferenceInterpreter.State)
    (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$>
      (localImpl setup wire route sign seed scalar provider selected (.inr (.inl (.inr (.inr query))))).run before =
      (localImpl setup wire route sign seed scalar provider selected (.inr (.inl (.inr (.inr query))))).run (reset memo before) := by
  rw [effect_run, effect_run]
  simp only [reset, Functor.map_map, Prod.map_def, id_eq]

theorem routed_reset (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$>
      (RegistrationNativeProviderLocal.routedImpl setup seed scalar provider query).run before =
      (RegistrationNativeProviderLocal.routedImpl setup seed scalar provider query).run (reset memo before) := by
  unfold RegistrationNativeProviderLocal.routedImpl
  rw [routed_source, routed_source]
  simp only [reset, Functor.map_map, Prod.map_def, id_eq]

theorem kem_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$>
      (localImpl setup wire route sign seed scalar provider selected (.inr (.inr query))).run before =
      (localImpl setup wire route sign seed scalar provider selected (.inr (.inr query))).run (reset memo before) := by
  rw [RegistrationNativeProviderLocal.kem_program, RegistrationNativeProviderLocal.kem_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (reset memo)
    (routed_reset setup seed scalar provider · memo) (RegistrationNativeKemRouting.route selected query) before

def Framed : (RegistrationBeaconReferenceCompiler.Spec n Unit).Domain → Prop
  | .inr (.inl (.inr (.inr _))) | .inr (.inr _) => True
  | _ => False

theorem query_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) (framed : Framed query)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$> (localImpl setup wire route sign seed scalar provider selected query).run before =
      (localImpl setup wire route sign seed scalar provider selected query).run (reset memo before) := by
  rcases query with message | ((message | (publication | effect)) | query)
  · exact framed.elim
  · exact framed.elim
  · exact framed.elim
  · exact effect_reset setup wire route sign seed scalar provider selected effect memo before
  · exact kem_reset setup wire route sign seed scalar provider selected query memo before

/-- Actual adaptive ordinary work and all indexed KEM branches keep the complete World, pool, counters, signing log and provider state under the same memo erasure. -/
theorem program_reset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (framed : AllQueriesSatisfy work Framed)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$> (simulateQ (localImpl setup wire route sign seed scalar provider selected) work).run before =
      (simulateQ (localImpl setup wire route sign seed scalar provider selected) work).run (reset memo before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp framed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_reset setup wire route sign seed scalar provider selected query first memo before, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (later result.1) result.2

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.effect_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.effect_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.effect_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.effect_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.routed_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.routed_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.kem_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.kem_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.query_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.query_reset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.program_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo.program_reset
