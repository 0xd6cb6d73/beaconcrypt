-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame

/-! The native trusted interpreter receives no Server seed, selected scalar or root memo. It runs actual World effects and the same total indexed KEM provider under the shared World sampler. The derived full-program projection removes only the private reference memo; every operational World, pool, signing-receipt and provider coordinate remains. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderNative
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState pack unpack)
open RegistrationNativeProviderBeaconPreparation (Frame drop)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    StateT (Frame n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1, ((result.2, before.1.2.1, before.1.2.2), before.2))) <$> work.run before.1.1

noncomputable def routed (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    StateT (Frame n KemSK ProviderState) ProbComp ((RegistrationNativePublicFrontend.RoutedKem KemSK).Range query) := fun before =>
  (fun result => (result.1.1, ((result.2, result.1.2.1, before.1.2.2), result.1.2.2))) <$>
    (PqxdhRecordLiftWorld.sampled ((provider query).run (before.1.2.1, before.2))).run before.1.1

noncomputable def handler (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
      (StateT (Frame n KemSK ProviderState) ProbComp)
  | .inl query => world (PqxdhRecordLiftWorld.effects query)
  | .inr query => simulateQ (routed provider) (RegistrationNativeKemRouting.route false query)

def rawDrop (before : RegistrationNativeProviderInterpreter.State n KemSK ProviderState) :
    Frame n KemSK ProviderState := drop (pack before)

/-- The actual source routed callback projects to the seed/scalar-free provider sampler with its complete reached frame. -/
theorem routed_project (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : RegistrationNativeProviderInterpreter.State n KemSK ProviderState) :
    Prod.map id rawDrop <$>
      (RegistrationNativeProviderLocal.routedImpl setup seed scalar provider query).run before =
      (routed provider query).run (rawDrop before) := by
  unfold RegistrationNativeProviderLocal.routedImpl
  rw [RegistrationNativeProviderSource.routed_source]
  simp only [routed, StateT.run, rawDrop, drop, pack,
    RegistrationNativeOrdinaryFinishSourceFrame.drop, RegistrationNativePublicSourceEffects.toPrivate,
    Functor.map_map, Prod.map_def, id_eq]

/-- Both native effects and indexed KEM requests retain exactly the same operational state after removing only the reference memo. -/
theorem query_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (RegistrationNativeProviderBeaconAgreement.trusted setup wire route sign seed scalar provider query).run before =
      (handler provider query).run (drop before) := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeProviderBeaconAgreement.trusted, QueryImpl.apply_compose,
        RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
        simulateQ_spec_query, RegistrationNativeProviderCallbacks.implementation, StateT.run,
        Functor.map_map, Prod.map_def, id_eq]
      change (fun result => (result.1, drop (pack result.2))) <$>
        (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider false
          (.inr (.inl (.inr (.inr query))))).run (unpack before) = _
      rw [RegistrationNativeProviderAcceptMemo.effect_run]
      simp only [Functor.map_map, handler, world, StateT.run, drop, pack, unpack,
        RegistrationNativeOrdinaryFinishSourceFrame.drop, RegistrationNativePublicSourceEffects.toPrivate,
        RegistrationNativePublicSourceEffects.fromPrivate]
      rfl
  | inr query =>
      simp only [RegistrationNativeProviderBeaconAgreement.trusted, QueryImpl.apply_compose,
        RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
        simulateQ_spec_query, RegistrationNativeProviderCallbacks.implementation, StateT.run,
        Functor.map_map, Prod.map_def, id_eq]
      change (fun result => (result.1, drop (pack result.2))) <$>
        (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider false
          (.inr (.inr query))).run (unpack before) = _
      rw [RegistrationNativeProviderLocal.kem_program]
      have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq
        (RegistrationNativeProviderLocal.routedImpl setup seed scalar provider) (routed provider) rawDrop
        (routed_project setup seed scalar provider)
        (RegistrationNativeKemRouting.route false query) (unpack before)
      simp only [handler, rawDrop, drop, pack, unpack,
        RegistrationNativeOrdinaryFinishSourceFrame.drop, RegistrationNativePublicSourceEffects.toPrivate,
        RegistrationNativePublicSourceEffects.fromPrivate, Prod.map_def, id_eq, StateT.run] at law ⊢
      convert law using 1
      all_goals rfl

/-- Every adaptive native trusted program has the same complete retained outcome under the concrete provider interpreter. -/
theorem program_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (RegistrationNativeProviderBeaconAgreement.trusted setup wire route sign seed scalar provider) work).run before =
      (simulateQ (handler provider) work).run (drop before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ drop
    (query_project setup wire route sign seed scalar provider) work before

end BeaconcryptCore.Computational.RegistrationNativeProviderNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderNative.routed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderNative.routed_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderNative.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderNative.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderNative.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderNative.program_project
