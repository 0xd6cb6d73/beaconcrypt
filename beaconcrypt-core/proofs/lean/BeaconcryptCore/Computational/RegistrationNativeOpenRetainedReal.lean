-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld

/-! The real specialization of the external provider is the literal indexed key pool and ordinary public encapsulation implementation. This source law retains all generated-key histories and actual sampler counts before applying the open compiler's explicit projection. It supplies no premise identifying real encapsulation with a randomized candidate branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativePublicInterpreter (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def provider (setup : Setup base KemSK) : Provider KemSK Unit
  | .inl (.inl query) => fun before =>
      (fun reply => (reply, before)) <$> RegistrationNativePublicInterpreter.unavailable query
  | .inl (.inr key) => fun before => (fun reply => (reply, before)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)
  | .inr (.inl query) => fun before => (fun result => (result.1, (result.2, before.2))) <$>
      (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.1
  | .inr (.inr key) => fun before => (fun reply => (reply, before)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)

private theorem ordinary_world (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) (before : State n KemSK) :
    (RegistrationNativePublicRetained.ordinary hmac (RegistrationNativePublicInterpreter.world work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        simulateQ RegistrationNativePublicRetained.coins (work.run before.world) := by
  change simulateQ RegistrationNativePublicRetained.coins
    (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac)
      ((fun result => (result.1, { before with world := result.2 })) <$>
        simulateQ RegistrationNativePublicInterpreter.coins (work.run before.world))) = _
  simp only [simulateQ_map]
  rw [← QueryImpl.simulateQ_compose (RegistrationNativePublicRootCoins.localImpl hmac)
    RegistrationNativePublicInterpreter.coins]
  have same : RegistrationNativePublicRootCoins.localImpl hmac ∘ₛ RegistrationNativePublicInterpreter.coins =
      QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- The real opaque provider executes exactly the original counted routed callback, retaining the full source pool and provider frame. -/
theorem routed_real (setup : Setup base KemSK)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK Unit) :
    (RegistrationNativeOpenRetainedSource.routed (provider setup) query).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationNativePublicRetained.ordinary setup.hmac
          (RegistrationNativePublicInterpreter.routedKem setup query)).run before.1 := by
  rcases query with (query | key) | query | key
  · cases query <;> simp [provider, RegistrationNativeOpenRetainedSource.routed,
      RegistrationNativePublicInterpreter.routedKem, RegistrationNativePublicInterpreter.kem,
      RegistrationNativePublicInterpreter.unavailable, RegistrationNativePublicRetained.ordinary,
      PqxdhRecordLiftWorld.sampled,
      StateT.lift, StateT.run, StateT.monad_pure_def, StateT.pure]
  · change _ = (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativePublicRetained.ordinary setup.hmac (RegistrationNativePublicInterpreter.world
        (PqxdhRecordLiftWorld.sampled (simulateQ
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))))).run before.1
    rw [ordinary_world]
    change (fun result => (result.1.1,
      ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        simulateQ RegistrationNativePublicRetained.coins
          ((PqxdhRecordLiftWorld.sampled ((fun reply => (reply, (before.1.pool, before.2))) <$>
            simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))).run before.1.world) = _
    rw [RegistrationNativeKemReferenceWorld.sampled_map]
    simp only [simulateQ_map, Functor.map_map, Prod.map_def, id_eq]
  · change _ = (fun result => (result.1, (result.2, before.2))) <$>
      simulateQ RegistrationNativePublicRetained.coins
        (simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac)
          ((RegistrationNativePublicInterpreter.kem setup (.inr (.inl query))).run before.1))
    simp only [RegistrationNativePublicInterpreter.kem, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, simulateQ_map]
    have world := ordinary_world setup.hmac
      (PqxdhRecordLiftWorld.sampled ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.1.pool)) before.1
    simp only [RegistrationNativePublicRetained.ordinary, StateT.run] at world
    simp only [StateT.run]
    rw [world]
    change (fun result => (result.1.1,
      ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        simulateQ RegistrationNativePublicRetained.coins
          ((PqxdhRecordLiftWorld.sampled ((fun result => (result.1, (result.2, before.2))) <$>
            (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.1.pool)).run before.1.world) = _
    rw [RegistrationNativeKemReferenceWorld.sampled_map]
    simp only [simulateQ_map, Functor.map_map, Prod.map_def, id_eq]
    rfl
  · change _ = (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativePublicRetained.ordinary setup.hmac (RegistrationNativePublicInterpreter.world
        (PqxdhRecordLiftWorld.sampled (simulateQ
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))))).run before.1
    rw [ordinary_world]
    change (fun result => (result.1.1,
      ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        simulateQ RegistrationNativePublicRetained.coins
          ((PqxdhRecordLiftWorld.sampled ((fun reply => (reply, (before.1.pool, before.2))) <$>
            simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))).run before.1.world) = _
    rw [RegistrationNativeKemReferenceWorld.sampled_map]
    simp only [simulateQ_map, Functor.map_map, Prod.map_def, id_eq]

/-- Every real compiler callback is the existing retained callback with a literal unchanged Unit frame. -/
theorem query_real (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK Unit) :
    (RegistrationNativeOpenRetainedSource.source setup wire route sign (provider setup) query).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationNativePublicRetained.compiler setup wire route sign query).run before.1 := by
  rcases query with (message | (message | query) | query) | query
  · rfl
  · rfl
  · rfl
  · exact routed_real setup query before
  · rfl

/-- The complete real specialization preserves the literal adaptive retained program before the explicit external-pool projection. -/
theorem program_real (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativeOpenRetainedSource.SourceState n KemSK Unit) :
    (simulateQ (RegistrationNativeOpenRetainedSource.source setup wire route sign (provider setup)) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativePublicRetained.compiler setup wire route sign) work).run before.1 := by
  let embed : State n KemSK → RegistrationNativeOpenRetainedSource.SourceState n KemSK Unit := fun state => (state, before.2)
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed
    (fun query state => (query_real setup wire route sign query (state, before.2)).symm) work before.1).symm

/-- Closing the executable open retained client with the literal real pool gives exactly the earlier real retained client. Only private compiler poststate is discarded. -/
theorem client_real (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) :
    (simulateQ (RegistrationNativeOpenRetainedSource.close (provider setup))
      (RegistrationNativeOpenRetained.client setup wire route sign work before)).run'
        (before.pool, ()) = RegistrationNativePublicRetained.client setup wire route sign work before := by
  have source := RegistrationNativeOpenRetainedSource.program_project setup wire route sign (provider setup) work
    (RegistrationNativePublicRetained.clear before, ())
  rw [program_real] at source
  have observed := congrArg (fun experiment => Prod.fst <$> experiment) source
  simp only [Functor.map_map, Prod.map_def, id_eq] at observed
  simp only [RegistrationNativeOpenRetained.client, RegistrationNativePublicRetained.client,
    StateT.run'_eq, simulateQ_map, StateT.run_map]
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map]
  simpa only [RegistrationNativeOpenRetainedSource.reference, RegistrationNativeOpenRetainedSource.project,
    RegistrationNativePublicRetained.clear, RegistrationNativePublicRootFrame.replace] using observed.symm

end BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.routed_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.routed_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.query_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.query_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.program_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.program_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.client_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal.client_real
