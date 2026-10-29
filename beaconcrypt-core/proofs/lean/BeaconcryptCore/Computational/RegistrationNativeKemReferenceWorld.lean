-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler
import BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative

/-! Actual real-source lowering of the open Server KEM/reference interface. The private World, indexed KEM pool and any remaining private service state stay separate from the scalar-free environment. Prefix programs use only ordinary effects and the literal encapsulation getter; prepare/material/publication callbacks are retained as arbitrary unreachable services rather than replaced by a source-game equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeKemReferenceCompiler (Spec)
variable {n : Nat} {ι KemSK Extra Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

structure Private (n : Nat) (KemSK Extra : Type) where
  world : PqxdhRecordLiftWorld.State n
  pool : PqxdhLiveKemBirth.Pool KemSK
  extra : Extra

def withWorld (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    StateT (Private n KemSK Extra) ProbComp Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

private theorem withWorld_run (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : Private n KemSK Extra) :
    (withWorld work).run before =
      (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world := rfl

noncomputable def effect : QueryImpl (EnvEffects n) (StateT (Private n KemSK Extra) ProbComp) :=
  fun query => withWorld (PqxdhRecordLiftWorld.effects query)

/-- Lifting actual World callbacks preserves the entire private pool and remaining service state through arbitrary adaptive continuations. -/
theorem world_program (implementation : QueryImpl spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp))
    (work : OracleComp spec Value) (before : Private n KemSK Extra) :
    (simulateQ (fun query => withWorld (implementation query)) work).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ implementation work).run before.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, withWorld_run,
        bind_map_left, ih, map_bind]

noncomputable def kem (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp) :
    QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK)
      (StateT (Private n KemSK Extra) ProbComp) := fun query before => do
  let result ← (PqxdhRecordLiftWorld.sampled
    ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
      (fun request => StateT.lift (other request)) query).run ((), before.pool))).run before.world
  pure (result.1.1, { before with world := result.2, pool := result.1.2.2 })

noncomputable def handler (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) ProbComp))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) ProbComp))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) ProbComp)) :
    QueryImpl (Spec n KemSK) (StateT (Private n KemSK Extra) ProbComp)
  | .inl message => prepare message
  | .inr (.inl (.inl message)) => demand message
  | .inr (.inl (.inr (.inl query))) => publication query
  | .inr (.inl (.inr (.inr query))) => effect query
  | .inr (.inr query) => kem setup other query

/-- Actual ordinary environment effects retain their original World behavior and entire private frame under the extended interface. -/
theorem effect_query (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) ProbComp))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) ProbComp))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) ProbComp))
    (query : (EnvEffects n).Domain) :
    ((handler setup other prepare demand publication ∘ₛ RegistrationNativeKemReferenceCompiler.lift) ∘ₛ
        RegistrationServerReferenceCompiler.effect) query = effect (KemSK := KemSK) (Extra := Extra) query := by
  simp only [QueryImpl.compose, RegistrationServerReferenceCompiler.effect,
    simulateQ_spec_query, RegistrationNativeKemReferenceCompiler.lift, handler]

private theorem sampled_run {Output : Type} (work : ProbComp Output) (before : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled work).run before =
      (fun result => (result.1, { before with primitive :=
        ({ before.primitive.1 with uniform := result.2 }, before.primitive.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.countCoin work).run before.primitive.1.uniform := by
  change ((simulateQ PqxdhRecordLiftWorld.countCoin work).run before.primitive.1.uniform >>= fun result =>
    pure (result.1, { before with primitive :=
      ({ before.primitive.1 with uniform := result.2 }, before.primitive.2) })) = _
  rw [bind_pure_comp]

/-- Mapping a source sampler preserves its complete World counting state. -/
theorem sampled_map {First Second : Type} (work : ProbComp First) (observe : First → Second)
    (before : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (observe <$> work)).run before =
      Prod.map observe id <$> (PqxdhRecordLiftWorld.sampled work).run before := by
  rw [sampled_run, sampled_run, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

/-- The literal indexed encapsulation uses the actual source sampler while retaining the entire private generated-key pool and remaining service frame. -/
theorem kem_encapsulation (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (key : PqxdhKemIndCca.MlKem768PublicKey) (before : Private n KemSK Extra) :
    (kem setup other (.inr (.inr key))).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (PqxdhRecordLiftWorld.sampled
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key))).run before.world := by
  have lifted : (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
      (fun request => StateT.lift (other request)) (.inr (.inr key))).run ((), before.pool) =
      (fun output => (output, ((), before.pool))) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key) := by
    rw [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp]
    rfl
  change (do
    let result ← (PqxdhRecordLiftWorld.sampled
      ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
        (fun request => StateT.lift (other request)) (.inr (.inr key))).run ((), before.pool))).run before.world
    pure (result.1.1, { before with world := result.2, pool := result.1.2.2 })) = _
  rw [lifted, sampled_map]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]

/-- Indexed requests keep the concrete same private source handler; no ambient encapsulation is substituted for the exposed getter. -/
theorem indexed_query (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) ProbComp))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) ProbComp))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) ProbComp))
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    (handler setup other prepare demand publication ∘ₛ RegistrationBeaconReferenceCompiler.indexed) query =
      kem (n := n) (Extra := Extra) setup other query := by
  simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.indexed,
    simulateQ_spec_query, handler]

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.world_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.world_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.effect_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.effect_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.kem_encapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.kem_encapsulation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.indexed_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.indexed_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.sampled_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld.sampled_map
