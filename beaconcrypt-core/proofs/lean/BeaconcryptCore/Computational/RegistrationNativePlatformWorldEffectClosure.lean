-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower
/-! Restricted source effects interpret on a separate private World. The public platform state is retained independently, while the Local source lens merely restores its unchanged auxiliary/request/receipt fields. Embedding into the existing World-plus-external-coin language preserves this same execution. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure
open RegistrationNativePlatformEffectCompiler (Spec)
variable {n : Nat} {Auxiliary Platform A : Type}

noncomputable def implementation : QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl effect => PqxdhRecordLiftWorld.effects effect
  | .inr coin => StateT.lift (unifSpec.query coin : ProbComp _)

noncomputable def close (work : StateT Platform (OracleComp (Spec n)) A) :
    StateT (PqxdhRecordLiftWorld.State n) (StateT Platform ProbComp) A := fun current previous =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ implementation (work.run previous)).run current

def attach (before : RegistrationWorldAgreement.State n Auxiliary) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationWorldAgreement.State n Auxiliary := { before with world := (world, before.world.2) }

private theorem query (before : RegistrationWorldAgreement.State n Auxiliary)
    (request : (Spec n).Domain) (world : PqxdhRecordLiftWorld.State n) :
    Prod.map id (attach before) <$> (implementation request).run world =
      (RegistrationNativePlatformEffectCompiler.implementation request).run (attach before world) := by
  cases request with
  | inl effect => rfl
  | inr coin =>
    simp only [implementation, RegistrationNativePlatformEffectCompiler.implementation,
      StateT.run_lift, bind_pure_comp, Functor.map_map]
    rfl

private theorem program (before : RegistrationWorldAgreement.State n Auxiliary)
    (work : OracleComp (Spec n) A) (world : PqxdhRecordLiftWorld.State n) :
    Prod.map id (attach before) <$> (simulateQ implementation work).run world =
      (simulateQ RegistrationNativePlatformEffectCompiler.implementation work).run (attach before world) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (attach before) (query before) work world

/-- The concrete source effect compiler contains exactly one private World; all other Local fields and the common persistent platform state are preserved by its source lens. -/
theorem local_world (work : StateT Platform (OracleComp (Spec n)) A)
    (before : RegistrationWorldAgreement.State n Auxiliary) (previous : Platform) :
    ((RegistrationNativePlatformEffectCompiler.close work).run before).run previous =
      (fun result => ((result.1.1, attach before result.1.2), result.2)) <$>
        ((close work).run before.world.1).run previous := by
  have same := program before (work.run previous) before.world.1
  have attached : attach before before.world.1 = before := rfl
  rw [attached] at same
  have mapped := congrArg (fun action => (fun result => ((result.1.1, result.2), result.1.2)) <$> action) same
  simpa only [close, RegistrationNativePlatformEffectCompiler.close, StateT.run,
    Functor.map_map, Prod.map, id_eq] using mapped.symm


def embedding : QueryImpl (Spec n) (OracleComp (RegistrationNativePlatformOrdinaryRandomizedLower.Spec n))
  | .inl effect => RegistrationNativePlatformOrdinaryRandomizedLower.world (.inr (.inl effect))
  | .inr coin => RegistrationNativePlatformOrdinaryRandomizedLower.publicCoin coin

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- This same restricted client embeds into the actual ordinary-record lower language; external random draws remain separate from private World accounting. -/
theorem embedded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (Spec n) A) :
    simulateQ (RegistrationNativePlatformOrdinaryRandomizedLower.implementation
      (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route))
      (simulateQ embedding work) = simulateQ implementation work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler work)
  funext request
  cases request with
  | inl effect =>
    simp only [QueryImpl.apply_compose, embedding, RegistrationNativePlatformOrdinaryRandomizedLower.world,
      simulateQ_spec_query, RegistrationNativePlatformOrdinaryRandomizedLower.implementation, implementation]
    rfl
  | inr coin =>
    simp only [QueryImpl.apply_compose, embedding, RegistrationNativePlatformOrdinaryRandomizedLower.publicCoin,
      simulateQ_spec_query, RegistrationNativePlatformOrdinaryRandomizedLower.implementation, implementation]

/-- The entire actual source first record runs as a client with only the persistent public platform state, alongside one separate private World and its exact reached shared cache. The accounting view is stated explicitly. -/
theorem source_record [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] {E : Type}
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationServerRootCompiler.Local n) (previous : Platform) :
    ((Prod.map id RegistrationServerRecordWorldSource.project <$>
      (RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (RegistrationNativePlatformServerCompletion.records RegistrationNativePlatformMldsaProgram.coins setup codec)
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper) initial).run before).run previous) =
      (fun result => ((result.1.1, attach (RegistrationServerRecordWorldSource.project before) result.1.2), result.2)) <$>
        ((close (RegistrationNativePlatformRecordCompiler.record setup.source view failure allocation erased helper
          (RegistrationBoundKeySchedule.publicInitial initial) (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run
            (RegistrationServerRecordWorldSource.project before).world.1).run previous := by
  have same := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformRecordCompiler.source setup codec view failure allocation erased helper initial root role before)
  rw [local_world] at same
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.local_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.local_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.embedded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.source_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure.source_record
