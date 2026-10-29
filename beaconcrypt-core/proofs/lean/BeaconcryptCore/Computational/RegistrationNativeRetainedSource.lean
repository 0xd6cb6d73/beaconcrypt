-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRetainedService
import BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection

/-! The private root-cache/memo interface of the actual ideal related-root interpreter is the retained phase service after erasing only ghost preparation counters. Complete adaptive output equality composes this exact source interface with private-root erasure and the five-loss uniform108 bound. No root/PRK independence or whole-client simulation premise is used. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRetainedSource
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Spec)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value : Type}

abbrev State := RegistrationNativeRetainedRoots.Memo × HmacOracle.QueryCache

def project (state : RegistrationNativeRetainedRoots.State) : State := (state.1, state.2.2)

noncomputable def implementation (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr (.prepare message) => fun before => do
      let result ← (RegistrationNativeRetainedRoots.root source hmac input inside message).run before.2
      pure (result.1.map (fun _ => message), (Function.update before.1 message result.1, result.2))
  | .inr (.demand message) => fun before =>
      pure ((before.1 message).map (PqxdhServerAuthKeySchedule.fromRoot source), before)

noncomputable def initial : State := ((fun _ => none), ∅)

/-- The actual optional private root callback is precisely the protected slice of the ideal native related-family interpreter. -/
theorem actual_root (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (message : Message) :
    RegistrationNativeRetainedRoots.root source hmac (RegistrationNativeRelatedFamily.input joint dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (joint.staticDh seed (dh.publicKey scalar))) message =
      RegistrationNativeRootCacheProjection.implementation source hmac joint dh seed scalar (.inr (.derive message)) := rfl

/-- The ghost-augmented prepare/material service retains exactly the original private cache/memo reply and state. -/
theorem query_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : RegistrationNativeRetainedRoots.State) :
    Prod.map id project <$> (RegistrationNativeRetainedService.retained source hmac input inside query).run before =
      (implementation source hmac input inside query).run (project before) := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRetainedService.retained, implementation,
        StateT.run, StateT.lift, bind_pure_comp, Functor.map_map]
      rfl
  | inr request => cases request with
    | prepare message => exact RegistrationNativeRetainedRoots.remember_root source hmac input inside message before
    | demand message =>
      cases stored : before.1 message <;>
        simp only [RegistrationNativeRetainedService.retained, RegistrationNativeRetainedRoots.demand,
          implementation, project, StateT.run, stored, Option.map_none, Option.map_some,
          map_pure, Prod.map, id_eq]

/-- Entire adaptive source clients retain their original output and private cache/memo after ghost metadata is erased. -/
theorem program_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (before : RegistrationNativeRetainedRoots.State) :
    Prod.map id project <$> (simulateQ (RegistrationNativeRetainedService.retained source hmac input inside) work).run before =
      (simulateQ (implementation source hmac input inside) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_project source hmac input inside) work before

/-- The actual root-cache/memo source execution starts before preparation and equals the constructed before-prepare phase game. -/
theorem source_phase (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (work : OracleComp Spec Bool) :
    (simulateQ (implementation source hmac input inside) work).run' initial =
      RegistrationNativeKeyServiceBound.g1 source hmac input inside (RegistrationNativeRetainedService.client work) := by
  have projected := congrArg (fun experiment => Prod.fst <$> experiment)
    (program_project source hmac input inside work RegistrationNativeRetainedService.initial)
  have empty : project RegistrationNativeRetainedService.initial = initial := rfl
  rw [empty] at projected
  have same : (simulateQ (implementation source hmac input inside) work).run' initial =
      (simulateQ (RegistrationNativeRetainedService.retained source hmac input inside) work).run'
        RegistrationNativeRetainedService.initial := by
    simpa only [StateT.run'_eq, Functor.map_map, Prod.map, id_eq] using projected.symm
  rw [same, RegistrationNativeRetainedService.source_phase]

/-- The actual retained source root interface has the uniform108 bound with the derived demand bill and the five ordinary primitive losses. -/
theorem key_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) (count : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeRetainedService.IsDemand count) :
    ((simulateQ (implementation source hmac input inside) work).run' initial).boolDistance
      (RegistrationNativeKeyServiceBound.g2 source input inside (RegistrationNativeRetainedService.client work)) ≤
      ∑ index ∈ Finset.range count, RegistrationBoundKeySchedule.keyLoss source hmac
        (RegistrationNativeKeyHybrid.reduction source hmac
          (RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work)
            RegistrationNativeKeyPhases.emptyMeta) index) := by
  rw [source_phase]
  exact RegistrationNativeKeyServiceBound.bound source hmac correct input inside _ count
    (RegistrationNativeRetainedService.client_bound work count bounded)

end BeaconcryptCore.Computational.RegistrationNativeRetainedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedSource.actual_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedSource.actual_root
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedSource.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedSource.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedSource.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedSource.program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedSource.source_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedSource.source_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedSource.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedSource.key_bound
