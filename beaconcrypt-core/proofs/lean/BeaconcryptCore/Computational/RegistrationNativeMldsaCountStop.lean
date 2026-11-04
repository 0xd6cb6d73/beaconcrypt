-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountProfile
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserverView

/-! The actual first-forgery stopping wrapper preserves its candidate and same-cut native state under free ML count normalization. Observer invariance is checked independently from actual public pins, phases, cache and signing history. Once selected, fixed default replies issue no primitive query. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaCountRules (Correct)
variable {source : RegistrationNativeMldsa.Source} {State Candidate Query Value : Type} {queries : OracleSpec Query}

def view (projection : State → State) (before : State × Option Candidate) := (projection before.1, before.2)

private theorem idempotent (projection : State → State)
    (same : ∀ before, projection (projection before) = projection before) (before : State × Option Candidate) :
    view projection (view projection before) = view projection before := by
  simp only [view, same]

section Generic
variable (projection : State → State) (same : ∀ before, projection (projection before) = projection before)
variable (observe : RegistrationNativeMldsaStop.Observer (spec := queries) (State := State) (Candidate := Candidate))
variable (invariant : ∀ query before after reply, observe query (projection before) reply (projection after) = observe query before reply after)
include same invariant

private theorem observer_before (query : queries.Domain) (before after : State) (reply : queries.Range query) :
    observe query (projection before) reply after = observe query before reply after := by
  have initial := invariant query (projection before) after reply
  rw [same] at initial
  exact initial.symm.trans (invariant query before after reply)

private theorem observer_after (query : queries.Domain) (before after : State) (reply : queries.Range query) :
    observe query before reply (projection after) = observe query before reply after := by
  have initial := invariant query before (projection after) reply
  rw [same] at initial
  exact initial.symm.trans (invariant query before after reply)

/-- The original first-candidate monitor inherits both checked count-continuation laws from its actual callback. -/
theorem monitor (handler : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (query : queries.Domain) (good : Correct projection (handler query)) :
    Correct (view projection) (RegistrationNativeMldsaStop.monitor handler observe query) := by
  constructor
  · intro before
    have actual := congrArg (fun computation => (fun result =>
      (result.1, (result.2, before.2.orElse fun _ => observe query before.1 result.1 result.2))) <$> computation) (good.1 before.1)
    simp only [RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp,
      Functor.map_map, Prod.map, id_eq, view,
      observer_before projection same observe invariant, observer_after projection same observe invariant] at actual ⊢
    exact actual
  · intro before
    have actual := congrArg (fun computation => (fun result =>
      (result.1, (result.2, before.2.orElse fun _ => observe query before.1 result.1 result.2))) <$> computation) (good.2 before.1)
    simp only [RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp, transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, view,
      observer_before projection same observe invariant, observer_after projection same observe invariant] at actual ⊢
    exact actual

/-- Freezing at the first actual observed candidate preserves the same candidate and projected stopping snapshot under count normalization. -/
theorem freeze (handler : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (query : queries.Domain) (good : Correct projection (handler query)) :
    Correct (view projection) (RegistrationNativeMldsaStop.freeze handler observe defaultReply query) := by
  constructor
  · intro before
    rcases before with ⟨current, previous⟩
    cases previous with
    | none => exact (monitor projection same observe invariant handler query good).1 (current, none)
    | some candidate =>
        simp only [RegistrationNativeMldsaStop.freeze, StateT.run, map_pure, Prod.map, id_eq, view, same]
  · intro before
    rcases before with ⟨current, previous⟩
    cases previous with
    | none => exact (monitor projection same observe invariant handler query good).2 (current, none)
    | some candidate =>
        simp only [RegistrationNativeMldsaStop.freeze, StateT.run, transform, simulateQ_pure,
          map_pure, Prod.map, id_eq, view, same]

/-- Arbitrary adaptive stopped programs preserve exact projected state and their first selected candidate. -/
theorem program (handler : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (good : ∀ query, Correct projection (handler query)) (work : OracleComp queries Value) :
    Correct (view projection) (simulateQ (RegistrationNativeMldsaStop.freeze handler observe defaultReply) work) :=
  RegistrationNativeMldsaCountRules.simulate (view projection) (idempotent projection same) _
    (fun query => freeze projection same observe invariant handler defaultReply query (good query)) work

end Generic

/-- The actual native first-forgery observer and complete source callbacks instantiate the stopped count-normalization theorem. -/
theorem native {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Correct (view (RegistrationNativeMldsaMainView.project (n := n)))
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential)
        (RegistrationNativeMldsaTrialObserver.observe source.verify publicKey) defaultReply) work) :=
  program RegistrationNativeMldsaMainView.project RegistrationNativeMldsaMainView.idempotent
    (RegistrationNativeMldsaTrialObserver.observe source.verify publicKey)
    (fun query before after reply => RegistrationNativeMldsaTrialObserverView.observe_count source.verify publicKey query before after reply)
    _ defaultReply (RegistrationNativeMldsaCountRun.handler setup checks wire route representation created credential) work
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.monitor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.freeze' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.freeze

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop.native
