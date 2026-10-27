import BeaconcryptCore.Computational.PqxdhInitialSelectedBeacon
import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-!
The target-free known/selected initializer reply is constructed from the actual coordinate-labelled shared root cache. Selected coordinates reuse the same orientation and opposite half; known inputs and every nonselected cached or freshly drawn root retain the actual source64 prefix. Native response reconstruction recovers the entire labelled service and adaptive source client with the same root cache. No cache independence or coordinate injectivity is assumed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSelectedService
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdf PqxdhJointKdfGame
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhCorrelatedExtractFamily
open PqxdhInitialRootLabelService PqxdhInitialSelectedBeacon
variable {Result : Type}

noncomputable def known (fixed : FixedHkdfSha512NoSaltSource) (root : RootOutput) : InitialValue :=
  .inl (initialPrefix (productionStream fixed.crypto (FixedHkdfDomain.ratchet.address root.toList)))

noncomputable def value (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other : RootOutput) :
    Request → StateT RootOracle.QueryCache ProbComp InitialValue
  | .known root => pure (known fixed root)
  | .family message =>
      if message = selected then pure (.inr (second, other)) else do
        let root ← uniformImpl (.inr message)
        pure (known fixed root)

/-- Every known root keeps exactly the original real64-byte response. -/
theorem known_response (fixed : FixedHkdfSha512NoSaltSource) (root target : RootOutput) :
    response target (known fixed root) = realInitial fixed root :=
  (PqxdhInitialCurrentSecrecy.response_prefix fixed root).symm

/-- The private selected-half reply reconstructs the actual labelled service, including every cached or fresh nonselected root and the complete shared root cache. -/
theorem value_response (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other target : RootOutput) (query : Request) :
    response target <$> value fixed selected second other query =
      labelled fixed selected
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)) query := by
  cases query with
  | known root => simp only [value, labelled, map_pure, known_response]
  | family message =>
      simp only [value, labelled]
      split
      · rfl
      · simp only [native, map_bind, map_pure, known_response]
        rfl

noncomputable def reconstructed (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other target : RootOutput) :
    QueryImpl PqxdhInitialLabelCompiler.Spec (StateT RootOracle.QueryCache ProbComp)
  | .inl coin => (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RootOracle.QueryCache ProbComp) coin
  | .inr query => response target <$> value fixed selected second other query

/-- The full source interface keeps all ordinary coin callbacks and the same coordinate-labelled initializer/cache service. -/
theorem full_handler (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other target : RootOutput) :
    reconstructed fixed selected second other target =
      labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)) := by
  funext query
  cases query with
  | inl coin => rfl
  | inr query => exact value_response fixed selected second other target query

/-- Every original adaptive labelled client retains its exact result and entire final root cache under the target-free service representation. -/
theorem full_source (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other target : RootOutput)
    (client : OracleComp PqxdhInitialLabelCompiler.Spec Result) (cache : RootOracle.QueryCache) :
    (simulateQ (reconstructed fixed selected second other target) client).run cache =
      (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target))) client).run cache := by
  rw [full_handler]

noncomputable def service (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    StateT RootOracle.QueryCache ProbComp (Option InitialValue) :=
  some <$> value fixed selected second other (PqxdhInitialRootLabelBridge.request fixed secrets)

/-- The exact original compiled Beacon initializer request selects the same known/family coordinate, preserves its cache and returns the same optional response. -/
theorem service_response (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other target : RootOutput)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Option.map (response target) <$> service fixed selected second other secrets =
      some <$> labelled fixed selected
        (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target))
        (PqxdhInitialRootLabelBridge.request fixed secrets) := by
  rw [← value_response fixed selected second other target]
  simp only [service, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target-free service pays the actual source sampling bill: selected and known requests are pure, and only a fresh nonselected coordinate draws32 bytes. -/
theorem value_uniform (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (second : Bool) (other : RootOutput) (query : Request) (cache : RootOracle.QueryCache) :
    ((value fixed selected second other query).run cache).IsTotalQueryBound 32 := by
  cases query with
  | known root => trivial
  | family message =>
      by_cases same : message = selected
      · simp only [value, same, ite_true, StateT.run_pure]
        trivial
      · simp only [value, same, ite_false]
        change (do let result ← (uniformImpl (.inr message)).run cache
                   pure (known fixed result.1, result.2)).IsTotalQueryBound 32
        cases found : cache message with
        | some root =>
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_some _ found, pure_bind]
            trivial
        | none =>
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_none _ found, uniformSampleImpl, bind_pure_comp,
              IsTotalQueryBound, isQueryBound_map_iff]
            exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

end BeaconcryptCore.Computational.PqxdhInitialSelectedService
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.known_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.known_response
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.value_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.value_response
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.full_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.full_handler
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.full_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.service_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.service_response
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedService.value_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedService.value_uniform
