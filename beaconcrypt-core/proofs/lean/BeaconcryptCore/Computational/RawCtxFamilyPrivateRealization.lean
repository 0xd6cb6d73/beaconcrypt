import BeaconcryptCore.Computational.RawCtxPendingChildRealization
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization

/-!
The actual privately patched complete family interpreter is the exact old private-query interface used by the candidate and freshness games. The original owner-tagged reads erase only that private tag while keeping their full source history. Public HKDF remains real. Candidate/disclosure instrumentation can be projected only after the complete execution, preserving the original result and shared primitive state. No callback realization or freshness equivalence is assumed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization
open RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedParentPrivatePatch
open RawCtxSelectedParentCalls RawCtxSelectedParentFamilyMap RawCtxSelectedChain
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {A Result : Type} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
/-- The complete patched family handler is the actual private alias-consistent handler composed with the original family query compiler. -/
theorem handler_patch (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (separate : targetAddress target ≠ entry.address) :
    labelLive (A := A) (S := S) (B := B) source writer (privatePatch prior target output) entry target =
      RawCtxSelectedParentPrivate.handler source writer prior entry output
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))
        (RawCtxSelectedParentPrivateRealization.realView source) target ∘ₛ RawCtxFamilyPendingCompiler.live := by
  funext query
  unfold labelLive
  rw [child_response prior entry target output separate]
  cases query with
  | inl primitive =>
      have original := congrFun (RawCtxSelectedParentPrivateRealization.live_patch (Auxiliary := A) source writer prior entry target output
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) separate) (.inl primitive)
      simpa only [RawCtxSelectedParentCompiler.live, RawCtxGenericLiveRead.handler,
        RawCtxPendingFamilyLiveQueries.handler, QueryImpl.compose, RawCtxFamilyPendingCompiler.live,
        RawCtxFamilyPendingCompiler.primitive, RawCtxPendingLiveQueries.erase,
        RawCtxSelectedLiveCompiler.primitiveForward, QueryImpl.simulateQ_compose, simulateQ_spec_query] using original
  | inr input =>
      rcases input with ⟨request, kernel⟩
      cases request <;> cases kernel <;>
        simp [RawCtxPendingFamilyLiveQueries.handler, QueryImpl.compose, RawCtxFamilyPendingCompiler.live,
          RawCtxFamilyReadCompiler.compiler, OracleSpec.query,
          RawCtxSelectedParentPrivate.read_same, RawCtxGenericFamilyRead.nativeReader]
      all_goals rfl

/-- Erasing only the private candidate list and exposure flag after the complete adaptive program retains every original result and shared primitive effect. -/
theorem observed_project (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (client : OracleComp RawCtxSelectedLiveCompiler.Spec Result)
    (state : RawCtxSelectedParentLive.State A) :
    Prod.map id (fun final => final.1.1) <$>
      (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))
        (RawCtxSelectedParentPrivateRealization.realView source) target) client).run state =
      (simulateQ (RawCtxSelectedParentPrivate.handler source writer prior entry output
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))
        (RawCtxSelectedParentPrivateRealization.realView source) target) client).run state.1.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query before
  simp [RawCtxSelectedParentPrivate.observed, RawCtxFlaggedQueryTrace.trace, StateT.run]

/-- The complete privately patched family execution is the literal projection of the candidate-instrumented old-interface execution; the family and source history remain in the returned result. -/
theorem program_patch (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (separate : targetAddress target ≠ entry.address)
    (client : OracleComp (RawCtxPendingFamilyLiveQueries.Spec Slot S B) Result)
    (state : RawCtxSelectedParentLive.State A) :
    (simulateQ (labelLive source writer (privatePatch prior target output) entry target) client).run state.1.1 =
      Prod.map id (fun final => final.1.1) <$>
        (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))
          (RawCtxSelectedParentPrivateRealization.realView source) target)
          (simulateQ RawCtxFamilyPendingCompiler.live client)).run state := by
  rw [observed_project, handler_patch source writer prior entry target output separate,
    QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.handler_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.handler_patch

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.observed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.observed_project

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.program_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrivateRealization.program_patch
