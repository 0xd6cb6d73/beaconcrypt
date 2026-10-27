import BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion
import BeaconcryptCore.Computational.PqxdhSharedParentCollect
import BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds

/-!
Cached parent cuts execute their original saved continuation and final publication/freshness decision. Completing missing cuts gives the literal full source program, so its actual callback budget bounds the whole prepared prefix, including cached continuations. This accounting does not use equality of evaluated distributions or posit a budget for an opaque observer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhSharedParentResources
open PqxdhNativeSharedPrefix PqxdhNativeSharedContinuation
open CtxRomAuth AdaptiveCtxSharedHash PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand
variable {ι M P I D K X Response Shared A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeAuditCarried.Execution extra M P I D K Bool Bool S B)

/-- The source prefix and its exact saved continuation execute the full original audited oracle program. -/
theorem carried_finish (depth stage : Nat) (state : Local A N RootOracle.QueryCache) :
    (carried source writer stage pre application initial selector aux mark sender route decode execution depth state >>=
      finish source writer stage pre application initial selector aux mark sender route decode) =
    (simulateQ (compiler source writer stage pre application initial selector aux)
      (simulateQ RawCtxForwardAnnotation.erase (PqxdhInitialNativeCarried.code source mark sender route decode execution))).run state := by
  have complete := RawCtxSharedPrefixCompletion.scan_finish
    PqxdhInitialForwardPost.selected (PqxdhNativeSharedPrefix.selected depth)
    (fun query state chosen => native_selection depth query (attach state ∅) chosen)
    (compiler source writer stage pre application initial selector aux)
    (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
    (PqxdhInitialNativeCarried.code source mark sender route decode execution)
    (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
      execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace)
    (PqxdhInitialOriginForwardBuilder.program_sound source mark execution.origin sender route decode
      execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state
  have sameFinish : finish (P := P) (Result := Bool) (S := S) (B := B) source writer stage pre application initial selector aux mark sender route decode =
      RawCtxSharedPrefixCompletion.finish (compiler source writer stage pre application initial selector aux)
        (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) := by
    funext cut
    cases cut <;> rfl
  rw [sameFinish]
  exact complete

variable (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

noncomputable def resume (stage : Nat) :
    Bool ⊕ PqxdhSharedParentCollect.Pending extra M P I D K A N RootOracle.QueryCache S B → OracleComp HashSpec Bool
  | .inl decision => pure decision
  | .inr (context, state) =>
      PqxdhSharedParentCollect.decision source root selected number ancestors disclosed <$>
        finish source writer stage pre application initial selector aux mark sender route decode (.pending context state)

/-- Cached and completed branches already contain the original decision; resuming only the missing branch recovers the same full source execution. -/
theorem collect_finish (depth : Nat)
    (cut : Carried extra M P I D K Bool Bool A N RootOracle.QueryCache S B) :
    (PqxdhSharedParentCollect.collect source writer pre application initial selector aux mark sender route decode
      root selected number ancestors disclosed depth cut >>=
      resume source writer pre application initial selector aux mark sender route decode root selected number ancestors disclosed (depth + 1)) =
    PqxdhSharedParentCollect.decision source root selected number ancestors disclosed <$>
      finish source writer (depth + 1) pre application initial selector aux mark sender route decode cut := by
  classical
  cases cut with
  | complete result state => rfl
  | pending context state =>
    simp only [PqxdhSharedParentCollect.collect]
    split <;> simp [resume]

/-- Completing only the missing output of the actual shared sampler gives its full original oracle program and final decision. -/
theorem prepared_finish (depth : Nat) (state : Local A N RootOracle.QueryCache) :
    ((carried source writer (depth + 1) pre application initial selector aux mark sender route decode execution depth state >>=
      PqxdhSharedParentCollect.collect source writer pre application initial selector aux mark sender route decode
        root selected number ancestors disclosed depth) >>=
      resume source writer pre application initial selector aux mark sender route decode root selected number ancestors disclosed (depth + 1)) =
    PqxdhSharedParentCollect.decision source root selected number ancestors disclosed <$>
      (simulateQ (compiler source writer (depth + 1) pre application initial selector aux)
        (simulateQ RawCtxForwardAnnotation.erase (PqxdhInitialNativeCarried.code source mark sender route decode execution))).run state := by
  rw [bind_assoc]
  simp only [collect_finish]
  rw [← map_bind, carried_finish]

/-- The complete prefix, including cached continuations, pays the actual seven builder callbacks and at most 67 callbacks per original adaptive post request. Each callback pays its source-local cost or76-byte draw, and hashes are counted separately even on hits. -/
theorem prepared_bound (depth qPost qPre qApplication qInitial qSelector qAux : Nat)
    (preBound : ∀ query state, ((pre query).run state).IsTotalQueryBound qPre)
    (applicationBound : ∀ query state, ((application query).run state).IsTotalQueryBound qApplication)
    (initialBound : ∀ query state, ((initial query).run state).IsTotalQueryBound qInitial)
    (selectorBound : ∀ query state, ((selector query).run state).IsTotalQueryBound qSelector)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (postBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (hash : Bool) (state : Local A N RootOracle.QueryCache) :
    (carried source writer (depth + 1) pre application initial selector aux mark sender route decode execution depth state >>=
      PqxdhSharedParentCollect.collect source writer pre application initial selector aux mark sender route decode
        root selected number ancestors disclosed depth).IsQueryBoundP (HashClass hash)
      ((7 + qPost * 67) * (if hash then 1 else 76 + qPre + qApplication + qInitial + qSelector + qAux)) := by
  apply RawCtxSharedPrefixCompletion.prefix_bound _
    (resume source writer pre application initial selector aux mark sender route decode root selected number ancestors disclosed (depth + 1))
  rw [prepared_finish, isQueryBoundP_map_iff]
  apply PqxdhBeaconPhase2Bounds.interpreted_total_bound
  · exact PqxdhNativeSharedPrefixBounds.step_bound source writer (depth + 1) pre application initial selector aux
      qPre qApplication qInitial qSelector qAux preBound applicationBound initialBound selectorBound auxBound hash
  · exact (RawCtxSharedPrefixBounds.annotation_total _ _).mpr
      (PqxdhNativeSharedPrefixBounds.code_total source mark sender route decode execution qPost postBound)

end BeaconcryptCore.Computational.PqxdhSharedParentResources

/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentResources.carried_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentResources.carried_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentResources.collect_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentResources.collect_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentResources.prepared_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentResources.prepared_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentResources.prepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentResources.prepared_bound
