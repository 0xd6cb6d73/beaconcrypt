import BeaconcryptCore.Computational.PqxdhInitialPostInterpretation
import BeaconcryptCore.Computational.PqxdhInitialSelectedRecords

/-!
Actual record and public operations evaluate in the same root-cache monad as Beacon initialization. Their original randomness does not touch that cache. The exact retained-parent record interpretation is lifted with the whole cache and every protocol field intact, without changing its source sampler or pretending ambient work is free.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords
open PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService
variable {ι State Result : Type} {spec : OracleSpec ι}

noncomputable def lift (handler : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl spec (StateT State (StateT RootOracle.QueryCache ProbComp)) :=
  fun query state cache => (fun result => (result, cache)) <$> (handler query).run state

/-- Every original ordinary computation retains its whole result and leaves the shared initializer root cache untouched. -/
theorem coins (fixed : FixedHkdfSha512NoSaltSource) (selected : Message) (response : Response)
    (computation : ProbComp Result) (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialLabelCompiler.coins computation)).run cache =
      (fun result => (result, cache)) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      change (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
        (PqxdhInitialLabelCompiler.Spec.query (.inl query) >>= fun answer => PqxdhInitialLabelCompiler.coins (next answer))).run cache = _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (do
        let answer ← (unifSpec.query query : ProbComp _)
        (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
          (PqxdhInitialLabelCompiler.coins (next answer))).run cache) = _
      simp only [ih, map_bind]

/-- The evaluated actual current record handler retains every source operation and complete root cache in exactly this lift. -/
theorem records_source {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (selected : Message) (response : Response) :
    (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response).mapStateTBase
      (PqxdhInitialCurrentPost.records (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)
        fixed writer kdf sender route decode) =
      lift (PqxdhInitialPrivateKdf.records fixed writer kdf sender route decode) := by
  funext query state cache
  exact coins fixed selected response _ cache

set_option backward.isDefEq.respectTransparency false in
/-- The concrete selected record equation retains the same complete initializer cache as the actual evaluated post scheduler. -/
theorem selected_record {M P I D K A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : PqxdhInitialGenericProtocol.State RawCtxSelectedChain.Kernel M P I D K A S B) :
    (lift (PqxdhInitialPrivateKdf.records source writer
      (PqxdhInitialGenericProtocolBuilder.retainedKdf prior entry target) sender route decode) query).run
      (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state) =
      Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (lift (PqxdhInitialGenericRecords.records
          (RawCtxSelectedParentCalls.labelCalls source writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
          (PqxdhInitialSelectedRecords.backend source writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
          sender route decode) query).run state := by
  funext cache
  change _ = (Prod.map id
    (PqxdhInitialGenericProtocol.native
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
    (lift (PqxdhInitialGenericRecords.records
      (RawCtxSelectedParentCalls.labelCalls source writer prior entry
        (RawCtxSelectedParentCalls.childResponse prior entry target))
      (PqxdhInitialSelectedRecords.backend source writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
      (RawCtxGenericFamilyRead.nativeReader
        (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
      sender route decode) query).run state).run cache
  rw [StateT.run_map]
  simp only [lift, StateT.run]
  have direct := PqxdhInitialSelectedRecords.record source writer prior entry target sender route decode query state
  simp only [StateT.run] at direct
  rw [direct]
  let reify := PqxdhInitialGenericProtocol.native (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
    (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))
  let execution := (PqxdhInitialGenericRecords.records
    (RawCtxSelectedParentCalls.labelCalls source writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
    (PqxdhInitialSelectedRecords.backend source writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
    sender route decode query).run state
  change (fun result => (result, cache)) <$> (Prod.map id reify <$> execution) =
    (fun result => (Prod.map id reify result.1, result.2)) <$> ((fun result => (result, cache)) <$> execution)
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.coins

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.records_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.records_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.selected_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords.selected_record
