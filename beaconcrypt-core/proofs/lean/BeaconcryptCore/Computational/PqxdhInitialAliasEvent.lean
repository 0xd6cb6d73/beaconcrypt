import BeaconcryptCore.Computational.PqxdhInitialAliasBound

/-!
The initializer value-consistency comparison preserves a context-dependent final source observation of the entire original result and root cache. The hidden original32-byte root is sampled independently of the complete preparation and the shared64 response. Equal-byte known or nonselected cached/generated roots receive the same selected response in the right experiment. The source consumer supplies the actual full-state client and original initializer-count bound; no protocol event equality is assumed here.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialAliasEvent
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialAliasBound
variable {Context Result : Type}
variable (fixed : FixedHkdfSha512NoSaltSource)
  (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
  (event : Context → HmacBlock → (Result × RootOracle.QueryCache) → Bool)

noncomputable def decision (context : Context) (result : RootOutput × (HmacBlock × Trace Result)) : Bool :=
  event context result.2.1 (result.2.2.1, result.2.2.2.1)

noncomputable def leftGame (prior : ProbComp Context) : ProbComp Bool :=
  sampleCut prior >>= fun cut => decision event cut.1.1 <$> left fixed selected client cut

noncomputable def rightGame (prior : ProbComp Context) : ProbComp Bool :=
  sampleCut prior >>= fun cut => decision event cut.1.1 <$> right fixed selected client cut

noncomputable def sourceGame (prior : ProbComp Context) : ProbComp Bool := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  event context output <$> (simulateQ
    (PqxdhInitialRootLabelService.labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp)
      (selected context) (RawCtxSelectedInitialConstructor.response64 output)) (client context)).run ∅

/-- The ordinary final observation is computed from the literal labelled source client with all original result/cache fields; only the private candidate ledger is removed. -/
theorem point_source (context : Context) (output : HmacBlock) :
    (fun result : Trace Result => event context output (result.1, result.2.1)) <$>
      observed fixed selected client context output =
    event context output <$> (simulateQ
      (PqxdhInitialRootLabelService.labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp)
        (selected context) (RawCtxSelectedInitialConstructor.response64 output)) (client context)).run ∅ := by
  have same := congrArg (Functor.map (event context output))
    (PqxdhInitialRootAliases.trace_source fixed (selected context)
      (RawCtxSelectedInitialConstructor.response64 output) (client context) (∅, []))
  simpa only [observed, Functor.map_map, Prod.map_def, id_eq] using same

/-- Discarding the private earlier root preserves the complete source event distribution, after the whole client and shared64 response have been retained. -/
theorem left_source (prior : ProbComp Context) :
    𝒟[leftGame fixed selected client event prior] = 𝒟[sourceGame fixed selected client event prior] := by
  apply EvalDistEq.evalDist_eq
  simp only [leftGame, sampleCut, left, decision, Functor.map_map, bind_assoc, pure_bind]
  simp only [point_source]
  refine EvalDistEq.bind_right prior fun context => ?_
  exact OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _

/-- The same source event differs from its value-consistent private initializer by at most one independent-root guess for each actual initializer query, while every public HKDF evaluation remains real. -/
theorem bound (prior : ProbComp Context) (qInitial : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP PqxdhInitialRootAliases.IsInitializer qInitial) :
    (sourceGame fixed selected client event prior).boolDistAdvantage
      (rightGame fixed selected client event prior) ≤ ((qInitial : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
  have mixture := PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind (sampleCut prior)
    (fun cut => decision event cut.1.1 <$> left fixed selected client cut)
    (fun cut => decision event cut.1.1 <$> right fixed selected client cut)
    (left fixed selected client) (fun result => result.1 ∈ result.2.2.2.2)
    (fun cut => (tvDist_map_le (decision event cut.1.1) _ _).trans (pointwise fixed selected client cut))
  have tv : tvDist (leftGame fixed selected client event prior) (rightGame fixed selected client event prior) ≤
      ((qInitial : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
    apply mixture.trans
    apply ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num)))
    exact candidates_bound fixed selected client prior qInitial bounded
  have erased := left_source fixed selected client event prior
  simpa only [ProbComp.boolDistAdvantage, ← erased, VCVioLegacy.evalDist_singleton_eq_probOutput] using
    (abs_probOutput_toReal_sub_le_tvDist _ _).trans tv

end BeaconcryptCore.Computational.PqxdhInitialAliasEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasEvent.point_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasEvent.point_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasEvent.left_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasEvent.left_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasEvent.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasEvent.bound
