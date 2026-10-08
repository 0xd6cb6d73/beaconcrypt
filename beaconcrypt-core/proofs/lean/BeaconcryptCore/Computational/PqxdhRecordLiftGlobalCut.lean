-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFirstLookup
import BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask
import BeaconcryptCore.Computational.LazyOracleDiscard

/-! Factor the first actual ideal parent miss and its full global continuation through the selected-input mask. The source primitive/cache/seed/log state is retained with its literal one KDF and 76 uniform costs. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol
open PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhJointKdfGame
variable {n : Nat} {Result : Type}

/-- The actual source miss increments its own native KDF ledger once and uniform ledger by 76, without changing any shared cache or effect counter. -/
def missPrimitive (primitive : PqxdhRecordLiftWorld.Primitive) : PqxdhRecordLiftWorld.Primitive :=
  ({ (PqxdhRecordLiftChainOracle.charge primitive).1 with uniform := primitive.1.uniform + 76 }, primitive.2)

def install (secret : Private n) (target : PqxdhRecordLiftWorldCompiler.Label n)
    (output : FullOutput) : Private n :=
  { secret with chain := secret.chain.cacheQuery target output, primitive := missPrimitive secret.primitive }

/-- The literal first ideal lookup installs one complete correlated 76 reply and preserves every other global private field. -/
theorem lookup_miss {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n) (secret : Private n)
    (selected : ideal target = true) (missing : secret.chain target = none) :
    (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec (.lookup target)).run secret =
      (fun output => ((), install secret target output)) <$> ($ᵗ FullOutput) := by
  simp only [interpreter, withRecord, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
    StateT.run, bind_pure_comp]
  change (fun result => (result.1, putRecord secret result.2)) <$>
    (((fun _ => ()) <$> PqxdhRecordLiftLoggedAdapters.liftLookup
      (PqxdhRecordLiftChainOracle.lookup source (cachedSeeds secret) ideal) target :
      StateT (RecordState n) ProbComp Unit).run (recordState secret)) = _
  rw [StateT.run_map]
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, recordState, Functor.map_map]
  have missed := PqxdhRecordLiftChainOracle.lookup_miss source (cachedSeeds secret) ideal target
    (secret.chain, secret.primitive) selected missing
  simp only [StateT.run] at missed
  rw [missed]
  simp only [Functor.map_map, putRecord, install, missPrimitive]

/-- Mask only the new parent's next32. The cut-local lookup/draw counters start at zero and record this one selected miss; the actual global counters stay separately and exactly in primitive. -/
def prepare (secret : Private n) (target : PqxdhRecordLiftWorldCompiler.Label n)
    (value : PqxdhRecordLiftProjectionCut.Retained) : PqxdhRecordLiftGlobalMask.State n :=
  ⟨PqxdhRecordLiftProjectionCut.mask (secret.chain, ⟨0, 0⟩) target value,
    missPrimitive secret.primitive, secret.seeds, secret.produced, secret.pending⟩

/-- Rejoining the retained 44 and fresh hidden32 recovers the entire actual post-miss source state, including its numerical primitive ledger. -/
theorem prepare_realize (secret : Private n) (target : PqxdhRecordLiftWorldCompiler.Label n)
    (output : FullOutput) :
    PqxdhRecordLiftGlobalMask.realize (PqxdhRecordLiftProjectionCut.secret .chain output)
      (prepare secret target (PqxdhRecordLiftProjectionCut.retained .chain output)) =
        install secret target output := by
  simp only [prepare, PqxdhRecordLiftGlobalMask.realize, PqxdhRecordLiftMaskedOracle.table,
    PqxdhRecordLiftProjectionCut.realize, PqxdhRecordLiftProjectionCut.mask,
    PqxdhRecordLiftProjectionCut.restore_split, install]

/-- The first actual parent miss has the split uniform32 distribution under every complete global continuation, retaining all other 44 bytes and all source state and counters. -/
theorem miss_continuation {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n) (state : Private n)
    (selected : ideal target = true) (missing : state.chain target = none)
    (continuation : Unit × Private n → ProbComp Result) :
    LazyOracleDiscard.LawEq
      ((interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec (.lookup target)).run state >>=
        continuation)
      (do let value ← $ᵗ PqxdhRecordLiftProjectionCut.Retained
          let hidden ← $ᵗ RootOutput
          continuation ((), PqxdhRecordLiftGlobalMask.realize hidden (prepare state target value))) := by
  rw [lookup_miss source ideal setup codec target state selected missing, bind_map_left]
  intro Observed _ observe
  simp only [bind_assoc]
  apply evalDist_eq_of_evalSPMF_eq
  simpa only [prepare_realize] using PqxdhRecordLiftProjectionCut.split_continuation .chain
    (fun value hidden => continuation ((), PqxdhRecordLiftGlobalMask.realize hidden (prepare state target value)) >>= observe)

/-- Split the actual fresh parent only if the source prefix reaches it. An execution that finishes early retains its original state and performs no parent draw. -/
noncomputable def splitRun {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) : ProbComp (Result × Private n) := do
  let reached ← PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client
  match reached.val.1 with
  | .complete result => pure (result, reached.val.2)
  | .pending next => do
      let value ← $ᵗ PqxdhRecordLiftProjectionCut.Retained
      let hidden ← $ᵗ RootOutput
      (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
        (next ())).run (PqxdhRecordLiftGlobalMask.realize hidden (prepare reached.val.2 target value))

/-- Every actual source execution supplies the fresh parent input at its derived first miss, under the complete adaptive continuation and full private state. -/
theorem source_split {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (selected : ideal target = true) :
    LazyOracleDiscard.LawEq
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run initialPrivate)
      (splitRun source ideal setup codec target client) := by
  rw [← PqxdhRecordLiftFirstLookup.resume_prefix source ideal setup codec target client]
  unfold splitRun
  apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
  intro reached
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [PqxdhRecordLiftFirstLookup.finish, simulateQ_pure, StateT.run_pure]
      exact LazyOracleDiscard.LawEq.refl _
  | pending next =>
      simp only [PqxdhRecordLiftFirstLookup.finish, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact miss_continuation source ideal setup codec target reached.val.2 selected reached.property
        (fun result => (simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
          (next result.1)).run result.2)

/-- A final or later continuation receives the original client result (which may retain the whole environment/control/ledger), actual shared ROM and frame logs. Hidden tables, seeds and private instrumentation are not exposed by this continuation interface; their source/reduction bills remain separate obligations. -/
abbrev Observer (Result : Type) := Result → CtxRomAuth.CtxRO.QueryCache →
  List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) →
  List PqxdhDeploymentNative.Frame → ProbComp Bool

def observe (finish : Observer Result) (result : Result × Private n) : ProbComp Bool :=
  finish result.1 result.2.primitive.2 result.2.produced result.2.pending

def observeMasked (finish : Observer Result)
    (result : Result × PqxdhRecordLiftGlobalMask.State n) : ProbComp Bool :=
  finish result.1 result.2.primitive.2 result.2.produced result.2.pending

/-- The actual complete suffix and permitted later continuation need the unavailable parent32 only through the supplied child derivation. Source state and work are first preserved by the whole-state realization, then projected explicitly for this observer. -/
theorem continuation_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalMask.State n)
    (hidden : RootOutput) (selected : ideal state.masked.coordinate = true) (finish : Observer Result) :
    ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run
      (PqxdhRecordLiftGlobalMask.realize hidden state) >>= observe finish) =
    ((simulateQ (PqxdhRecordLiftGlobalMask.interpreter source ideal
      (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec) client).run
      state >>= observeMasked finish) := by
  rw [← PqxdhRecordLiftGlobalMask.schedule_realization source ideal hidden setup codec client state selected,
    bind_map_left]
  rfl

abbrev Context (n : Nat) (Result : Type) := PqxdhRecordLiftFirstLookup.Cut n Result × Private n

/-- The primitive reduction samples the actual complete prefix before either fresh projection. Its miss proof is derived, and its auxiliary cut-local counts start at zero. -/
noncomputable def parentSample {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) :
    ProbComp (Context n Result × PqxdhRecordLiftProjectionCut.AtMiss (Slot n)) := do
  let reached ← PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client
  pure (reached.val, ⟨(target, (reached.val.2.chain, ⟨0, 0⟩)), reached.property⟩)

/-- The actual suffix, including any later environment continuation, gets the supplied full child output but never the selected parent next32. An unused source cut ignores both the child and the extra primitive-game parent draw. -/
noncomputable def parentObserver {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (finish : Observer Result) :
    FullObserver (Context n Result × PqxdhRecordLiftProjectionCut.Mask (Slot n)) := fun input child =>
  match input.1.1 with
  | .complete result => observe finish (result, input.1.2)
  | .pending next =>
      (simulateQ (PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec) (next ())).run
        ⟨input.2, missPrimitive input.1.2.primitive, input.1.2.seeds, input.1.2.produced, input.1.2.pending⟩ >>=
          observeMasked finish

/-- After the actual reached miss is split, the full source continuation is exactly the constructed target-free primitive observer. -/
theorem split_observer {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n) (state : Private n)
    (next : Unit → OracleComp (ServiceSpec n) Result)
    (value : PqxdhRecordLiftProjectionCut.Retained) (hidden : RootOutput)
    (selected : ideal target = true) (finish : Observer Result) :
    ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (next ())).run
      (PqxdhRecordLiftGlobalMask.realize hidden (prepare state target value)) >>= observe finish) =
    parentObserver source ideal setup codec finish
      ((.pending next, state), PqxdhRecordLiftProjectionCut.mask (state.chain, ⟨0, 0⟩) target value)
      (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)) :=
  continuation_source source ideal setup codec (next ()) (prepare state target value) hidden selected finish

/-- Splitting one independent full 76 draw is valid under every complete measurable continuation. -/
theorem full_split_law {X : Type} (continuation : PqxdhRecordLiftProjectionCut.Retained → RootOutput → ProbComp X) :
    LazyOracleDiscard.LawEq
      (do let output ← $ᵗ FullOutput
          continuation (PqxdhRecordLiftProjectionCut.retained .chain output)
            (PqxdhRecordLiftProjectionCut.secret .chain output))
      (do let value ← $ᵗ PqxdhRecordLiftProjectionCut.Retained
          let hidden ← $ᵗ RootOutput
          continuation value hidden) := by
  intro Observed _ observe
  apply evalDist_eq_of_evalSPMF_eq
  simpa only [bind_assoc] using PqxdhRecordLiftProjectionCut.split_continuation .chain
    (fun value hidden => continuation value hidden >>= observe)

/-- The actual source experiment, including an unused cut, supplies the exact sampler and target-free observer of the full secret-input component. -/
theorem observed_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (selected : ideal target = true) (finish : Observer Result) :
    LazyOracleDiscard.LawEq
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run initialPrivate >>=
        observe finish)
      (PqxdhRecordLiftProjectionCut.childReal source (parentSample source ideal setup codec target client)
        (parentObserver source ideal setup codec finish)) := by
  apply ((source_split source ideal setup codec target client selected).bind
    (fun result => LazyOracleDiscard.LawEq.refl (observe finish result))).trans
  simp only [splitRun, PqxdhRecordLiftProjectionCut.childReal, parentSample, bind_assoc, pure_bind]
  apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
  intro reached
  rw [PqxdhRecordLiftLazyTable.run_miss target (reached.val.2.chain, ⟨0, 0⟩) reached.property, bind_map_left]
  cases stopped : reached.val.1 with
  | complete result =>
      simpa only [parentObserver, stopped, pure_bind] using
        (LazyOracleDiscard.lawEq_drop ($ᵗ FullOutput) (observe finish (result, reached.val.2))).symm
  | pending next =>
      simp only [bind_assoc]
      simp_rw [split_observer source ideal setup codec target reached.val.2 next _ _ selected finish]
      simpa only [parentObserver, stopped] using (full_split_law (fun value hidden =>
        parentObserver source ideal setup codec finish
          ((.pending next, reached.val.2), PqxdhRecordLiftProjectionCut.mask (reached.val.2.chain, ⟨0, 0⟩) target value)
          (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)))).symm

/-- The explicit primitive observer samples the actual source prefix, retains its correlated 44 bytes and resumes the original global continuation. -/
noncomputable def reductionObserver {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (finish : Observer Result) : FullObserver Unit :=
  PqxdhRecordLiftProjectionCut.unitObserver (parentSample source ideal setup codec target client)
    (parentObserver source ideal setup codec finish)

/-- Coefficient-one reduction of the actual observed execution to a supplied independent child, using only the ordinary uniform32 Extract endpoint and the full two-block HMAC reduction. Identifying the independent endpoint with an adjacent source policy and deriving global query caps are separate obligations. -/
theorem observed_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (selected : ideal target = true) (finish : Observer Result) :
    (((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run initialPrivate >>=
      observe finish)).boolDistAdvantage
      (PqxdhRecordLiftProjectionCut.childUniform (parentSample source ideal setup codec target client)
        (parentObserver source ideal setup codec finish)) ≤
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (reductionObserver source ideal setup codec target client finish))).boolDistAdvantage
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (reductionObserver source ideal setup codec target client finish))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish))).boolDistAdvantage
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish))) := by
  have actual := (observed_source source ideal setup codec target client selected finish).evalDist_eq
  simpa only [ProbComp.boolDistAdvantage, actual, reductionObserver] using
    PqxdhRecordLiftProjectionCut.child_bound source hmac correct
      (parentSample source ideal setup codec target client) (parentObserver source ideal setup codec finish)

/-- The constructed observer pays for every prefix draw, the retained 44 and the entire supported suffix. A suffix budget is needed only at cuts produced by this exact source execution, not at invented continuations. -/
theorem reductionObserver_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (finish : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client),
      ∀ value child, (parentObserver source ideal setup codec finish
        (reached.val, PqxdhRecordLiftProjectionCut.mask (reached.val.2.chain, ⟨0, 0⟩) target value)
        child).IsTotalQueryBound qSuffix)
    (context : Unit) (output : FullOutput) :
    (reductionObserver source ideal setup codec target client finish context output).IsTotalQueryBound
      (qPrefix + (44 + qSuffix)) := by
  simp only [reductionObserver, PqxdhRecordLiftProjectionCut.unitObserver,
    PqxdhRecordLiftProjectionCut.retainedContext, parentSample, bind_assoc, pure_bind]
  exact isTotalQueryBound_bind_of_mem_support prefixBound (fun reached supported =>
    isTotalQueryBound_bind PqxdhOrderedChainHybrids.material_uniform_query_bound
      (fun value => suffixBound reached supported value output))

/-- The explicit HMAC reduction makes at most two challenge queries; all ordinary randomness of the source prefix, retained 44, suffix and uniform32 input remains in its separate cap. -/
theorem reduction_bounds {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (finish : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client),
      ∀ value child, (parentObserver source ideal setup codec finish
        (reached.val, PqxdhRecordLiftProjectionCut.mask (reached.val.2.chain, ⟨0, 0⟩) target value)
        child).IsTotalQueryBound qSuffix) :
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish)).IsQueryBoundP IsHmacUniformQuery
        (32 + (qPrefix + (44 + qSuffix))) := by
  refine ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ ?_
      (reductionObserver_bound source ideal setup codec target client finish qPrefix qSuffix prefixBound suffixBound)⟩
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)

/-- All four primitive challenger worlds retain the exact prefix/suffix cap and charge complete 64-byte HMAC answers, even though the final block contributes only 12 bytes. -/
theorem challenger_bounds {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : PqxdhRecordLiftWorldCompiler.Label n)
    (client : OracleComp (ServiceSpec n) Result) (finish : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (PqxdhRecordLiftFirstLookup.sampledPrefix source ideal setup codec target client),
      ∀ value child, (parentObserver source ideal setup codec finish
        (reached.val, PqxdhRecordLiftProjectionCut.mask (reached.val.2.chain, ⟨0, 0⟩) target value)
        child).IsTotalQueryBound qSuffix) :
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (reductionObserver source ideal setup codec target client finish))).IsTotalQueryBound
        (32 + (qPrefix + (44 + qSuffix))) ∧
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (reductionObserver source ideal setup codec target client finish))).IsTotalQueryBound
        (32 + (64 + (qPrefix + (44 + qSuffix)))) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish))).IsTotalQueryBound
        (64 + (32 + (qPrefix + (44 + qSuffix)))) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal setup codec target client finish))).IsTotalQueryBound
        (32 + (64 + (64 + (qPrefix + (44 + qSuffix))))) := by
  have inputBound : PqxdhServerAuthKeySchedule.uniform32.IsTotalQueryBound 32 :=
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)
  have observerBound := reductionObserver_bound source ideal setup codec target client finish
    qPrefix qSuffix prefixBound suffixBound
  exact ⟨isTotalQueryBound_bind inputBound (fun pair => observerBound pair.1 _),
    fullExtractUniform_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ inputBound observerBound⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.lookup_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.lookup_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.prepare_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.prepare_realize

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.miss_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.miss_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.source_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.source_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.continuation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.split_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.split_observer

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.full_split_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.full_split_law

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.observed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.observed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.observed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.reductionObserver_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.reductionObserver_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut.challenger_bounds
