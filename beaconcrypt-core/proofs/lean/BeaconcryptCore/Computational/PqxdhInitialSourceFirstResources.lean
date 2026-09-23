import BeaconcryptCore.Computational.PqxdhInitialSourceFirstSecrecy
import BeaconcryptCore.Computational.PqxdhInitialHalfResources
import BeaconcryptCore.Computational.RawCtxSupportedSample

/-!
The common preparation sampler carries proof-only support certificates through unchanged syntax. Consequently finite source callback bounds are needed only for inputs that can actually be prepared. They construct the first-hop main/tester reductions and their concrete full-source candidate and query allowances, without a whole-observer security premise or conditioning loss.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy (Input Context)
open PqxdhInitialHalfResources RawCtxSelectedParentEntry
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

structure Caps (input : Input extra M P I D K X Response A N S B)
    (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat) : Prop where
  postBound : ∀ reply, (input.post reply).IsTotalQueryBound qPost
  checkBound : input.number.val - 1 + 1 ≤ qCheck
  knownBound : (RawCtxFamilyFreshnessProxy.knownInputs input.disclosed input.before.roles.2).length ≤ qKnown
  preBound : ∀ query state cache, (input.other (.inl query) state cache).IsTotalQueryBound qPre
  applicationBound : ∀ query state cache, (input.other (.inr (.inl query)) state cache).IsTotalQueryBound qApplication
  selectorBound : ∀ query state cache, (input.other (.inr (.inr (.inr (.inl query)))) state cache).IsTotalQueryBound qSelector
  auxBound : ∀ query state cache, (input.other (.inr (.inr (.inr (.inr query)))) state cache).IsTotalQueryBound qAux

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (prior : ProbComp (Context extra M P I D K X Response A N S B))

abbrev Pending := RawCtxSupportedSample.Pending prior

noncomputable def view : PqxdhInitialHalfSecrecy.View (Pending prior) extra M P I D K X Response
    PqxdhPhase2DecapsulationRouting.Shared A N PqxdhCorrelatedExpand.RootOracle.QueryCache S B where
  execution := fun context => (PqxdhInitialSourceHalf.view source).execution (context.1.val, context.2)
  prior := fun context => (PqxdhInitialSourceHalf.view source).prior context.val
  pre := fun context => (PqxdhInitialSourceHalf.view source).pre context.val
  application := fun context => (PqxdhInitialSourceHalf.view source).application context.val
  initializer := fun context => (PqxdhInitialSourceHalf.view source).initializer (context.1.val, context.2)
  selector := fun context => (PqxdhInitialSourceHalf.view source).selector context.val
  aux := fun context => (PqxdhInitialSourceHalf.view source).aux context.val
  ambient := fun context => (PqxdhInitialSourceHalf.view source).ambient context.val
  priorCandidates := fun context => (PqxdhInitialSourceHalf.view source).priorCandidates (context.1.val, context.2)
  disclosed := fun context => context.val.disclosed
  ancestors := fun context => context.val.ancestors
  selected := fun context => context.val.selected
  number := fun context => context.val.number

noncomputable def mark (input : Pending prior) := PqxdhInitialSourceHalf.mark source input.val

def address (_ : Bool ⊕ Pending prior) : JointKdfAddress := rootAddress []

noncomputable def observer := PqxdhInitialHalfSecrecy.observer source writer (mark source prior) sender route decode (view source prior)
noncomputable def aliasTester := PqxdhInitialHalfSecrecy.aliasTester source writer (mark source prior) sender route decode (view source prior)
noncomputable def reductionObserver := PqxdhInitialHalfSecrecy.reductionObserver source writer (mark source prior) sender route decode (view source prior)
noncomputable def joint := RawCtxSelectedParentSecrecy.joint (RawCtxSupportedSample.sum prior) (address prior)

/-- Proof annotation does not change any original computation in the real-child source experiment. -/
theorem actual_erase :
    PqxdhInitialHalfSecrecy.actual source writer (mark source prior) sender route decode (view source prior)
      (RawCtxSupportedSample.sum prior) (address prior) =
    PqxdhInitialHalfSecrecy.actual source writer (PqxdhInitialSourceHalf.mark source) sender route decode
      (PqxdhInitialSourceHalf.view source) prior PqxdhInitialSourceFirstSecrecy.address := by
  simp only [PqxdhInitialHalfSecrecy.actual, RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  rw [← RawCtxSupportedSample.sum_run prior (fun context => ($ᵗ FullOutput) >>= fun output =>
    PqxdhInitialHalfSecrecy.native source writer (PqxdhInitialSourceHalf.mark source) sender route decode
      (PqxdhInitialSourceHalf.view source) (context, fromOutput (PqxdhInitialSourceFirstSecrecy.address context) output)
      (PqxdhOrderedChainHybrids.nextChain output)
      (productionStream source.crypto (FixedHkdfDomain.ratchet.address (PqxdhOrderedChainHybrids.nextChain output).toList)))]
  apply bind_congr
  intro context
  cases context <;> rfl

/-- Proof annotation also preserves every callback and draw in the independent-child experiment. -/
theorem random_erase :
    PqxdhInitialHalfSecrecy.random source writer (mark source prior) sender route decode (view source prior)
      (RawCtxSupportedSample.sum prior) (address prior) =
    PqxdhInitialHalfSecrecy.random source writer (PqxdhInitialSourceHalf.mark source) sender route decode
      (PqxdhInitialSourceHalf.view source) prior PqxdhInitialSourceFirstSecrecy.address := by
  simp only [PqxdhInitialHalfSecrecy.random, RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  rw [← RawCtxSupportedSample.sum_run prior (fun context => ($ᵗ FullOutput) >>= fun parent =>
    ($ᵗ FullOutput) >>= fun output =>
    PqxdhInitialHalfSecrecy.native source writer (PqxdhInitialSourceHalf.mark source) sender route decode
      (PqxdhInitialSourceHalf.view source) (context, fromOutput (PqxdhInitialSourceFirstSecrecy.address context) parent)
      (PqxdhOrderedChainHybrids.nextChain parent) output)]
  apply bind_congr
  intro context
  cases context <;> rfl

variable (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat)
  (caps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)

include caps in
/-- The ordinary source observer's complete uniform and candidate caps are derived on each actually prepared input; common decisions have zero work and candidates. -/
theorem observed_bounds (context : (Bool ⊕ Pending prior) × Entry) (output : FullOutput) :
    let work := PqxdhInitialHalfSecrecy.observed source writer (mark source prior) sender route decode (view source prior) context output
    work.IsTotalQueryBound (uniformCap qPost qCheck qPre qApplication qSelector qAux) ∧
      ∀ result ∈ support work, (PqxdhInitialHalfSecrecy.candidates result).length ≤ candidateCap qPost qCheck qKnown := by
  rcases context with ⟨common | pending, entry⟩
  · constructor
    · trivial
    · intro result supported
      simp only [PqxdhInitialHalfSecrecy.observed, mem_support_pure_iff] at supported
      subst result
      exact Nat.zero_le _
  · let c := caps pending.val pending.property
    exact one_bounds source writer sender route decode pending.val qPost qCheck qKnown qPre qApplication qSelector qAux
      c.postBound c.checkBound c.knownBound c.preBound c.applicationBound c.selectorBound c.auxBound entry output

noncomputable def loss (hmac : HmacSha512) : ℝ :=
  RawCtxSelectedParentHop.extractLoss hmac (RawCtxSupportedSample.sum prior) (address prior)
      (observer source writer sender route decode prior) +
    RawCtxSelectedParentHop.hmacLoss hmac (RawCtxSupportedSample.sum prior) (address prior)
      (observer source writer sender route decode prior) +
    3 * (RawCtxSelectedParentHop.extractLoss hmac (RawCtxSupportedSample.sum prior) (address prior)
      (aliasTester source writer sender route decode prior) +
      RawCtxSelectedParentHop.hmacLoss hmac (RawCtxSupportedSample.sum prior) (address prior)
        (aliasTester source writer sender route decode prior) +
      (2 ^ 352 : ℝ)⁻¹ + (candidateCap qPost qCheck qKnown : ℝ) / (2 ^ 256 : ℝ))

include caps in
/-- The actual sampled source stage zero-to-one secrecy comparison uses its constructed ordinary Extract/HMAC reductions, explicit factor-three alias loss and source-derived candidate bill. No honest-selection, distinct-byte, prior-state or final-event equality is assumed. -/
theorem bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (positive : ∀ input, Sum.inr input ∈ support prior → 0 < input.number.val) :
    (PqxdhInitialSourceSampled.game source writer sender route decode prior 0).boolDistAdvantage
      (PqxdhInitialSourceSampled.game source writer sender route decode prior 1) ≤
      loss source writer sender route decode prior qPost qCheck qKnown hmac := by
  have result := PqxdhInitialHalfSecrecy.bound source hmac correct writer (mark source prior) sender route decode
    (view source prior) (RawCtxSupportedSample.sum prior) (address prior) (candidateCap qPost qCheck qKnown)
    (fun context output => (observed_bounds source writer sender route decode prior qPost qCheck qKnown qPre qApplication
      qSelector qAux caps context output).2)
  rw [actual_erase, random_erase] at result
  have realLaw := OracleComp.probOutput_congr (x := true) rfl
    (PqxdhInitialSourceFirstSecrecy.actual_source source writer sender route decode prior)
  have randomLaw := OracleComp.probOutput_congr (x := true) rfl
    (PqxdhInitialSourceFirstSecrecy.random_source source writer sender route decode prior positive)
  simpa only [ProbComp.boolDistAdvantage, ← realLaw, ← randomLaw, loss, observer, aliasTester] using result

/-- Attaching supported source inputs preserves the original preparation query bill by syntax equality. -/
theorem sample_uniform (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    (RawCtxSupportedSample.sum prior).IsTotalQueryBound qPrior := by
  apply (isQueryBound_map_iff _ (Sum.map id Subtype.val) _ _ _).mp
  rw [RawCtxSupportedSample.sum_erase]
  exact bounded

include caps in
/-- The two constructed reductions each ask at most two HMAC challenges and pay every preparation, full76 sampler and complete source/checker random query. The tester's real-HKDF evaluation count is separately bounded by the whole candidate cap. -/
theorem reduction_queries (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    (∀ forTester, let observe := reductionObserver source writer sender route decode prior forTester
      (fullExpandReduction .ratchet (joint prior) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (joint prior) observe).IsQueryBoundP IsHmacUniformQuery
          ((qPrior + 76) + uniformCap qPost qCheck qPre qApplication qSelector qAux)) ∧
      (∀ context output result, result ∈ support
        (PqxdhInitialHalfSecrecy.observed source writer (mark source prior) sender route decode (view source prior) context output) →
        (RawCtxFullPreimageTester.evaluate output (PqxdhInitialHalfSecrecy.candidates result)).IsTotalQueryBound
          (candidateCap qPost qCheck qKnown)) :=
  PqxdhInitialHalfSecrecy.reduction_queries source writer (mark source prior) sender route decode (view source prior)
    (RawCtxSupportedSample.sum prior) (address prior) qPrior (uniformCap qPost qCheck qPre qApplication qSelector qAux)
    (candidateCap qPost qCheck qKnown) (sample_uniform prior qPrior bounded)
    (fun context output => (observed_bounds source writer sender route decode prior qPost qCheck qKnown qPre qApplication
      qSelector qAux caps context output).1)
    (fun context output => (observed_bounds source writer sender route decode prior qPost qCheck qKnown qPre qApplication
      qSelector qAux caps context output).2)

include caps in
/-- The literal Extract-real, Extract-random, HMAC-real, HMAC-random and independent-child games pay their own sampler/challenger bills, in addition to the same complete ordinary observer. -/
theorem challenger_queries (hmac : HmacSha512) (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) (forTester : Bool) :
    let observe := reductionObserver source writer sender route decode prior forTester
    let joint := joint prior
    let u := uniformCap qPost qCheck qPre qApplication qSelector qAux
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((qPrior + 76) + u) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((qPrior + 76) + (64 + u)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (64 + ((qPrior + 76) + u)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound ((qPrior + 76) + (64 + (64 + u))) ∧
      (RawCtxSelectedParentSecrecy.random (RawCtxSupportedSample.sum prior) (address prior) observe).IsTotalQueryBound
        ((qPrior + 76) + (76 + u)) :=
  PqxdhInitialHalfSecrecy.challenger_queries source hmac writer (mark source prior) sender route decode (view source prior)
    (RawCtxSupportedSample.sum prior) (address prior) qPrior (uniformCap qPost qCheck qPre qApplication qSelector qAux)
    (sample_uniform prior qPrior bounded)
    (fun context output => (observed_bounds source writer sender route decode prior qPost qCheck qKnown qPre qApplication
      qSelector qAux caps context output).1) forTester

end BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.actual_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.actual_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.random_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.random_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.observed_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.observed_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.sample_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.sample_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources.challenger_queries
