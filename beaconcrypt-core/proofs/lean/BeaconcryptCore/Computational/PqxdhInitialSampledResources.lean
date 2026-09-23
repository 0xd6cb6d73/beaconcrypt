import BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy

/-!
Finite query bills come from the actually sampled original source input. The support certificate is attached by forward syntax-preserving annotation; it neither conditions the run nor tests support at runtime. Only original callbacks, original post requests and the explicit pre-existing disclosure count are budgeted. Complete stopped observers and reduction costs are derived from those local source bounds.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSourcePreparedSecrecy
open RawCtxSelectedParentEntry PqxdhInitialSampledParent
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

structure Caps (input : Input extra M P I D K X Response A N S B)
    (qPost qPre qApplication qSelector qAux qKnown : Nat) : Prop where
  postBound : ∀ reply, (input.post reply).IsTotalQueryBound qPost
  preBound : ∀ query ambientState rootCache, (pre input.other query ambientState rootCache).IsTotalQueryBound qPre
  applicationBound : ∀ query ambientState rootCache, (application input.other query ambientState rootCache).IsTotalQueryBound qApplication
  selectorBound : ∀ query ambientState rootCache, (selector input.other query ambientState rootCache).IsTotalQueryBound qSelector
  auxBound : ∀ query ambientState rootCache, (aux input.other query ambientState rootCache).IsTotalQueryBound qAux
  knownBound : PqxdhInitialHistoryBudget.knownLength input.disclosed input.before.roles.2 ≤ qKnown

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat)
  (qPost qPre qApplication qSelector qAux qKnown : Nat)

local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "costs" => PqxdhInitialAuditedResources.retainedCosts qPre qApplication qSelector qAux

def candidateCap : Nat := qKnown + qPost + 3 * (7 + qPost * 67) + 3 * (2 * (255 + qPost * 67) + (remaining + 1))

/-- The full source candidate allowance follows from the explicitly counted actual initial disclosures and original source callback allowance. -/
theorem candidate_cap (input : Input extra M P I D K X Response A N S B)
    (caps : Caps input qPost qPre qApplication qSelector qAux qKnown) :
    candidateBudget input.before input.disclosed remaining qPost ≤ candidateCap remaining qPost qKnown := by
  unfold candidateBudget candidateCap
  have count := caps.knownBound
  omega

/-- Each supported source input supplies both the complete stopped-observer uniform cost and every candidate appended by the source and checker. -/
theorem one_bounds (start : Start extra M P I D K X Response A N S B)
    (caps : Caps start.1 qPost qPre qApplication qSelector qAux qKnown)
    (context : Carrier source writer sender route decode depth start × Entry) (output : FullOutput) :
    let work := PqxdhInitialCommonSecrecy.observed source writer (marker source start) sender route decode
      (PqxdhInitialSampledParent.view source writer sender route decode depth remaining start) context output
    work.IsTotalQueryBound (observerBudget remaining qPost qPre qApplication qSelector qAux) ∧
      ∀ result ∈ support work, (PqxdhInitialCommonSecrecy.candidates result).length ≤ candidateCap remaining qPost qKnown := by
  let initial := PqxdhInitialNativeInitializer.initial (A := A) (N := N) source start.1.selectedMessage zeroRoot (response start)
  let execution := PqxdhInitialSourceExperiment.execution (response start) start.1.index start.1.metadata
    { start.1.ready with root := zeroRoot } start.1.post start.1.before
  let root := PqxdhInitialSourceExperiment.root source zeroRoot (response start) start.1.selected
  let state := (PqxdhInitialSourceExperiment.initialState root start.1.shared start.1.privateState start.1.cache, ([] : List RootOutput))
  have callbacks := PqxdhInitialAuditedResources.retained_callbacks source start.1.selectedMessage zeroRoot (response start)
    (pre start.1.other) (application start.1.other) (selector start.1.other) (aux start.1.other)
    qPre qApplication qSelector qAux caps.preBound caps.applicationBound caps.selectorBound caps.auxBound
  have uniforms := PqxdhInitialSourceSecrecyResources.observed_uniform source writer (pre start.1.other) (application start.1.other)
    initial (selector start.1.other) (aux start.1.other) (marker source start) sender route decode execution depth state
    root start.1.ancestors start.1.disclosed start.1.selected start.1.number remaining qPost caps.postBound costs callbacks context output
  constructor
  · simpa only [initial, execution, root, state, marker, PqxdhInitialSampledParent.view, PqxdhInitialSourcePreparedSecrecy.view, observerBudget, PqxdhInitialSourceSecrecyResources.uniformBudget,
      PqxdhInitialSourceSecrecyResources.callbackBudget, PqxdhInitialParentObserverBudgets.Costs.cap,
      PqxdhInitialAuditedResources.retainedCosts] using uniforms
  · intro result supported
    have count := PqxdhInitialSourceSecrecyResources.candidates_bound source writer (pre start.1.other) (application start.1.other)
      initial (selector start.1.other) (aux start.1.other) (marker source start) sender route decode execution depth state
      root start.1.ancestors start.1.disclosed start.1.selected start.1.number remaining qPost caps.postBound costs callbacks context output result supported
    have localCap : (PqxdhInitialCommonSecrecy.candidates result).length ≤ candidateBudget start.1.before start.1.disclosed remaining qPost := by
      simpa only [PqxdhInitialSourceSecrecyResources.candidateBudget, PqxdhInitialSourceSecrecyResources.callbackBudget,
        PqxdhInitialSupportedCertificate.priorBudget, execution, state, PqxdhInitialSourceExperiment.execution,
        List.length_nil, Nat.add_zero, candidateBudget] using count
    exact localCap.trans (candidate_cap remaining qPost qPre qApplication qSelector qAux qKnown start.1 caps)

variable (prior : ProbComp (Context extra M P I D K X Response A N S B))
  (sourceCaps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qPre qApplication qSelector qAux qKnown)

include sourceCaps in
/-- Every actual global carrier has its supported original source certificate; unreachable arbitrary inputs introduce no uniform or candidate premise. -/
theorem observed_bounds (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) (output : FullOutput) :
    (observed source writer sender route decode depth remaining context output).IsTotalQueryBound
      (observerBudget remaining qPost qPre qApplication qSelector qAux) ∧
      ∀ result ∈ support (observed source writer sender route decode depth remaining context output),
        (PqxdhInitialCommonSecrecy.candidates result).length ≤ candidateCap remaining qPost qKnown := by
  rcases context with ⟨decision | ⟨start, pending⟩, entry⟩
  · refine ⟨by trivial, ?_⟩
    intro result reached
    simp only [observed, mem_support_pure_iff] at reached
    subst result
    simp [PqxdhInitialCommonSecrecy.candidates]
  · exact one_bounds source writer sender route decode depth remaining qPost qPre qApplication qSelector qAux qKnown
      start (sourceCaps start.1 pending.property) (pending.val, entry) output

include sourceCaps in
set_option maxRecDepth 2048 in
/-- The full reduction prefix pays the exact original preparation, the shared64-byte initial response and the complete original stopped-source sampler. -/
theorem sample_uniform (qPrior : Nat) (priorBound : prior.IsTotalQueryBound qPrior) :
    (PqxdhInitialSampledParent.sample source writer sender route decode depth prior).IsTotalQueryBound
      (qPrior + (64 + sampleBudget qPost qPre qApplication qSelector qAux)) := by
  have annotated : (RawCtxSupportedSample.sum prior).IsTotalQueryBound qPrior := by
    apply (isQueryBound_map_iff _ (Sum.map id Subtype.val) _ _ _).mp
    rw [RawCtxSupportedSample.sum_erase]
    exact priorBound
  unfold PqxdhInitialSampledParent.sample
  apply isTotalQueryBound_bind annotated
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
  intro output
  cases context with
  | inl decision => trivial
  | inr input =>
    apply (isQueryBound_map_iff _ _ _ _ _).2
    have caps := sourceCaps input.val input.property
    exact PqxdhInitialSourcePreparedSecrecy.sample_uniform source writer input.val.selectedMessage zeroRoot
      (RawCtxSelectedInitialConstructor.response64 output) input.val.other sender route decode input.val.index input.val.metadata
      { input.val.ready with root := zeroRoot } input.val.post input.val.before input.val.selected input.val.number
      input.val.ancestors input.val.disclosed input.val.shared input.val.privateState input.val.cache depth
      qPost qPre qApplication qSelector qAux caps.postBound caps.preBound caps.applicationBound caps.selectorBound caps.auxBound

include sourceCaps in
/-- The main ordinary observer and the separate real-HKDF candidate tester retain the complete original source and appended-checker sampling bill. -/
theorem observer_bounds :
    (∀ (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) output,
      (observer source writer sender route decode depth remaining context output).IsTotalQueryBound
        (observerBudget remaining qPost qPre qApplication qSelector qAux)) ∧
      (∀ (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) output,
      (PqxdhInitialSampledParentSecrecy.aliasTester source writer sender route decode depth remaining context output).IsTotalQueryBound
        (observerBudget remaining qPost qPre qApplication qSelector qAux)) := by
  constructor
  · intro context output
    rcases context with ⟨decision | ⟨start, pending⟩, entry⟩
    · trivial
    · exact (PqxdhInitialCommonSecrecy.observer_bounds source writer (marker source start) sender route decode
        (PqxdhInitialSampledParent.view source writer sender route decode depth remaining start)
        (observerBudget remaining qPost qPre qApplication qSelector qAux)
        (fun context output => (one_bounds source writer sender route decode depth remaining
          qPost qPre qApplication qSelector qAux qKnown start (sourceCaps start.1 pending.property) context output).1)).1
        (pending.val, entry) output
  · exact RawCtxFullPreimageTester.tester_uniform _ _ _
      (fun context output => (observed_bounds source writer sender route decode depth remaining
        qPost qPre qApplication qSelector qAux qKnown prior sourceCaps context output).1)

end BeaconcryptCore.Computational.PqxdhInitialSampledResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledResources.candidate_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledResources.candidate_cap
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledResources.one_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledResources.one_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledResources.observed_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledResources.observed_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledResources.sample_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledResources.sample_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledResources.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledResources.observer_bounds
