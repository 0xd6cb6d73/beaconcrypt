import BeaconcryptCore.Computational.PqxdhLaterExecutableSource
import BeaconcryptCore.Computational.PqxdhLaterRetainedEvent

/-! The actual certified sampler connects its original final-material observation to the exact saved source event. The original finite checker and reveal history remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableEvent
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
open PqxdhNativeSharedPrefix PqxdhSelectedFirstRecord RawCtxSelectedParentTable PqxdhJointKdfGame RawCtxSelectedMessageDriver PqxdhJointKdf
local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
  (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
open PqxdhFirstRecordConfidentiality


local notation "Carrier" => PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

noncomputable def earlier (start : Input × HmacBlock) (pending : Pending) : List RatchetChain :=
  (PqxdhInitialSourceSecrecyResources.earlierInputs
    (PqxdhInitialSourceExperiment.root env.source zeroRoot (PqxdhInitialSampledParent.response start) start.1.selected)
    (pending.1, attach pending.2 ∅)).map RawCtxFreshChainCut.concreteChain

noncomputable def decision (result : Carrier) (start : Input × HmacBlock) (pending : Pending)
    (key : RootOutput) : Bool × (Front × Trace) → Bool :=
  PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream env.source.crypto) pending.2.store.1)
    result.2.1.1.2 result.2.1.2 (RawCtxSelectedMessageKdf.response key result.2.2.1 result.2.2.2) 0
    (earlier setup env start pending) start.1.ancestors start.1.disclosed start.1.selected start.1.number

/-- Mathematical observation on the full projected source state. Outer refusal is distinct from the original Boolean result. -/
noncomputable def optionalDecision (result : Carrier) (start : Input × HmacBlock) (pending : Pending)
    (key : RootOutput) (value : Option Bool × (Front × Trace)) : Bool :=
  value.1.elim false (fun bit => decision setup env result start pending key (bit, value.2))

noncomputable def pendingFlagged (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (key : RootOutput) (component : AdaptiveCtxDynamicKnownKeys.SourceState) := by
  let fits : PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
    simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
  exact
  PqxdhLaterSavedPostComparison.flagged
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.val.2.1.2) (result.val.2.2.1) (result.val.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode ⟨0, Nat.zero_lt_succ _⟩ (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.val.2.1.1.2)).material fits (pending.2, component)


/-- The same original decision is exactly the saved event, including the interpreted source reveal history. -/
theorem optional_event (result : Carrier) (start : Input × HmacBlock) (pending : Pending)
    (key : RootOutput) (value : Option Bool × Traced M P (IdentityHandle I) (DhPair setup) (KemHandle K)
      A (BareState 1) RootOracle.QueryCache S (B + 1)) :
    optionalDecision setup env result start pending key (value.1, (tracedProj key value.2).1) =
      (by classical exact decide (PqxdhLaterSavedFreshness.Event
        (view (productionStream env.source.crypto) pending.2.store.1)
        result.2.1.1.2 result.2.1.2 key result.2.2.1 result.2.2.2
        (earlier setup env start pending) start.1.ancestors start.1.disclosed start.1.selected start.1.number value)) := by
  classical
  cases value with | mk reply state => cases reply <;> simp [optionalDecision, decision, PqxdhLaterSavedFreshness.Event]

/-- The unchanged original material observation executes the literal saved source and tests its exact publication/finite-key-freshness decision. Descriptor address provenance comes from the actual certified sampler. -/
theorem pending_original (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c))
    (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending)) (cache : CtxRO.QueryCache)
    (supported : (result, cache) ∈ support ((simulateQ hashImpl
      (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅))
    (key : RootOutput)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2 ≠ result.val.2.1.1.2.address) :
    PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
      (PqxdhLaterSharedMessagePrefix.restore setup result.val.2 cache) key =
    (fun final => decision setup env result.val start pending key final.1) <$>
      PqxdhLaterPreparedCompletion.native setup env (result.val, cache) start pending key := by
  have scopeFacts := PqxdhLaterSavedSampler.pending_scope setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed c depth (result.val, cache)
    (PqxdhLaterExecutableCertificates.evaluated_support env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth (result, cache) supported) start pending shape
  have native := PqxdhLaterRetainedEvent.original_event env.source env.recordWriter
    (PqxdhInitialSourcePreparedSecrecy.pre start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
    (PqxdhInitialNativeInitializer.initial env.source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhInitialSourcePreparedSecrecy.selector start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
    env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source start)
    (pending.1, attach pending.2 cache) result.val.2.1.1.2 result.val.2.1.2
    (RawCtxSelectedMessageKdf.response key result.val.2.2.1 result.val.2.2.2)
    (PqxdhInitialSourceExperiment.root env.source zeroRoot (PqxdhInitialSampledParent.response start) start.1.selected)
    start.1.ancestors start.1.disclosed start.1.selected start.1.number scopeFacts.2.2.1 separate
  simpa only [PqxdhErasedParentMaterial.observe, PqxdhLaterSharedMessagePrefix.restore,
    PqxdhSharedParentInput.restore, shape, PqxdhSharedParentCollect.restore, PqxdhErasedParentSample.native,
    PqxdhLaterPreparedCompletion.native, PqxdhInitialSourcePreparedSecrecy.external_source,
    privateTable, decision, earlier, RawCtxSelectedMessageKdf.response,
    PqxdhInitialSourceSecrecyResources.earlierInputs, attach,
    PqxdhInitialNativeParentRealization.flat, PqxdhInitialSupportedCertificate.ambient,
    PqxdhInitialNativeRetained.project] using native

/-- The actual original pending decision is the same observation of the complete saved comparison source; all callback and descriptor premises come from the executed certified sampler. -/
theorem pending_event (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c))
    (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending)) (cache : CtxRO.QueryCache)
    (supported : (result, cache) ∈ support ((simulateQ hashImpl
      (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅))
    (key : RootOutput)
    (component : AdaptiveCtxDynamicKnownKeys.SourceState) (sameCache : component.cache = cache)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2 ≠ result.val.2.1.1.2.address) :
    PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
      (PqxdhLaterSharedMessagePrefix.restore setup result.val.2 cache) key =
    (fun final => optionalDecision setup env result.val start pending key
      (final.1, (tracedProj key final.2).1)) <$>
      PqxdhLaterExecutableSource.pendingOriginal setup env callbacks program post attachedVerify primitives baseImpl kem
        c result start pending shape key component := by
  rw [pending_original setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed
    c depth result start pending shape cache supported key separate]
  have source := PqxdhLaterExecutableSource.pending_native setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed c depth result start pending shape cache supported key component sameCache
  have observed := congrArg (fun work => (fun final => optionalDecision setup env result.val start pending key final.1) <$> work) source
  simpa only [Functor.map_map, optionalDecision, Option.elim_some] using observed.symm

/-- Every actual nonaliased pending observation is bounded by its complete compiled original event and the actual same-run nonce refusal. The source checker discharges hidden-key freshness rather than adding a new condition. -/
theorem pending_bound (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c))
    (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending)) (cache : CtxRO.QueryCache)
    (supported : (result, cache) ∈ support ((simulateQ hashImpl
      (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅))
    (key : RootOutput)
    (component : AdaptiveCtxDynamicKnownKeys.SourceState) (sameCache : component.cache = cache)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress result.val.2.1.2 ≠ result.val.2.1.1.2.address) :
    𝒟[PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
      (PqxdhLaterSharedMessagePrefix.restore setup result.val.2 cache) key] {true} ≤
    𝒟[(fun final => optionalDecision setup env result.val start pending key
      (final.1, (tracedProj key (insProject final.2)).1)) <$>
      PqxdhLaterExecutableSource.pendingCompiled setup env callbacks program post attachedVerify primitives baseImpl kem
        c result start pending shape key component] {true} +
    𝒟[(fun final => final.2.2 && optionalDecision setup env result.val start pending key
      (final.1, (tracedProj key (insProject final.2.1)).1)) <$>
      pendingFlagged setup env callbacks program post attachedVerify primitives baseImpl kem
        c result start pending shape key component] {true} := by
  rw [pending_event setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed
    c depth result start pending shape cache supported key component sameCache separate]
  have scopeFacts := PqxdhLaterSavedSampler.pending_scope setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed c depth (result.val, cache)
    (PqxdhLaterExecutableCertificates.evaluated_support env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth (result, cache) supported) start pending shape
  have parent : Entry.mk (PqxdhInitialBuilderContext.address pending.1.original) result.val.2.1.1.2.material = result.val.2.1.1.2 := by
    rw [← scopeFacts.2.2.1]
  let fits : PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
    simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
  have comparison := PqxdhLaterSavedFreshness.source_bound
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.val.2.1.2) (result.val.2.2.1) (result.val.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode ⟨0, Nat.zero_lt_succ _⟩ (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.val.2.1.1.2)).material fits (pending.2, component)

    (earlier setup env start pending) start.1.ancestors start.1.disclosed start.1.selected start.1.number
  rw [parent] at comparison
  have observed := fun reply state => optional_event setup env result.val start pending key (reply, state)
  simpa only [PqxdhLaterExecutableSource.pendingOriginal, PqxdhLaterExecutableSource.pendingCompiled,
    pendingFlagged, observed] using comparison

end BeaconcryptCore.Computational.PqxdhLaterExecutableEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.optional_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.optional_event
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_original
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_event
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableEvent.pending_bound
