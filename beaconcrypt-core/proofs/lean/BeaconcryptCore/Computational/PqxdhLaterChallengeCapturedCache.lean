import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache
import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology

/-! The actual prepared capture and complete resumed wrapper identify historical target publications in the same finite source cache, without reconstructing a normalized prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => PqxdhPreparedSharedPrefix.environment original callbacks
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "pre" => PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "application" => PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "selector" => PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge)
local notation "aux" => PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks

open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture

open PqxdhLaterChallengePreparedCapture
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "Details" => PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)
local notation "Cut" => CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)


local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Base" => PqxdhInitialPostContext.Base (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
  (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared S (B + 1)

/-- Actual prepared-source reachability, the unchanged generated descriptor composition and a complete true resumed output place every marked target publication in the original finite cache at that same cut, when the wrapper had already chosen its challenge. -/
theorem reached_cached {Other : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeSampleChronology.Reached original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after)
    (joined : PqxdhLaterChallengeCapture.Joined owner number bit (pending.1, details))
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage)
        (env).senderId (env).route (env).decode pending.1).2 reply)).run before))
    (used : details.request.before.pair.isSome) (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    RawCtxSourcePublishedPath.Cached
      (PqxdhInitialSourceExperiment.root (env).source zeroRoot (RawCtxSelectedInitialConstructor.response64 output) owner)
      number pending.2.store.1 := by
  obtain ⟨built, backend, front, history, ambient, initialized, traced, captured⟩ := reached
  have recorded : ((owner, number), true) ∈ history.published :=
    (PqxdhLaterChallengeRemainderPublication.captured_publication
      (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
      owner number bit (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
      (PqxdhLaterChallengeSampleChronology.native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)
      (front, history) ambient (attach pending.2 after) (pending.1, details) joined captured
      afterImpl before reply result completed used accepted).mp published
  simp only [PqxdhLaterChallengeSampleChronology.native, PqxdhNativeSharedPrefix.initial_source] at initialized traced captured
  have first := PqxdhLaterChallengePrefixCache.builder_invariant (env).source (env).recordWriter (depth + 1)
    start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)
    (fun query => localLift (pre query)) (fun value => localLift (application value))
    (fun query => localLift (selector query)) (fun query => localLift (aux query))
    (env).senderId (env).route (env).decode owner start.index start.metadata { start.ready with root := zeroRoot }
    start.before (attach (PqxdhPreparedSharedPrefix.state original start output) cache) (built, backend)
    (by simpa only [PqxdhInitialSourceExperiment.execution, withPost] using initialized)
  have current := PqxdhLaterChallengePrefixCache.reaches_invariant (env).source (env).recordWriter (depth + 1)
    start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)
    (fun query => localLift (pre query)) (fun value => localLift (application value))
    (fun query => localLift (selector query)) (fun query => localLift (aux query))
    (env).senderId (env).route (env).decode
    (RawCtxSelectedQueryTrace.rootVector (PqxdhInitialSourceExperiment.server (env).source
      (RawCtxSelectedInitialConstructor.response64 output)).refined.send_chain)
    owner number bit _ _ _ _ _ _ traced first
  exact PqxdhLaterChallengePrefixCache.pending_cached (env).source (env).recordWriter (depth + 1)
    start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)
    (fun query => localLift (pre query)) (fun value => localLift (application value))
    (fun query => localLift (selector query)) (fun query => localLift (aux query))
    PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    (PqxdhInitialOriginContext.frame (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage)
      (env).senderId (env).route (env).decode) _ _
    (PqxdhInitialOriginForwardPost.program_sound _ _ _ _ _ front history)
    ambient (attach pending.2 after) details.callback captured _ number (current.2 number recorded)

/-- In the actual missing-parent sampler, a complete true resumed target-publication event cannot have an already-used wrapper at the saved callback. The same finite cache supplies both the historical path and the pending miss, so no probabilistic freshness or new cut-selection premise is used. -/
theorem run_not_used {Other : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (number : U64) (position : number.val = depth + 2) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth start.selected number bit adversary)).run start.shared.2))
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage)
        (env).senderId (env).route (env).decode pending.1).2 reply)).run before))
    (accepted : result.1.1 = true)
    (published : ((start.selected, number), true) ∈ result.1.2.2.published) :
    ¬ details.request.before.pair.isSome := by
  intro used
  have syntactic : Sum.inr (pending, some details) ∈ support
      (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth start.selected number bit adversary) := by
    apply support_simulateQ_run'_subset hashImpl _ start.shared.2
    simp only [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨(Sum.inr (pending, some details), after), supported, rfl⟩
  have joined := PqxdhLaterChallengePreparedCapture.run_joined original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth start.selected number bit adversary pending (some details) syntactic
  have reached := PqxdhLaterChallengeSampleChronology.run_reaches original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth start.selected number bit adversary pending details start.shared.2 after supported
  have cached := reached_cached original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth start.selected number bit adversary pending details start.shared.2 after reached joined
    afterImpl before reply result completed used accepted published
  have sampled : Sum.inr (pending.1, attach pending.2 after) ∈ support
      (PqxdhErasedParentSample.sampleOne (env).source (env).recordWriter (env).senderId (env).route (env).decode depth
        (PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge
          (withPost (setup := setup) start start.selected number bit adversary), output)) := by
    rw [← PqxdhLaterChallengePreparedCapture.run_source original callbacks baseImpl kem attachedVerify primitives secret challenge,
      support_map]
    exact ⟨(Sum.inr (pending, some details), after), supported, rfl⟩
  have cursor := PqxdhLaterSendAddress.sample_one_cursor (env).source (env).recordWriter (env).senderId (env).route (env).decode
    depth _ _ sampled
  have absent := (PqxdhInitialPreparedParent.supported_pending (env).source (env).recordWriter _ _ _ _ _ _
    (env).senderId (env).route (env).decode _ _ depth _ (attach pending.2 after) pending.1).mp sampled
  apply PqxdhLaterCommonRisk.cached_beyond_cursor _ number pending.2.store cursor.2.2 cached
    (by have same : pending.2.store.2.depth = depth := cursor.1; omega)
  have address : PqxdhInitialBuilderContext.address pending.1.original =
      RawCtxSelectiveChainGame.cursorAddress pending.2.store.2 := cursor.2.1
  rw [← address]
  exact absent.2

/-- The prepared source program takes its current shared cache from the interpreter state; changing only the saved initial cache field does not change any request, continuation or complete/cache branch. -/
theorem run_start_cache (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (cache : CtxRO.QueryCache) :
    PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
      { start with shared := (start.shared.1, cache) } output depth owner number bit adversary =
    PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary := by
  rfl

/-- The same actual sampled exclusion holds for an arbitrary reached shared cache. An exact source-program equality restores only its explicit initial cache field, without asserting any normalized prefix reachable. -/
theorem cache_not_used {Other : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (number : U64) (position : number.val = depth + 2) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth start.selected number bit adversary)).run cache))
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage)
        (env).senderId (env).route (env).decode pending.1).2 reply)).run before))
    (accepted : result.1.1 = true)
    (published : ((start.selected, number), true) ∈ result.1.2.2.published) :
    ¬ details.request.before.pair.isSome := by
  apply run_not_used original callbacks baseImpl kem attachedVerify primitives secret challenge
    { start with shared := (start.shared.1, cache) } output depth number position bit adversary pending details after
    _ afterImpl before reply result completed accepted published
  simpa only [run_start_cache] using supported

end BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.reached_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.reached_cached
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.run_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.run_not_used
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.run_start_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.run_start_cache
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.cache_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache.cache_not_used
