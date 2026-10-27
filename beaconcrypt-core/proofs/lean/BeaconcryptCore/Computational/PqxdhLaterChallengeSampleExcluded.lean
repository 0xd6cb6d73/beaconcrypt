import BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache
import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleActive
import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded

/-! Exclude the inside challenge phase using the actual prepared parent sample, its same-cache lineage and the real retained executor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded
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

/-- The complete real retained continuation from an actual prepared missing-parent sample cannot yield the marked target event from an inside-phase challenge cut. All cache and frontend facts come from that same sampled execution. -/
theorem run_not_inside {OtherA OtherN OtherC : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (number : U64) (position : number.val = depth + 2) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth start.selected number bit adversary)).run start.shared.2))
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : PqxdhFullSecretInputKdf.FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained (env).source (env).recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume
        (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode pending.1
        (PqxdhInitialParentBuilderContext.reply (env).senderId (env).route (env).decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true) (published : ((start.selected, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  intro classified
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
  obtain ⟨front, history, invariant, cut⟩ := PqxdhLaterChallengeSampleActive.reached_active original callbacks
    baseImpl kem attachedVerify primitives secret challenge start output depth start.selected number bit adversary
    pending details start.shared.2 after reached classified
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
  apply PqxdhLaterChallengeInsideExcluded.frame_excluded
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
    start.selected number bit details classified (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    (PqxdhLaterChallengeSampleChronology.native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)
    (front, history) (attach pending.2 after) (attach pending.2 after) cut pending.1 joined
    (env).source (env).recordWriter prior entry target full external atParent before result completed
    _ (attach pending.2 after).1 invariant cursor.2.2 _ _ accepted published
  · change pending.2.store.1 (RawCtxSelectiveChainGame.cursorAddress pending.2.store.2) = none
    have address : PqxdhInitialBuilderContext.address pending.1.original =
        RawCtxSelectiveChainGame.cursorAddress pending.2.store.2 := cursor.2.1
    rw [← address]
    exact absent.2
  · have same : (attach pending.2 after).1.1.1.2.2.depth = depth := cursor.1
    omega

/-- Changing only the saved initial cache field leaves the actual program unchanged, so the real inside-event exclusion holds from any reached shared cache. -/
theorem cache_not_inside {OtherA OtherN OtherC : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (number : U64) (position : number.val = depth + 2) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth start.selected number bit adversary)).run cache))
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : PqxdhFullSecretInputKdf.FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained (env).source (env).recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume
        (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode pending.1
        (PqxdhInitialParentBuilderContext.reply (env).senderId (env).route (env).decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true) (published : ((start.selected, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  apply run_not_inside original callbacks baseImpl kem attachedVerify primitives secret challenge
    { start with shared := (start.shared.1, cache) } output depth number position bit adversary pending details after
    _ prior entry target full external atParent before result completed accepted published
  simpa only [PqxdhLaterChallengeCapturedCache.run_start_cache] using supported

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded.run_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded.run_not_inside

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded.cache_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded.cache_not_inside
