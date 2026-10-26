import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCache
import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache

/-! The actual inside cut retains the initialized source cache invariant at the literal pre-request frontend and the exact carried native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampleActive
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

/-- The exact carried source state at an inside cut has the source's initialized directional-cache invariant at the same literal pre-request frontend/history. -/
theorem reached_active (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeSampleChronology.Reached original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside) :
    ∃ (front : Front) (history : Trace),
      PqxdhInitialOriginPostPath.Invariant
        (PqxdhInitialSourceExperiment.root (env).source zeroRoot (RawCtxSelectedInitialConstructor.response64 output) owner)
        owner (front, history) (attach pending.2 after).1 ∧
      RawCtxForwardScan.Cut.pending details.callback (attach pending.2 after) ∈ support
        (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth)
          (native_selection depth)
          (PqxdhLaterChallengeSampleChronology.native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)
          (PqxdhInitialOriginForwardPost.program
            (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
            ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
          (PqxdhInitialOriginForwardPost.program_covered
            (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
            ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
          (attach pending.2 after)) := by
  obtain ⟨built, backend, front, history, ambient, initialized, traced, captured⟩ := reached
  have unchanged := (PqxdhLaterChallengeInsideFirst.cut_start _ _ _ _ owner number bit details classified
    _ _ _ front history ambient (attach pending.2 after) captured).1
  subst ambient
  simp only [PqxdhLaterChallengeSampleChronology.native, PqxdhNativeSharedPrefix.initial_source] at initialized traced
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
  exact ⟨front, history, current, captured⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampleActive

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleActive.reached_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleActive.reached_active
