import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput
import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology

/-! An earlier successful challenge in the actual prepared sampler leaves its literal source input in the same captured predecessor log. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput
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


/-- The original Builder result and complete wrapper witness retain the earlier challenge input in the captured source log. This concerns the earlier-challenge branch only. -/
def BeforeInput (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache : CtxRO.QueryCache) : Prop :=
  let execution := PqxdhInitialSourceExperiment.execution (RawCtxSelectedInitialConstructor.response64 output)
    start.index start.metadata { start.ready with root := zeroRoot }
    (withPost (setup := setup) start owner number bit adversary).post start.before
  let impl := PqxdhLaterChallengeSampleChronology.native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  let marker := PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage
  ∃ built backend front history ambient,
    (built, backend) ∈ support ((simulateQ impl (simulateQ RawCtxForwardAnnotation.erase
      (PqxdhInitialOriginForwardBuilder.program (env).source marker execution.origin (env).senderId (env).route (env).decode
        execution.initial execution.index execution.metadata execution.ready pure execution.before execution.trace))).run
      (attach (PqxdhPreparedSharedPrefix.state original start output) cache)) ∧
    PqxdhLaterChallengePrefixInput.InputBefore (env).source (env).recordWriter (depth + 1)
        (fun query => localLift (pre query)) (fun reply => localLift (application reply))
        (fun secrets => localLift (initialLocal (env).source start.selectedMessage zeroRoot
          (RawCtxSelectedInitialConstructor.response64 output) secrets))
        (fun query => localLift (selector query)) (fun query => localLift (aux query))
      marker (env).senderId (env).route (env).decode owner number bit
      (adversary built.1)
      ((PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)).query details.request.query >>= details.request.next)
      PqxdhRecordConfidentialityChallenge.initial details.request.before
      (built.2, backend) ((front, history), ambient) pending.2.inputs

/-- Actual prepared-source reachability and the unchanged reached target supply the earlier input, including the complete callback-local scan. -/
theorem reached_input (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache : CtxRO.QueryCache) (after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeSampleChronology.Reached original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after)
    (target : PqxdhRecordConfidentialityChallenge.Target number details.request.before) :
    BeforeInput original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache := by
  obtain ⟨built, backend, front, history, ambient, initialized, reached, captured⟩ := reached
  refine ⟨built, backend, front, history, ambient, initialized, ?_⟩
  exact PqxdhLaterChallengePrefixInput.pending_input (env).source (env).recordWriter (depth + 1)
    (fun query => localLift (pre query)) (fun reply => localLift (application reply))
    (fun secrets => localLift (initialLocal (env).source start.selectedMessage zeroRoot
      (RawCtxSelectedInitialConstructor.response64 output) secrets))
    (fun query => localLift (selector query)) (fun query => localLift (aux query))
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
    owner number bit _ _ _ _ _ _ reached rfl target
    PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth)
    (PqxdhInitialOriginContext.frame (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage)
      (env).senderId (env).route (env).decode) _ _
    (PqxdhInitialOriginForwardPost.program_sound _ _ _ _ _ front history)
    (attach pending.2 after) details.callback captured

/-- The complete prepared sampler supplies the earlier challenge's literal input in its captured log. Its common and cached outputs remain untouched. -/
theorem run_input (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache : CtxRO.QueryCache) (after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number bit adversary)).run cache))
    (target : PqxdhRecordConfidentialityChallenge.Target number details.request.before) :
    BeforeInput original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache :=
  reached_input original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth owner number bit adversary pending details cache after
    (PqxdhLaterChallengeSampleChronology.run_reaches original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after supported) target

end BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput.reached_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput.reached_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput.run_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput.run_input
