import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst

/-! Retain the exact pre-request frontend and parent address in the inside-phase sampled chronology. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampleFirst
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
open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture

open PqxdhLaterChallengePreparedCapture
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "Details" => PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

/-- The actual inside cut retains the pre-request frontend/history and uses its exact captured complete native state as the end of its unchanged source prefix. -/
def First (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache) : Prop :=
  let execution := PqxdhInitialSourceExperiment.execution (RawCtxSelectedInitialConstructor.response64 output)
    start.index start.metadata { start.ready with root := zeroRoot }
    (withPost (setup := setup) start owner number bit adversary).post start.before
  let impl := PqxdhLaterChallengeSampleChronology.native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  let marker := PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage
  ∃ built backend front history,
    (built, backend) ∈ support ((simulateQ impl (simulateQ RawCtxForwardAnnotation.erase
      (PqxdhInitialOriginForwardBuilder.program (env).source marker execution.origin (env).senderId (env).route (env).decode
        execution.initial execution.index execution.metadata execution.ready pure execution.before execution.trace))).run
      (attach (PqxdhPreparedSharedPrefix.state original start output) cache)) ∧
    (∀ (view : _ → PqxdhFirstRecordConfidentiality.InsState M P (IdentityHandle I) (DhPair setup) (KemHandle K) A
        (BareState 1) RootOracle.QueryCache S (B + 1)) (target : RootOutput) (choice : Option Bool),
      PqxdhLaterChallengeSourceMonitor.Reaches
        (PqxdhLaterChallengeCutChronology.postImpl marker (env).senderId (env).route (env).decode impl) view target
        owner number bit (adversary built.1) ((PqxdhRecordConfidentialityChallenge.initial, (built.2, backend)), choice)
        ((PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)).query details.request.query >>= details.request.next)
        ((details.request.before, ((front, history), (attach pending.2 after))), choice)) ∧
    PqxdhLaterChallengeInsideState.FromChallenge owner bit details.request.query front history details.callback ∧
    PqxdhLaterChallengeInsideState.AtAddress owner front details.callback ∧
    RawCtxForwardScan.Cut.pending details.callback (attach pending.2 after) ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth) impl
        (PqxdhInitialOriginForwardPost.program marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
        (PqxdhInitialOriginForwardPost.program_covered marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) (attach pending.2 after))

/-- The inside callback has no earlier primitive effect, so the actual generated prefix ends in the complete same native state stored in the pending packet. -/
theorem reached_first (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeSampleChronology.Reached original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside) :
    First original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending details cache after := by
  obtain ⟨built, backend, front, history, ambient, initial, historyReached, request, address, cut⟩ :=
    PqxdhLaterChallengeSampleInside.reached_inside original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after reached classified
  have unchanged := (PqxdhLaterChallengeInsideFirst.cut_start _ _ _ _ owner number bit details classified _ _ _ front history ambient _ cut).1
  subst ambient
  exact ⟨built, backend, front, history, initial, historyReached, request, address, cut⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampleFirst

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleFirst.reached_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleFirst.reached_first
