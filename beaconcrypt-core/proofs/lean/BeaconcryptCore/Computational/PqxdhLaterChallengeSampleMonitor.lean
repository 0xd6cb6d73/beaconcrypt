import BeaconcryptCore.Computational.PqxdhLaterChallengeSourceMonitor
import BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology

/-! Preserve the exact sampled source chronology while carrying the private request monitor through its actual prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor
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

/-- The same Builder execution and callback-local cut, with their complete native state and cache; every exact state view yields a marker-preserving actual prefix. This does not identify the state view needed by an inside-challenge argument. -/
def Marked (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache) : Prop :=
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
    (∀ (view : _ → PqxdhFirstRecordConfidentiality.InsState M P (IdentityHandle I) (DhPair setup) (KemHandle K) A
        (BareState 1) RootOracle.QueryCache S (B + 1)) (target : RootOutput) (choice : Option Bool),
      PqxdhLaterChallengeSourceMonitor.Reaches
        (PqxdhLaterChallengeCutChronology.postImpl marker (env).senderId (env).route (env).decode impl) view target
        owner number bit (adversary built.1) ((PqxdhRecordConfidentialityChallenge.initial, (built.2, backend)), choice)
        ((PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)).query details.request.query >>= details.request.next)
        ((details.request.before, ((front, history), ambient)), choice)) ∧
    RawCtxForwardScan.Cut.pending details.callback (attach pending.2 after) ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth) impl
        (PqxdhInitialOriginForwardPost.program marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
        (PqxdhInitialOriginForwardPost.program_covered marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) ambient)

/-- The actual source chronology supplies the annotated prefix at the same reached request and callback cut whenever its wrapper is still unused. -/
theorem reached_marked (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeSampleChronology.Reached original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary pending details cache after)
    (unused : details.request.before.pair = none) :
    Marked original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending details cache after := by
  obtain ⟨built, backend, front, history, ambient, initial, historyReached, cut⟩ := reached
  refine ⟨built, backend, front, history, ambient, initial, ?_, cut⟩
  exact fun view target choice => PqxdhLaterChallengeSourceMonitor.source_unused _ view target owner number bit _ _ _ _ _ _ historyReached choice unused

/-- Any captured request outside the used phase has not yet chosen a challenge pair. -/
theorem phase_unused (details : Details)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .used) :
    details.request.before.pair = none := by
  cases pair : details.request.before.pair with
  | none => rfl
  | some pair =>
      have used := (PqxdhLaterChallengeSavedClassification.phase_used details).mpr (by simp only [pair, Option.isSome_some])
      exact False.elim (classified used)

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor.reached_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor.reached_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor.phase_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor.phase_unused
