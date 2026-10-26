import BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor

/-! The actual generated before-phase cut supplies its source-derived unused-wrapper certificate to the saved compiler and monitor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
open PqxdhJointKdfGame PqxdhNativeSharedPrefix RawCtxSelectedParentTable
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (adversary : program.Selection → PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
    (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- Every supported generated before-phase packet retains an outside callback whose successful result leaves the wrapper unused. This consumes the actual evaluated chronology, including the reached callback state and cache. -/
theorem unused (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.1.2 = some details)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before) :
    PqxdhLaterSavedOutsideSupport.Returns (fun result => result.2.pair = none) details.callback := by
  obtain ⟨selection, _, start, secret, challenge, output, cache, chronology⟩ :=
    PqxdhLaterChallengeCarriedChronology.carried_reaches setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth result stored pending details after supported shape captured
  obtain ⟨built, backend, front, history, ambient, _, _, cut⟩ := chronology
  exact PqxdhLaterChallengeBeforeMonitor.cut_unused _ _ _ _ owner number bit details classified _ _ _ front history ambient _ cut

variable {Y Answer Shared L N C : Type}
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec (IdentityHandle I) (DhPair setup) (KemHandle K) Y Answer Shared)
      (StateT (ExternalState L N C) ProbComp))
    (application : Answer → LocalCallback L N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback L N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl (SelectorSpec baseSpec) (StateT (ExternalState L N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState L N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin (B + 1))

/-- The actual generated before-phase packet feeds the unchanged monitored two-world continuation. Its unused-wrapper condition is derived from that same evaluated source execution; only the maintained explicit alias inequality and operational callback certificate remain. -/
theorem resume_pre (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.1.2 = some details)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost details.callback) (localState : Local L N C)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address details.callback.original) :
    PqxdhFirstRecordConfidentiality.Pre (fun a b => a = b) (fun value => PqxdhLaterChallengeMonitor.Dead value.2)
      (fun value => PqxdhLaterChallengeMonitor.Dead value.2)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next sender route read
        mark monitor owner number false details material qPost fits localState none)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next sender route read
        mark monitor owner number true details material qPost fits localState none) :=
  PqxdhLaterChallengeBeforeMonitor.resume_pre pre application initial selector aux source writer prior target nonce next sender route read
    mark monitor owner number details material qPost fits
    (unused setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      depth result stored pending details after supported shape captured classified) localState separate

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore.unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore.unused
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore.resume_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBefore.resume_pre
