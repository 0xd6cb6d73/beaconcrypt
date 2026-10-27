import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation
import BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture

/-! Preserve the source-generated continuation through the actual prepared predecessor scanner and collector. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation
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
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture

open PqxdhLaterChallengePreparedCapture

/-- Every concrete shared-prefix cut retains the original Builder-or-wrapper continuation, without reconstructing an erased function. -/
theorem prefix_continuation (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (reached : Local A (BareState 1) RootOracle.QueryCache)
    (supported : RawCtxForwardScan.Cut.pending (context, details) reached ∈ support
      (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    PqxdhLaterChallengeBuilderContinuation.Continuation owner number bit adversary (context, details) := by
  exact PqxdhLaterChallengeBuilderContinuation.shared_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ supported


/-- The complete collector carries the exact source-generated continuation only on its actual pending branch; completed and cached decisions remain unchanged. -/
theorem run_continuation (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (supported : Sum.inr (pending, details) ∈ support
      (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    PqxdhLaterChallengeBuilderContinuation.Continuation owner number bit adversary (pending.1, details) := by
  simp only [PqxdhLaterChallengePreparedCapture.run, mem_support_bind_iff] at supported
  obtain ⟨cut, reached, collected⟩ := supported
  exact prefix_continuation original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth owner number bit adversary pending.1 details pending.2
    ((collect_pending original callbacks baseImpl kem attachedVerify primitives secret challenge
      (withPost (setup := setup) start owner number bit adversary) output depth cut pending details collected) ▸ reached)

end BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation.prefix_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation.prefix_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation.run_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation.run_continuation
