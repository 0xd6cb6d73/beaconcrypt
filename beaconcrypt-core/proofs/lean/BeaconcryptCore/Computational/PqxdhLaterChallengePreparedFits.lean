-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits

/-! Carry source-derived all-reply continuation allowances through the concrete prepared prefix and original missing-address collector. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits
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

/-- The concrete source prefix supplies both complete wrapper allowances from the original all-reply adversary cap. -/
theorem prefix_fits (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (q : Nat) (bounded : ∀ reply, (adversary reply).IsTotalQueryBound q)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (reached : Local A (BareState 1) RootOracle.QueryCache)
    (supported : RawCtxForwardScan.Cut.pending (context, details) reached ∈ support
      (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    PqxdhLaterChallengeCapturedFits.BothFits owner number q (context, details) := by
  exact PqxdhLaterChallengeCapturedFits.shared_fits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q bounded _ _ _ _ _ supported

/-- The original collector can return a pending callback only at its actual missing-address cut, whose two complete continuations retain the source allowance. -/
theorem run_fits (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (q : Nat) (bounded : ∀ reply, (adversary reply).IsTotalQueryBound q)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (supported : Sum.inr (pending, details) ∈ support
      (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    PqxdhLaterChallengeCapturedFits.BothFits owner number q (pending.1, details) := by
  simp only [PqxdhLaterChallengePreparedCapture.run, mem_support_bind_iff] at supported
  obtain ⟨cut, reached, collected⟩ := supported
  have actual := collect_pending original callbacks baseImpl kem attachedVerify primitives secret challenge
    (withPost (setup := setup) start owner number bit adversary) output depth cut pending details collected
  rw [actual] at reached
  exact prefix_fits original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary q bounded pending.1 details pending.2 reached

end BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits.prefix_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits.prefix_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits.run_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits.run_fits
