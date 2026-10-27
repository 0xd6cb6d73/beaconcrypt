import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling

/-! Instantiate the full-pair scan relation at the actual shared source compiler and concrete prepared input, retaining the executed shared cache and every private field. -/
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling
section Shared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhInitialPostContext PqxdhNativeSharedPrefix
open PqxdhLaterChallengeBuilderCapture CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I D K X Response Shared Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth : Nat)

/-- The two original shared-ROM scans have the checked full native coupling, after the invertible reassembly of their local state and actual reached ROM cache. No cache is installed or replaced. -/
theorem shared (state : Local A N C) (cache : CtxRO.QueryCache) :
    RelTriple
      (RawCtxSharedPrefixScan.restore attach <$>
        (simulateQ hashImpl (sharedCarried mark origin sender route read index before trace source writer stage
          pre application initializer selector aux initial metadata ready owner number first adversary depth state)).run cache)
      (RawCtxSharedPrefixScan.restore attach <$>
        (simulateQ hashImpl (sharedCarried mark origin sender route read index before trace source writer stage
          pre application initializer selector aux initial metadata ready owner number second adversary depth state)).run cache)
      (PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary) := by
  rw [PqxdhLaterChallengeCutChronology.shared_source, PqxdhLaterChallengeCutChronology.shared_source]
  exact PqxdhLaterChallengeBuilderCoupling.coupled mark origin sender route read index before trace source initial metadata ready
    _ _ _ owner number first second adversary (attach state cache)

end Shared
section Prepared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
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
/-- The actual prepared source input instantiates the complete two-world prefix coupling. The original private callbacks, selected message, first 64-byte expansion and reached ROM cache are the exact ones executed by this sampler. -/
theorem prepared (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      (RawCtxSharedPrefixScan.restore attach <$> (simulateQ hashImpl
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number first adversary)).run cache)
      (RawCtxSharedPrefixScan.restore attach <$> (simulateQ hashImpl
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number second adversary)).run cache)
      (PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary) := by
  apply shared

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling.shared

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling.prepared
