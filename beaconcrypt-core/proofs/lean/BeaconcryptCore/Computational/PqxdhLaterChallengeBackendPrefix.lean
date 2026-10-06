-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCoupling
import BeaconcryptCore.Computational.RawCtxSharedPrefixBackend

/-! Couple the actual shared source prefix with its entire interpreted backend, including public-hash observation history. -/
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix
section Shared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhInitialPostContext PqxdhNativeSharedPrefix
open PqxdhLaterChallengeBuilderCapture CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I D K X Response Shared Origin A N C Backend : Type} {extra : OracleSpec ι} {S B : Nat}
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

/-- The two actual shared scans retain a full pair of local state and interpreted backend. Every backend field, including its query history, agrees on the before-admission branch. -/
theorem shared (backend : QueryImpl HashSpec (StateT Backend ProbComp)) (state : Local A N C) (cache : Backend) :
    RelTriple
      (RawCtxSharedPrefixBackend.restore <$>
        (simulateQ backend (sharedCarried mark origin sender route read index before trace source writer stage
          pre application initializer selector aux initial metadata ready owner number first adversary depth state)).run cache)
      (RawCtxSharedPrefixBackend.restore <$>
        (simulateQ backend (sharedCarried mark origin sender route read index before trace source writer stage
          pre application initializer selector aux initial metadata ready owner number second adversary depth state)).run cache)
      (PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary) := by
  unfold sharedCarried
  rw [RawCtxSharedPrefixBackend.evaluated, RawCtxSharedPrefixBackend.evaluated]
  exact PqxdhLaterChallengeBuilderCoupling.coupled mark origin sender route read index before trace source initial metadata ready
    _ _ _ owner number first second adversary (state, cache)

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
variable {ι M P I K X Response A KemSK Backend : Type} {baseSpec : OracleSpec ι} {S B : Nat}
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
/-- The literal prepared source input instantiates the full backend coupling. No backend history is projected out, and all complete or post-admission outcomes retain their full actual distributions. -/
theorem prepared (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (backend : QueryImpl HashSpec (StateT Backend ProbComp)) (cache : Backend) :
    RelTriple
      (RawCtxSharedPrefixBackend.restore <$> (simulateQ backend
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number first adversary)).run cache)
      (RawCtxSharedPrefixBackend.restore <$> (simulateQ backend
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number second adversary)).run cache)
      (PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary) := by
  apply shared

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix.shared

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix.prepared
