import BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded
import BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedSource
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume

/-! Identify the actual remaining before-phase source request and retain its literal saved-start origin predicate for the monitored two-world continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
open PqxdhNativeSharedPrefix PqxdhFirstRecordConfidentiality RawCtxSelectedParentTable PqxdhSelectedFirstRecord RawCtxSelectedMessageDriver
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

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec (IdentityHandle I) (DhPair setup) (KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A (BareState 1) RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A (BareState 1) RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A (BareState 1) RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl (SelectorSpec baseSpec) (StateT (ExternalState A (BareState 1) RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A (BareState 1) RootOracle.QueryCache) ProbComp))

private theorem request_not_builder
    (details : PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .builder := by
  unfold PqxdhLaterChallengeSavedClassification.phase
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- The actual original saved-source target event can only occur before the challenge when request metadata is present. Both excluded phases are discharged by that same generated execution, without a new phase premise. -/
theorem generated_before (depth : Nat) (position : number.val = depth + 2)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (captured : result.1.2 = some details)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (qPost : Nat) (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost pending.1)
    (certificate : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program
      (PqxdhRecordConfidentialityChallenge.post adversary owner number bit))
    (state : RawCtxSelectedReceiveCompiler.State (Local A (BareState 1) RootOracle.QueryCache))
    (finalState : Traced M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (completed : (some true, finalState) ∈ support (PqxdhLaterSavedPostComparison.original pre application initial selector aux env.source
      env.recordWriter prior key target nonce next (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode
      qPost pending.1 material fits state))
    (published : ((owner, number), true) ∈ (tracedProj key finalState).1.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) = .before := by
  have notUsed := PqxdhLaterChallengeGeneratedFrame.generated_not_used setup env callbacks program adversary owner number bit
    attachedVerify primitives baseImpl kem ancestors disclosed pre application initial selector aux depth position result stored pending
    details after supported shape captured prior key target nonce next qPost material fits certificate state finalState completed published
  have notInside := PqxdhLaterChallengeSourceExcluded.generated_not_inside setup env callbacks program adversary owner number bit
    attachedVerify primitives baseImpl kem ancestors disclosed pre application initial selector aux depth position result stored pending
    details after supported shape captured prior key target nonce next qPost material fits certificate state finalState completed published
  have notBuilder := request_not_builder setup details
  cases classified : PqxdhLaterChallengeSavedClassification.phase (some details) <;> simp_all

/-- The actual generated callback cut and literal stored-start image instantiate the full two-world saved before-resume coupling. This is a continuation theorem for the same packet, not a coupling of independently generated prefixes. -/
theorem generated_resume_pre (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (captured : result.1.2 = some details)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (monitor : Fin (B + 1))
    (qPost : Nat) (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (localState : Local A (BareState 1) RootOracle.QueryCache)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address details.callback.original) :
    Pre (fun a b => a = b) (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux env.source env.recordWriter prior target nonce next
        env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source stored) monitor owner number false
        details material qPost fits localState none)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux env.source env.recordWriter prior target nonce next
        env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source stored) monitor owner number true
        details material qPost fits localState none) := by
  obtain ⟨selection, chosen, start, secret, challenge, output, cache, image, reached⟩ :=
    PqxdhLaterChallengeCarriedSource.carried_source setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth result stored pending details after supported shape captured
  obtain ⟨built, backend, front, history, ambient, initialized, traced, cut⟩ := reached
  have marker : PqxdhInitialSampledParent.marker env.source stored =
      PqxdhInitialSelectedOrigin.mark env.source start.selectedMessage := by
    rw [image]
    rfl
  rw [marker]
  exact PqxdhLaterChallengeBeforeResume.resume_pre pre application initial selector aux env.source env.recordWriter prior target
    nonce next env.senderId env.route env.decode (PqxdhInitialSelectedOrigin.mark env.source start.selectedMessage) monitor
    owner number bit details classified (PqxdhInitialNativeAuditCarried.selected depth)
    (PqxdhNativeSharedPrefix.native_selection depth) _ front history ambient (attach pending.2 after) cut
    material qPost fits localState separate

/-- The original generated saved-source target event supplies the before phase for the complete same-callback two-world continuation. The actual comparison and callback resource certificates, supplied state and alias separation remain explicit. -/
theorem generated_event_pre (depth : Nat) (position : number.val = depth + 2)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (captured : result.1.2 = some details)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (qPost : Nat) (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost pending.1)
    (certificate : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program
      (PqxdhRecordConfidentialityChallenge.post adversary owner number bit))
    (state : RawCtxSelectedReceiveCompiler.State (Local A (BareState 1) RootOracle.QueryCache))
    (finalState : Traced M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (completed : (some true, finalState) ∈ support (PqxdhLaterSavedPostComparison.original pre application initial selector aux env.source
      env.recordWriter prior key target nonce next (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode
      qPost pending.1 material fits state))
    (published : ((owner, number), true) ∈ (tracedProj key finalState).1.2.published)
    (monitor : Fin (B + 1))
    (callbackFits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (localState : Local A (BareState 1) RootOracle.QueryCache)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address details.callback.original) :
    Pre (fun a b => a = b) (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux env.source env.recordWriter prior target nonce next
        env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source stored) monitor owner number false
        details material qPost callbackFits localState none)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux env.source env.recordWriter prior target nonce next
        env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source stored) monitor owner number true
        details material qPost callbackFits localState none) :=
  generated_resume_pre setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    pre application initial selector aux depth result stored pending details after supported shape captured
    (generated_before setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      pre application initial selector aux depth position result stored pending details after supported shape captured prior key target nonce next
      qPost material fits certificate state finalState completed published)
    prior target nonce next monitor qPost material callbackFits localState separate

end BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_before

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_resume_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_resume_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_event_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore.generated_event_pre
