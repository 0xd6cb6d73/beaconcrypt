import BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin
import BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology

/-! The actual generated saved-source comparison retains the source publication trace used to exclude an already-used challenge phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame
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

/-- Erasing the newly carried selection and callback metadata recovers the original supported sampler packet, whose actual source certificate supplies its residual callback allowance and raw descriptor provenance. -/
theorem generated_scope (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (certificate : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program
      (PqxdhRecordConfidentialityChallenge.post adversary owner number bit)) :
    PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program
        (PqxdhRecordConfidentialityChallenge.post adversary owner number bit) certificate) pending.1 ∧
      PqxdhInitialDescriptorScope.Valid env.decode pending.1 := by
  have sampler : (result.1, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅) := by
    rw [← PqxdhLaterChallengeGeneratedContinuation.run_erase setup env callbacks program adversary owner number bit attachedVerify primitives
      baseImpl kem ancestors disclosed depth, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(result, after), supported, rfl⟩
  have saved : (result.1.1, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterSavedSampler.run setup env callbacks program (PqxdhRecordConfidentialityChallenge.post adversary owner number bit)
        attachedVerify primitives baseImpl kem owner number ancestors disclosed depth)).run ∅) := by
    rw [← PqxdhLaterChallengeSampler.run_erase setup env callbacks program adversary owner number bit attachedVerify primitives
      baseImpl kem ancestors disclosed depth, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(result.1, after), sampler, rfl⟩
  have facts := PqxdhLaterSavedSampler.pending_scope setup env callbacks program
    (PqxdhRecordConfidentialityChallenge.post adversary owner number bit) attachedVerify primitives baseImpl kem owner number ancestors
    disclosed certificate depth (result.1.1, after) saved stored pending shape
  exact ⟨facts.1, facts.2.1⟩

/-- The full original saved-source comparison cannot return a true marked target publication from a generated used-phase cut. This transports the literal resumed frame, including its trace and native state; it is not a claim about the nonce-stopped executable compiler. -/
theorem source_not_used (depth : Nat) (position : number.val = depth + 2)
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
    (admitted : PqxdhInitialDescriptorScope.Valid env.decode pending.1)
    (state : RawCtxSelectedReceiveCompiler.State (Local A (BareState 1) RootOracle.QueryCache))
    (finalState : Traced M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (completed : (some true, finalState) ∈ support (PqxdhLaterSavedPostComparison.original pre application initial selector aux env.source
      env.recordWriter prior key target nonce next (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode
      qPost pending.1 material fits state))
    (published : ((owner, number), true) ∈ (tracedProj key finalState).1.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .used := by
  apply PqxdhLaterChallengeSavedClassification.evaluated_not_used setup env callbacks program adversary owner number bit attachedVerify
    primitives baseImpl kem ancestors disclosed depth position result stored pending details after supported shape captured
    (PqxdhInitialNativeRetained.retained env.source env.recordWriter
      (privateTable prior (some ⟨PqxdhInitialBuilderContext.address pending.1.original, material⟩) target
        (RawCtxSelectedMessageKdf.response key nonce next)) (lifted pre application initial selector aux))
    (retainedOf (RawCtxSelectedReceiveCompiler.project state))
    (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
      (realize ⟨PqxdhInitialBuilderContext.address pending.1.original, material⟩ target))
    ((true, (tracedProj key finalState).1), retainedOf (tracedProj key finalState).2) _ rfl published
  exact PqxdhLaterSavedFrameJoin.original_frame_support pre application initial selector aux env.source env.recordWriter prior key target
    nonce next (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode qPost pending.1 material fits state
    admitted true finalState completed

/-- The actual generated packet supplies raw descriptor validity through its original resource certificate, discharging that operational premise of the source-side used-phase exclusion. The complete comparison still receives its explicit supplied component state and universally quantified callbacks. -/
theorem generated_not_used (depth : Nat) (position : number.val = depth + 2)
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
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .used :=
  source_not_used setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    pre application initial selector aux depth position result stored pending details after supported shape captured prior key target nonce next
    qPost material fits
    (generated_scope setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      depth result stored pending after supported shape certificate).2 state finalState completed published

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.generated_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.generated_scope
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.source_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.source_not_used
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.generated_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame.generated_not_used
