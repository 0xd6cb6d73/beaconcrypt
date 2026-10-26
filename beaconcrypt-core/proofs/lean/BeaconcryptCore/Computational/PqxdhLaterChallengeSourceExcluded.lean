import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFrame
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded

/-! Exclude the inside challenge phase in the complete original saved-source comparison of the same generated carrier. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded
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

/-- Erasing only the newly carried selection recovers the original full sampler support and retains the same inside exclusion for the actual retained executor. -/
theorem evaluated_not_inside {OtherA OtherN OtherC : Type} (depth : Nat) (position : number.val = depth + 2)
    (carrier : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedExcluded.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (carrier, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : carrier.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : carrier.1.2 = some details)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1) × PqxdhInitialOriginPost.Trace Bool S (B + 1))) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained env.source env.recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1
        (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  have erased : (carrier.1, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅) := by
    rw [← PqxdhLaterChallengeGeneratedContinuation.run_erase setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(carrier, after), supported, rfl⟩
  exact PqxdhLaterChallengeGeneratedExcluded.run_not_inside setup env callbacks program adversary owner number bit attachedVerify
    primitives baseImpl kem ancestors disclosed depth position carrier.1 stored pending details after erased shape captured
    prior entry target full external atParent before result completed accepted published

/-- The actual original saved-source comparison excludes the inside phase at depth+2; its literal saved parent descriptor supplies the address relation. This retains complete source trace/state and does not claim equivalence with the nonce-stopped compiler. -/
theorem source_not_inside (depth : Nat) (position : number.val = depth + 2)
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
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  apply evaluated_not_inside setup env callbacks program adversary owner number bit attachedVerify
    primitives baseImpl kem ancestors disclosed depth position result stored pending details after supported shape captured
    prior ⟨PqxdhInitialBuilderContext.address pending.1.original, material⟩ target
    (RawCtxSelectedMessageKdf.response key nonce next) (lifted pre application initial selector aux) rfl
    (retainedOf (RawCtxSelectedReceiveCompiler.project state))
    ((true, (tracedProj key finalState).1), retainedOf (tracedProj key finalState).2) _ rfl published
  exact PqxdhLaterSavedFrameJoin.original_frame_support pre application initial selector aux env.source env.recordWriter prior key target
    nonce next (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode qPost pending.1 material fits state
    admitted true finalState completed

/-- The same actual generated source certificate supplies descriptor validity, so the retained inside-event exclusion needs no new admission premise. Residual Fits and the complete supplied comparison state remain explicit. -/
theorem generated_not_inside (depth : Nat) (position : number.val = depth + 2)
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
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside :=
  source_not_inside setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    pre application initial selector aux depth position result stored pending details after supported shape captured prior key target nonce next
    qPost material fits
    (PqxdhLaterChallengeGeneratedFrame.generated_scope setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      depth result stored pending after supported shape certificate).2 state finalState completed published

end BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.evaluated_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.evaluated_not_inside

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.source_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.source_not_inside

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.generated_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSourceExcluded.generated_not_inside
