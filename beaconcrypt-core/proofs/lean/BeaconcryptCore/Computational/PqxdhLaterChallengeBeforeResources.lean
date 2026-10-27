-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded
import BeaconcryptCore.Computational.PqxdhLaterExecutableResources

/-! Charge the complete source-derived before reduction at the original source callback allowances, including native uniform and permitted primitive work. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (adversary : program.Selection → PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)


local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "CaptureDetails" => Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)
local notation "Post" => PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)


local notation "Output" => PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program


local notation "Carrier" => PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

open PqxdhJointKdf PqxdhNativeSharedPrefix PqxdhFirstRecordConfidentiality PqxdhJointKdfGame RawCtxSelectedMessageDriver RawCtxSelectedParentTable
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Key" => PqxdhLaterChallengeGeneratedBeforeObservation.Key setup program (M := M) (P := P) (I := I) (K := K) (A := A) (X := X) (Response := Response) (KemSK := KemSK)

variable (original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

open PqxdhLaterChallengeBeforeUnguarded

/-- The source callback allowance charges both optional publication callbacks and all retained Post work. -/
def suffixAllowance (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original) (qPost : Nat) : Nat :=
  (1 + ((PqxdhLaterExecutableResources.callbackAllowance setup env callbacks program original baseImpl kem c) + (PqxdhLaterExecutableResources.callbackAllowance setup env callbacks program original baseImpl kem c)) + qPost * (16 * (PqxdhLaterExecutableResources.callbackAllowance setup env callbacks program original baseImpl kem c)))

/-- The guard-free saved client pays the actual source certificate for every uniform callback, including base and permitted decapsulation work and work before optional refusal. -/
theorem client_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original) (qPost : Nat) (bit : Bool) (key : Key)
    (valid : KeyFits setup program owner number qPost key) :
    (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key valid).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute
      (suffixAllowance setup env callbacks program baseImpl kem original c qPost) := by
  classical
  cases key with
  | none => trivial
  | some payload =>
    rcases payload with ⟨credentials, start, output, details, native, parent, target, nonce, next, selection⟩
    simp only [KeyFits] at valid
    simp only [client]
    split
    · simp only [isQueryBoundP_map_iff]
      have bills := PqxdhLaterSavedUniformBounds.complete_cost
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
        (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
        target nonce next (PqxdhInitialSampledParent.marker env.source (start, output)) env.senderId env.route env.decode
        ⟨0, Nat.zero_lt_succ _⟩ AdaptiveCtxDynamicKnownBounds.UniformRoute (PqxdhLaterExecutableResources.callbackAllowance setup env callbacks program original baseImpl kem c)
        (by unfold PqxdhLaterExecutableResources.callbackAllowance; omega)
        (PqxdhLaterExecutableResources.external_uniform setup env callbacks program original attachedVerify primitives baseImpl kem c
          credentials.1 credentials.2 start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
        qPost (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1 parent.material (valid bit)
        (PqxdhLaterChallengeCollectorCoupling.detach native).1
      rw [← PqxdhLaterChallengeSavedMonitor.resume_erase
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
        (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
        target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
        ⟨0, Nat.zero_lt_succ _⟩ owner number bit details (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1 rfl
        parent.material qPost (PqxdhLaterChallengeBeforeConsumer.callback_fits setup owner number qPost details valid) (valid bit)
        (PqxdhLaterChallengeCollectorCoupling.detach native).1 none] at bills
      simpa only [suffixAllowance, isQueryBoundP_map_iff] using bills
    · trivial

/-- The actual full generated prefix and saved continuation both pay uniform work. The proof attachment changes no source call; the suffix uses the original concrete callback, base and decapsulation certificate. -/
theorem compiled_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth qUniformPre : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre) :
    (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (qUniformPre + suffixAllowance setup env callbacks program baseImpl kem original c
        (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget)) := by
  rw [← PqxdhLaterChallengeGeneratedFits.certified_erase setup env callbacks program adversary owner number prefixBit
    attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded, isQueryBoundP_map_iff] at uniformBound
  unfold compiled
  apply isQueryBoundP_bind (m := suffixAllowance setup env callbacks program baseImpl kem original c
    (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget)) ?_
    (fun result _ => client_uniform setup env callbacks program owner number attachedVerify primitives baseImpl kem original c
      _ continuationBit _ _)
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward _).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qUniformPre
  apply AdaptiveCtxSharedTarget.forward_bound
  simpa only [AdaptiveCtxSharedTarget.forward_uniform_class] using uniformBound

/-- All original complete source-prefix class bounds transfer by exact metadata erasure, including cached continuations and every source draw. -/
theorem prefix_class (depth q : Nat) (bit hash : Bool) :
    (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass hash) q ↔
    (PqxdhLaterSharedMessagePrefix.run setup env callbacks program (PqxdhRecordConfidentialityChallenge.post adversary owner number bit)
      attachedVerify primitives baseImpl kem owner number ancestors disclosed depth).IsQueryBoundP (HashClass hash) q := by
  rw [← PqxdhLaterSavedSampler.run_erase setup env callbacks program (PqxdhRecordConfidentialityChallenge.post adversary owner number bit)
    attachedVerify primitives baseImpl kem owner number ancestors disclosed depth, isQueryBoundP_map_iff,
    ← PqxdhLaterChallengeSampler.run_erase setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth, isQueryBoundP_map_iff,
    ← PqxdhLaterChallengeGeneratedContinuation.run_erase setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.client_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.compiled_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.compiled_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.prefix_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources.prefix_class
