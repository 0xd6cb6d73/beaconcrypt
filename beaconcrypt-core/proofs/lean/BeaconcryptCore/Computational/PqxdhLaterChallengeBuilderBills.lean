-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResources

/-! Charge the actual initial Builder callback and its complete selected adaptive continuation. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills
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
local notation "Key" => PqxdhLaterChallengeRandomEarly.SourceKey setup program (M := M) (P := P) (I := I) (K := K) (A := A) (X := X) (Response := Response) (KemSK := KemSK)

open PqxdhLaterChallengeBuilderConsumer

/-- The initial Builder and every adaptive outside request are charged, including work before publication failure or nonce refusal. -/
theorem client_bills (qPost : Nat) (bit : Bool) (key : Key)
    (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound qPost) :
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + qPost) ∧
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + qPost) ∧
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (1 + qPost) := by
  classical
  rcases key with _ | ⟨credentials, start, output, ⟨original, trace, origin⟩, native, parent, target, nonce, next, selection⟩
  · exact ⟨by trivial, by trivial, by trivial⟩
  · cases selection with
    | none => exact ⟨by trivial, by trivial, by trivial⟩
    | some selection =>
      cases original with
      | inl request => exact ⟨by trivial, by trivial, by trivial⟩
      | inr saved =>
        simp only [client]
        split
        · simp only [isQueryBoundP_map_iff]
          have fits := whole_fits setup program adversary owner number qPost bit selection saved trace origin (bounded selection)
          have bills := PqxdhLaterSavedPostBounds.component_bills
            (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
            (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
            (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
            target nonce next (PqxdhInitialSampledParent.marker env.source (start, output)) env.senderId env.route env.decode
            ⟨0, Nat.zero_lt_succ _⟩ qPost (whole setup program adversary owner number bit selection saved trace origin)
            parent.material fits (PqxdhLaterChallengeCollectorCoupling.detach native).1
          rw [← PqxdhLaterChallengeSavedMonitor.builder_erase
            (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
            (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
            (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
            target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
            ⟨0, Nat.zero_lt_succ _⟩ owner number bit (adversary selection)
            (whole setup program adversary owner number bit selection saved trace origin) _ rfl rfl parent.material qPost
            (only_fits setup saved trace origin qPost) fits (PqxdhLaterChallengeCollectorCoupling.detach native).1] at bills
          simpa only [isQueryBoundP_map_iff, whole, PqxdhLaterChallengeSavedMonitor.builderOnly] using bills
        · exact ⟨by trivial, by trivial, by trivial⟩

variable (original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Initial Builder work and the complete selected continuation pay the original source callback, base, decapsulation and auxiliary allowances, including work before optional refusal. -/
theorem client_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (qPost : Nat) (bit : Bool) (key : Key)
    (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound qPost) :
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute
      (PqxdhLaterChallengeBeforeResources.suffixAllowance setup env callbacks program baseImpl kem original c qPost) := by
  classical
  rcases key with _ | ⟨credentials, start, output, ⟨original, trace, origin⟩, native, parent, target, nonce, next, selection⟩
  · trivial
  · cases selection with
    | none => trivial
    | some selection =>
      cases original with
      | inl request => trivial
      | inr saved =>
        simp only [client]
        split
        · simp only [isQueryBoundP_map_iff]
          have fits := whole_fits setup program adversary owner number qPost bit selection saved trace origin (bounded selection)
          have bills := PqxdhLaterSavedUniformBounds.complete_cost
            (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
            (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
            (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
            target nonce next (PqxdhInitialSampledParent.marker env.source (start, output)) env.senderId env.route env.decode
            ⟨0, Nat.zero_lt_succ _⟩ AdaptiveCtxDynamicKnownBounds.UniformRoute
            (PqxdhLaterExecutableResources.callbackAllowance setup env callbacks program original baseImpl kem c)
            (by unfold PqxdhLaterExecutableResources.callbackAllowance; omega)
            (PqxdhLaterExecutableResources.external_uniform setup env callbacks program original attachedVerify primitives baseImpl kem c
              credentials.1 credentials.2 start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            qPost (whole setup program adversary owner number bit selection saved trace origin)
            parent.material fits (PqxdhLaterChallengeCollectorCoupling.detach native).1
          rw [← PqxdhLaterChallengeSavedMonitor.builder_erase
            (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
            (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
            (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
            target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
            ⟨0, Nat.zero_lt_succ _⟩ owner number bit (adversary selection)
            (whole setup program adversary owner number bit selection saved trace origin) _ rfl rfl parent.material qPost
            (only_fits setup saved trace origin qPost) fits (PqxdhLaterChallengeCollectorCoupling.detach native).1] at bills
          simpa only [PqxdhLaterChallengeBeforeResources.suffixAllowance, isQueryBoundP_map_iff, whole, PqxdhLaterChallengeSavedMonitor.builderOnly] using bills
        · trivial

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills.client_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills.client_uniform
