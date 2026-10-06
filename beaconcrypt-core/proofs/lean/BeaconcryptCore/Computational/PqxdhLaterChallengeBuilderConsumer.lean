-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded

/-! Run the actual initial Builder callback followed by its selected adaptive source continuation with the same private monitor. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer
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

/-- A callback-only Builder has a pure outside continuation, so its logical Post allowance is structural rather than a tested semantic guard. Primitive and publication work is still charged by the callback compiler. -/
theorem only_fits
    (saved : PqxdhInitialBuilderContext.Builder (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) PqxdhInitialBuilderContext.BuildResult S (B + 1))
    (trace : PqxdhInitialOriginPost.Trace Bool S (B + 1)) (origin : Option Bool) (qPost : Nat) :
    PqxdhInitialOriginCertificates.Fits qPost (PqxdhLaterChallengeSavedMonitor.builderOnly saved trace origin) := by
  exact fun _ => by trivial

/-- Resume the actual normalized initial Builder and its selected original adversary. Only the explicit byte-address alias exclusion remains; no semantic budget predicate is tested. -/
noncomputable def client (qPost : Nat) (bit : Bool) (key : Key) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := by
  classical
  exact match key with
  | none => pure false
  | some (_, _, _, _, _, _, _, _, _, none) => pure false
  | some (credentials, start, output, callback, native, parent, target, nonce, next, some selection) =>
    match callback.original with
    | .inl _ => pure false
    | .inr saved =>
      let normalized := PqxdhLaterChallengeSavedMonitor.builderOnly saved callback.trace callback.origin
      if RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address normalized.original then
        PqxdhLaterChallengeBeforeConsumer.decision setup <$> PqxdhLaterChallengeSavedMonitor.builderResume
          (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
          (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
          (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
          (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
          target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
          ⟨0, Nat.zero_lt_succ _⟩ owner number bit (adversary selection) normalized parent.material qPost
          (only_fits setup saved callback.trace callback.origin qPost) (PqxdhLaterChallengeCollectorCoupling.detach native).1
      else pure false

/-- The initial Builder executes one identical callback and enters its real selected wrapper from the unused initial state. The monitored pair is identical until an explicit terminal event. -/
theorem client_pre (qPost : Nat) (key : Key) :
    Pre (fun a b => a = b) (fun a => a = false) (fun b => b = false)
      (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost false key)
      (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost true key) := by
  classical
  rcases key with _ | ⟨credentials, start, output, ⟨original, trace, origin⟩, native, parent, target, nonce, next, selection⟩
  · exact Pre.pure rfl
  · cases selection with
    | none => exact Pre.pure rfl
    | some selection =>
      cases original with
      | inl request => exact Pre.pure rfl
      | inr saved =>
        simp only [client]
        split
        · rename_i separate
          have paired := PqxdhLaterChallengeSavedMonitor.builder_pre
            (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
            (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
            (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
            (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
            (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
            target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
            ⟨0, Nat.zero_lt_succ _⟩ owner number (adversary selection)
            (PqxdhLaterChallengeSavedMonitor.builderOnly saved trace origin) parent.material qPost
            (only_fits setup saved trace origin qPost) (PqxdhLaterChallengeCollectorCoupling.detach native).1 separate
          exact pre_map paired _ _ (fun _ _ same => congrArg _ same)
            (fun _ dead => by simp only [PqxdhLaterChallengeBeforeConsumer.decision, ite_eq_left dead])
            (fun _ dead => by simp only [PqxdhLaterChallengeBeforeConsumer.decision, ite_eq_left dead])
        · exact Pre.pure rfl

/-- The complete Builder continuation has the same true probability from any one full ordinary random state, preserving all backend histories and refusal mass. -/
theorem client_random (qPost : Nat) (key : Key) (state : RandomState) :
    𝒟[Prod.fst <$> (simulateQ (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
      (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost false key)).run state] {true} =
    𝒟[Prod.fst <$> (simulateQ (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
      (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost true key)).run state] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact pre_event (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
    (fun m0 m1 => identRandom m0 m1)
    (client_pre setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost key)
    (fun a => a = true) (fun b => b = true) (fun a b same => by rw [same])
    (fun a dead => by simp [dead]) (fun b dead => by simp [dead])
    (fun m0 m1 equal => random_compatible m0 m1 (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto equal) state

/-- Restore the selected actual adaptive wrapper around the callback-only Builder, preserving every saved field, publication trace and origin. -/
noncomputable def whole (bit : Bool) (selection : program.Selection)
    (saved : PqxdhInitialBuilderContext.Builder (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) PqxdhInitialBuilderContext.BuildResult S (B + 1))
    (trace : PqxdhInitialOriginPost.Trace Bool S (B + 1)) (origin : Option Bool) :
    PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) Bool Bool S (B + 1) :=
  ⟨.inr { saved with outside := fun reply =>
      PqxdhLaterChallengeCapture.wrapped owner number bit (adversary selection reply) PqxdhRecordConfidentialityChallenge.initial }, trace, origin⟩

/-- The entire literal selected wrapper is charged to its original all-reply source budget; callback work is billed separately by the compiler. -/
theorem whole_fits (qPost : Nat) (bit : Bool) (selection : program.Selection)
    (saved : PqxdhInitialBuilderContext.Builder (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) PqxdhInitialBuilderContext.BuildResult S (B + 1))
    (trace : PqxdhInitialOriginPost.Trace Bool S (B + 1)) (origin : Option Bool)
    (bounded : ∀ reply, (adversary selection reply).IsTotalQueryBound qPost) :
    PqxdhInitialOriginCertificates.Fits qPost (whole setup program adversary owner number bit selection saved trace origin) := by
  exact fun reply => PqxdhLaterChallengeCapturedFits.wrapped_total owner number bit (adversary selection reply)
    PqxdhRecordConfidentialityChallenge.initial qPost (bounded reply)

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.only_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.only_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.client_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.client_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.client_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.client_random

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.whole_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer.whole_fits
