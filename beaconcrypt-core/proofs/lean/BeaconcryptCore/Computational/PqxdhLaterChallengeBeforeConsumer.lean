import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation
import BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBefore
import BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds

/-! Execute the actual source-derived before callback with its literal private credentials and retained parent material, keeping all refusal and terminal monitor events. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer
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

/-- Only the actual terminal designation/finish-opening restriction is added to the already wrapped source decision. Optional refusal stays false. -/
noncomputable def decision
    (result : Option Bool × PqxdhLaterChallengeMonitor.State M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)) : Bool := by
  classical
  exact if PqxdhLaterChallengeMonitor.Dead result.2 then false else result.1.getD false

/-- Both literal outside wrappers are billed at the same cap. The callback alone is insufficient to bound the adversary's full saved continuation. -/
def Fits (qPost : Nat) (details : CaptureDetails) : Prop :=
  ∀ bit, PqxdhInitialOriginCertificates.Fits qPost (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1

/-- The joint complete-source allowance also bounds the callback before its carried outside wrapper. -/
theorem callback_fits (qPost : Nat) (details : CaptureDetails)
    (fits : Fits setup owner number qPost details) :
    PqxdhInitialOriginCertificates.Fits qPost details.callback :=
  PqxdhLaterChallengeSavedMonitor.callback_fits _ details.callback qPost (fits false)

/-- The literal saved before callback and source-carried outside continuation. Invalid resource certificates and address aliases are explicit excluded branches; no source request is removed from an accepted branch. -/
noncomputable def client (qPost : Nat) (bit : Bool) (key : Key) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := by
  classical
  exact match key with
  | none => pure false
  | some (credentials, start, output, details, native, parent, target, nonce, next, _) =>
    if fits : Fits setup owner number qPost details then
      if RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address details.callback.original then
        decision setup <$> PqxdhLaterChallengeSavedMonitor.resume
          (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
          (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
          (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
          (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
          target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
          ⟨0, Nat.zero_lt_succ _⟩ owner number bit details parent.material qPost (callback_fits setup owner number qPost details fits)
          (PqxdhLaterChallengeCollectorCoupling.detach native).1 none
      else pure false
    else pure false

/-- The actual generated source prefix supplies the chronology for this exact callback. Both monitored clients retain the original optional result and all callback work; parent alias and resource exclusions agree in both worlds. -/
theorem generated_pre (depth qPost : Nat) (sourceBit : Bool)
    (result : Carrier × Option program.Selection) (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number sourceBit
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅)) :
    Pre (fun a b => a = b) (fun a => a = false) (fun b => b = false)
      (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost false
        (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, after)))
      (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost true
        (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, after))) := by
  classical
  rcases result with ⟨⟨⟨credentials, ⟨⟨⟨packet, parent⟩, target⟩, nonce, next⟩⟩, captured⟩, selection⟩
  rcases packet with decision | ⟨stored, decision | pending⟩
  · exact Pre.pure rfl
  · exact Pre.pure rfl
  · cases captured with
    | none => exact Pre.pure rfl
    | some details =>
      simp only [PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey]
      split
      · rename_i before
        simp only [client]
        split
        · rename_i fits
          split
          · rename_i separate
            have paired := PqxdhLaterChallengeSourceBefore.generated_resume_pre setup env callbacks program adversary
              owner number sourceBit attachedVerify primitives baseImpl kem ancestors disclosed
              (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
              (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
              (initialLocal (A := A) (N := BareState 1) (env0).source stored.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response stored))
              (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
              (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) depth
              (((credentials, (((Sum.inr (stored, Sum.inr pending), parent), target), nonce, next)), some details), selection)
              stored pending details after supported rfl rfl before
              (view (productionStream env.source.crypto) pending.2.store.1) target nonce next ⟨0, Nat.zero_lt_succ _⟩
              qPost parent.material (callback_fits setup owner number qPost details fits) pending.2 separate
            exact pre_map paired _ _ (fun _ _ same => congrArg _ same)
              (fun _ dead => by simp only [decision, ite_eq_left dead])
              (fun _ dead => by simp only [decision, ite_eq_left dead])
          · exact Pre.pure rfl
        · exact Pre.pure rfl
      · exact Pre.pure rfl

/-- The complete concrete monitored continuation has equal true mass from any one supplied full random interpreter state. No state component is reset at the source cut. -/
theorem generated_random (depth qPost : Nat) (sourceBit : Bool)
    (result : Carrier × Option program.Selection) (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number sourceBit
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (state : RandomState) :
    𝒟[Prod.fst <$> (simulateQ (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
      (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost false
        (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, after)))).run state] {true} =
    𝒟[Prod.fst <$> (simulateQ (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
      (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost true
        (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, after)))).run state] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact pre_event_vcvioLegacy (confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto)
    (fun m0 m1 => identRandom m0 m1)
    (generated_pre setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost sourceBit result after supported)
    (fun a => a = true) (fun b => b = true) (fun a b same => by rw [same])
    (fun a dead => by simp [dead]) (fun b dead => by simp [dead])
    (fun m0 m1 equal => random_compatible m0 m1 (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto equal) state

/-- Every accepted before continuation bills its saved operation and the complete carried outside program. The three bounds count attempted selected seals, adaptive raw openings and routed public hash work, including execution before refusal. -/
theorem client_bills (qPost : Nat) (bit : Bool) (key : Key) :
    (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + qPost) ∧
    (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + qPost) ∧
    (client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (1 + qPost) := by
  classical
  unfold client
  split
  · exact ⟨by trivial, by trivial, by trivial⟩
  · rename_i credentials start output details native parent target nonce next selection
    split
    · rename_i fits
      split
      · simp only [isQueryBoundP_map_iff]
        have bills := PqxdhLaterSavedPostBounds.component_bills
          (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
          (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
          (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
          (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
          target nonce next (PqxdhInitialSampledParent.marker env.source (start, output)) env.senderId env.route env.decode
          ⟨0, Nat.zero_lt_succ _⟩ qPost (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1
          parent.material (fits bit) (PqxdhLaterChallengeCollectorCoupling.detach native).1
        rw [← PqxdhLaterChallengeSavedMonitor.resume_erase
          (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
          (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
          (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
          (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
          (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
          target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
          ⟨0, Nat.zero_lt_succ _⟩ owner number bit details (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1 rfl parent.material qPost
          (callback_fits setup owner number qPost details fits) (fits bit)
          (PqxdhLaterChallengeCollectorCoupling.detach native).1 none] at bills
        simpa only [isQueryBoundP_map_iff] using bills
      · exact ⟨by trivial, by trivial, by trivial⟩
    · exact ⟨by trivial, by trivial, by trivial⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.callback_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.callback_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.generated_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.generated_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.generated_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.generated_random

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer.client_bills
