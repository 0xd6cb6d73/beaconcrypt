import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation
import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor

/-! Classify each generated saved cut against the wrapper's single challenge and instantiate the saved monitor with the actual captured callback and original continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality

/-- Position of a stored cut relative to the wrapper's single challenge, read only from the carried source metadata. -/
inductive Phase where
  /-- The initial Builder, before the wrapper has started. -/
  | builder
  /-- An ordinary or immediately rejected request while the challenge is unused. -/
  | before
  /-- The admitted challenge's own callback. -/
  | inside
  /-- A request after the challenge was already chosen. -/
  | used
  deriving DecidableEq

section Classify
variable {ι M P I D K Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Absent request metadata is the initial Builder. Otherwise the request's own pre-query wrapper state and query decide the phase. -/
def phase : Option (PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B) → Phase
  | none => .builder
  | some details => match details.request.before.pair, details.request.query with
    | some _, _ => .used
    | none, .inl _ => .before
    | none, .inr (left, right) => if left.length = right.length then .inside else .before

/-- The used phase is exactly a wrapper that had already chosen its challenge before the captured request. -/
theorem phase_used (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B) :
    phase (some details) = .used ↔ details.request.before.pair.isSome := by
  rcases details with ⟨⟨query, ⟨pair, reply, other⟩, next⟩, callback⟩
  rcases pair with _ | pair
  · constructor
    · intro classified
      rcases query with request | ⟨left, right⟩
      · simp only [phase, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · simp only [phase] at classified
          rw [ite_eq_left equal] at classified
          cases classified
        · simp only [phase] at classified
          rw [ite_eq_right equal] at classified
          cases classified
    · intro impossible
      cases impossible
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

end Classify

section Marker
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- In the pre-challenge phase the monitor leaves its private marker unset at the captured request, whatever the reached instrumented state. -/
theorem before_record (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (state : InsState M P I D K A N C S B) (classified : phase (some details) = .before) :
    PqxdhLaterChallengeMonitor.record target owner details.request.query details.request.before (state, none) = none := by
  rcases details with ⟨⟨query, ⟨pair, reply, other⟩, next⟩, callback⟩
  rcases pair with _ | pair
  · rcases query with request | ⟨left, right⟩
    · rfl
    · by_cases equal : left.length = right.length
      · simp only [phase] at classified
        rw [ite_eq_left equal] at classified
        cases classified
      · simp only [PqxdhLaterChallengeMonitor.record]
        rw [ite_eq_left (Or.inr equal)]
  · simp only [phase, reduceCtorEq] at classified

/-- Inside the admitted challenge's callback the monitor's marker is the selected-input condition of the instrumented state before that callback. A cut inside the callback does not carry that state, so this phase stays an explicit obligation. -/
theorem inside_record (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (state : InsState M P I D K A N C S B) (classified : phase (some details) = .inside) :
    PqxdhLaterChallengeMonitor.record target owner details.request.query details.request.before (state, none) =
      some (@decide (PqxdhLaterChallengeMonitor.Selected target owner state) (Classical.propDecidable _)) := by
  rcases details with ⟨⟨query, ⟨pair, reply, other⟩, next⟩, callback⟩
  rcases pair with _ | pair
  · rcases query with request | ⟨left, right⟩
    · simp only [phase, reduceCtorEq] at classified
    · by_cases equal : left.length = right.length
      · simp only [PqxdhLaterChallengeMonitor.record]
        rw [ite_eq_right (by rintro (impossible | unequal) <;> [cases impossible; exact unequal equal])]
      · simp only [phase] at classified
        rw [ite_eq_right equal] at classified
        cases classified
  · simp only [phase, reduceCtorEq] at classified

end Marker

section Generated
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
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
variable {Y Answer Shared L N C : Type}
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec (IdentityHandle I) (DhPair setup) (KemHandle K) Y Answer Shared)
      (StateT (ExternalState L N C) ProbComp))
    (application : Answer → LocalCallback L N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback L N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl (SelectorSpec baseSpec) (StateT (ExternalState L N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState L N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin (B + 1))

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
    (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "Carrier" => PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

/-- Builder phase: the carried selection's literal wrapper is the stored Builder's outside continuation, and the complete saved program is the monitored Builder resume from the unused initial wrapper with an unset marker. The adversary receives only `adversary selection`, as in the original experiment. -/
theorem generated_builder (depth : Nat) (result : Carrier) (stored : Input × HmacBlock) (pending : Pending)
    (supported : result ∈ support (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (absent : result.1.2 = none)
    (saved : PqxdhInitialBuilderContext.Builder (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))
    (same : pending.1.original = .inr saved)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost pending.1) (localState : Local L N C) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection ∧
      saved.outside = (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (adversary selection reply)
        PqxdhRecordConfidentialityChallenge.initial) ∧
      Prod.map id Prod.fst <$> PqxdhLaterChallengeSavedMonitor.builderResume pre application initial selector aux source writer prior
        target nonce next sender route read mark monitor owner number bit (adversary selection)
        (PqxdhLaterChallengeSavedMonitor.builderOnly saved pending.1.trace pending.1.origin) material qPost
        (PqxdhLaterChallengeSavedMonitor.builder_fits pending.1 saved same qPost fits) localState =
      PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route
        read monitor qPost pending.1 material fits localState := by
  obtain ⟨selection, carried, post, valid⟩ := PqxdhLaterChallengeGeneratedContinuation.run_capture setup env callbacks program
    adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth result stored pending supported shape
  rw [absent] at valid
  obtain ⟨found, original, outside⟩ := valid
  rw [same] at original
  cases original
  exact ⟨selection, carried, post, outside, PqxdhLaterChallengeSavedMonitor.builder_erase pre application initial selector aux source
    writer prior target nonce next sender route read mark monitor owner number bit (adversary selection) pending.1 saved same outside
    material qPost _ fits localState⟩

/-- Request phases: the stored descriptor is the actual captured callback joined to the request's carried continuation, the callback's allowance is derived from the descriptor's own certificate, and the complete saved program is the monitored resume of exactly that callback and continuation. The carried selection fixes the stored Post; `Joined` does not mention it, and `details.request.next` is not related to `adversary selection` by this theorem; see `GeneratedChronology.run_reaches`. The marker is any supplied value; `before_record` shows that the monitor's `record` keeps an unset marker unset at a before-phase request; that the marker is unset at the cut remains open. -/
theorem generated_request (depth : Nat) (result : Carrier) (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))
    (supported : result ∈ support (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (captured : result.1.2 = some details)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost pending.1) (localState : Local L N C) (choice : Option Bool) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection ∧
      PqxdhLaterChallengeCapture.Joined owner number bit (pending.1, details) ∧
      ∃ callbackFits : PqxdhInitialOriginCertificates.Fits qPost details.callback,
        Prod.map id Prod.fst <$> PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior
          target nonce next sender route read mark monitor owner number bit details material qPost callbackFits localState choice =
        PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route
          read monitor qPost pending.1 material fits localState := by
  obtain ⟨selection, carried, post, valid⟩ := PqxdhLaterChallengeGeneratedContinuation.run_capture setup env callbacks program
    adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth result stored pending supported shape
  rw [captured] at valid
  change PqxdhLaterChallengeCapture.Joined owner number bit (pending.1, details) at valid
  have callbackFits : PqxdhInitialOriginCertificates.Fits qPost details.callback := by
    have whole := fits
    change pending.1 = PqxdhLaterChallengeCapture.append _ details.callback at valid
    rw [valid] at whole
    exact PqxdhLaterChallengeSavedMonitor.callback_fits _ _ qPost whole
  exact ⟨selection, carried, post, valid, callbackFits, PqxdhLaterChallengeSavedMonitor.resume_erase pre application initial selector
    aux source writer prior target nonce next sender route read mark monitor owner number bit details pending.1 valid material qPost
    callbackFits fits localState choice⟩

local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Base" => PqxdhInitialPostContext.Base (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
  (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared S (B + 1)

/-- Used phase: at target position `depth + 2` the complete generated sampler excludes it whenever the frame-level saved continuation returns the original true output with the marked target publication. This reads Chronology64's `run_not_used` through erasure of the carried selection; it is an event exclusion, not a probability bound. -/
theorem evaluated_not_used {Other : Type} (depth : Nat) (position : number.val = depth + 2)
    (result : Carrier) (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) (captured : result.1.2 = some details)
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode pending.1).1)
    (outcome : (Bool × (Front × Trace)) × Other)
    (completed : outcome ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1).2 reply)).run before))
    (accepted : outcome.1.1 = true)
    (published : ((owner, number), true) ∈ outcome.1.2.2.published) :
    phase (some details) ≠ .used := by
  intro used
  have erased : (result.1, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅) := by
    rw [← PqxdhLaterChallengeGeneratedContinuation.run_erase setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(result, after), supported, rfl⟩
  exact PqxdhLaterChallengeGeneratedCache.run_not_used setup env callbacks program adversary owner number bit attachedVerify primitives
    baseImpl kem ancestors disclosed depth position result.1 stored pending details after erased shape captured afterImpl before reply
    outcome completed accepted published ((phase_used details).mp used)

end Generated

end BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.phase_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.phase_used
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.before_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.before_record
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.inside_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.inside_record
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.generated_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.generated_builder
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.generated_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.generated_request
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.evaluated_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification.evaluated_not_used
