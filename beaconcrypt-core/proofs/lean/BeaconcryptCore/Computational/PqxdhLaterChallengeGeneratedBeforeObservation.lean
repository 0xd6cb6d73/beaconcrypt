import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling
import BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore

/-! Exact observation of the actual generated before-admission callback, complete private source context, material and ROM state, with all complementary mass retained. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation
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

/-- Omit only the bit-specific stored outside wrapper from this observation. Every other source input field remains literal; the complete coupled programs still retain their original wrappers. -/
noncomputable def inputKey (start : Input) : Input := {start with post := fun _ => pure false}

/-- The actual before callback retains its entire private packet, source input apart from its explicit world wrapper, native state, correlated material, selected continuation and reached ROM cache. Every other outcome is one unconditioned None. -/
noncomputable def beforeKey (result : (Carrier × Option program.Selection) × CtxRO.QueryCache) :=
  match result with
  | ((((credentials, (((Sum.inr (stored, Sum.inr pending), parent), target), nonce, next)), some details), selection), cache) =>
      if PqxdhLaterChallengeSavedClassification.phase (some details) = PqxdhLaterChallengeSavedClassification.Phase.before then
        some (credentials, inputKey setup stored.1, stored.2, details, PqxdhNativeSharedPrefix.attach pending.2 cache,
          parent, target, nonce, next, selection)
      else none
  | _ => none

/-- A collector outcome outside the before observation contributes exactly to the complete carrier's complementary outcome, regardless of its real cached/common decision or source context. -/
theorem encoded_none (packet : Packet) (start : Input) (output : HmacBlock) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (result : (Bool ⊕ (Pending × Option CaptureDetails)) × CtxRO.QueryCache)
    (key : PqxdhLaterChallengeCollectorBefore.beforeKey result = none) :
    beforeKey setup program (PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeGeneratedCoupling.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output bit continuation result)) = none := by
  rcases result with ⟨decision | ⟨pending, details⟩, cache⟩
  · rfl
  · cases details with
    | none => rfl
    | some details =>
      simp only [PqxdhLaterChallengeCollectorBefore.beforeKey, PqxdhLaterChallengeCollectorCoupling.pendingView,
        Option.bind_some, PqxdhLaterChallengePrefixMass.beforeKey] at key
      simp only [beforeKey, PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected,
        PqxdhLaterChallengeGeneratedSamplerCoupling.finish, PqxdhLaterChallengeGeneratedCoupling.encodePrepared]
      split at key
      · cases key
      · exact ite_eq_right ‹_›

/-- The same actual before callback and complete native state yield identical carrier observations in both worlds, retaining the same stored source context, correlated material and actual parent address. -/
theorem encoded_pending (packet : Packet) (start : Input) (output : HmacBlock) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (details : CaptureDetails) (state : PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache) :
    beforeKey setup program (PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeGeneratedCoupling.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output first continuation
        (PqxdhLaterChallengeCollectorBefore.pending owner number first details state))) =
    beforeKey setup program (PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeGeneratedCoupling.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output second continuation
        (PqxdhLaterChallengeCollectorBefore.pending owner number second details state))) := by
  simp only [beforeKey, PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected,
    PqxdhLaterChallengeGeneratedSamplerCoupling.finish, PqxdhLaterChallengeGeneratedCoupling.encodePrepared,
    PqxdhLaterChallengeCollectorBefore.pending, PqxdhLaterChallengeScanCoupling.tagged]
  simp only [PqxdhLaterSharedMessagePrefix.address, PqxdhErasedParentSample.address,
    PqxdhSharedParentInput.restore, PqxdhSharedParentCollect.restore,
    PqxdhLaterChallengeSavedMonitor.append_address]
  rfl

/-- The complete collector relation preserves this whole before-carrier observation, including its literal source input and selected callback; all complementary mass maps to None on both sides. -/
theorem encoded_related (packet : Packet) (start : Input) (output : HmacBlock) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (left right : (Bool ⊕ (Pending × Option CaptureDetails)) × CtxRO.QueryCache)
    (related : PqxdhLaterChallengeCollectorCoupling.Related owner number first second continuation left right) :
    beforeKey setup program (PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeGeneratedCoupling.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output first continuation left)) =
    beforeKey setup program (PqxdhLaterChallengeGeneratedSamplerCoupling.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeGeneratedCoupling.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output second continuation right)) := by
  have sameKey := PqxdhLaterChallengeCollectorBefore.related_key owner number first second continuation left right related
  cases key : PqxdhLaterChallengeCollectorBefore.beforeKey left with
  | none =>
    have rightKey := sameKey.symm.trans key
    rw [encoded_none setup env callbacks program owner number attachedVerify primitives baseImpl kem packet start output first continuation parent nonce next left key,
      encoded_none setup env callbacks program owner number attachedVerify primitives baseImpl kem packet start output second continuation parent nonce next right rightKey]
  | some observed =>
    rcases observed with ⟨details, state⟩
    obtain ⟨rfl, rfl⟩ := PqxdhLaterChallengeCollectorBefore.matched owner number first second continuation left right related details state key
    exact encoded_pending setup env callbacks program owner number attachedVerify primitives baseImpl kem packet start output first second continuation parent nonce next details state

/-- The full actual generated-carrier relation implies equality of its complete before observation, including all private source context/material and the complementary None outcome. -/
theorem related_key (first second : Bool)
    (left right : (Carrier × Option program.Selection) × CtxRO.QueryCache)
    (related : PqxdhLaterChallengeGeneratedSamplerCoupling.CarriedRelated setup env callbacks program adversary owner number
      attachedVerify primitives baseImpl kem ancestors disclosed first second left right) :
    beforeKey setup program left = beforeKey setup program right := by
  rcases related with ⟨beforeLeft, beforeRight, output, parent, nonce, next, leftAfter, rightAfter, packets, collected, rfl, rfl⟩
  rcases collected with ⟨leftDecision, rightDecision, _, _, rfl, rfl⟩ |
      ⟨prefixOutput, ephemeral, start, rfl, _, _, prepared⟩
  · rfl
  · rcases prepared with ⟨leftResult, rightResult, rfl, rfl, collector⟩
    exact encoded_related setup env callbacks program owner number attachedVerify primitives baseImpl kem
      beforeLeft.1 start output first second (adversary prefixOutput.context.selection.1) parent nonce next leftResult rightResult collector

/-- The entire unconditioned before-observation distribution of the actual source sampler has a diagonal coupling, including its full complementary mass. -/
theorem carried (depth : Nat) (first second : Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      (beforeKey setup program <$> (simulateQ hashImpl (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      (beforeKey setup program <$> (simulateQ hashImpl (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      Eq := by
  apply relTriple_map
  exact relTriple_post_mono
    (PqxdhLaterChallengeGeneratedSamplerCoupling.carried setup env callbacks program adversary owner number
      attachedVerify primitives baseImpl kem ancestors disclosed depth first second cache)
    (related_key setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second)

/-- Type of the retained before observation: the same full source and private state, with only the explicit world wrapper omitted. -/
abbrev Key := Option ((KemSK × MlKem768Ciphertext) × Input × HmacBlock × CaptureDetails ×
  PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache × Entry × RootOutput × NonceOutput × RootOutput × Option program.Selection)

/-- Any Boolean decision on the complete before observation has exactly the same measured distribution in both actual source worlds, including every complementary outcome. No success conditioning is used. -/
theorem observed (depth : Nat) (first second : Bool) (cache : CtxRO.QueryCache)
    (observe : Key setup program (X := X) (Response := Response) (KemSK := KemSK) → Bool) :
    𝒟[(observe ∘ beforeKey setup program) <$> (simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number first
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache] =
    𝒟[(observe ∘ beforeKey setup program) <$> (simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number second
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache] := by
  exact evalDist_eq_of_evalSPMF_eq _ _ (evalSPMF_map_eq_of_relTriple (relTriple_post_mono
    (PqxdhLaterChallengeGeneratedSamplerCoupling.carried setup env callbacks program adversary owner number
      attachedVerify primitives baseImpl kem ancestors disclosed depth first second cache)
    (fun left right related => congrArg observe
      (related_key setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second left right related))))

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_none

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.encoded_related

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.related_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.related_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.carried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.carried

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation.observed
