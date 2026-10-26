import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology

/-! The actual generated sampler supplies its original wrapper request chronology. Earlier start-cache erasure is kept separate from the reached source cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology
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
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "post" => PqxdhRecordConfidentialityChallenge.post adversary owner number bit
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- The concrete prepared packet retains its original prepared-input image and the reached request from that exact draw. The erased earlier cache is not reconstructed or assumed reachable. -/
theorem prepared_reaches (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (supported : ((Sum.inr (stored, Sum.inr pending), some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)).run cache)) :
    stored = PqxdhErasedParentSample.forgetStart
      (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit continuation), output) ∧
      PqxdhLaterChallengeSampleChronology.Reached env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number bit continuation pending details cache after := by
  simp only [PqxdhLaterChallengeSampler.prepared, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨result, current⟩, sampled, same⟩ := supported
  rcases result with decision | ⟨returned, captured⟩
  · cases same
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at same
    obtain ⟨⟨⟨storedEq, rfl⟩, rfl⟩, rfl⟩ := same
    exact ⟨storedEq, PqxdhLaterChallengeSampleChronology.run_reaches env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit continuation pending details cache after sampled⟩

/-- The original generated selection and original prepared start are retained beside the normalized packet. This predicate only describes an actual captured pending callback. -/
noncomputable def AfterReached (packet : Packet) (output : HmacBlock) (depth : Nat)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache) : Prop :=
  match packet.state with
  | .completed _ => False
  | .pending prefixOutput _ => ∃ start,
      input packet = Sum.inr start ∧
      stored = PqxdhErasedParentSample.forgetStart
        (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext
          (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit
            (adversary prefixOutput.context.selection.1)), output) ∧
      PqxdhLaterChallengeSampleChronology.Reached env0 callbacks baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext
        start output depth owner number bit (adversary prefixOutput.context.selection.1) pending details cache after

/-- A pending capture after the generated preparation has the request chronology of its literal selected continuation and original prepared start. -/
theorem after_reaches (packet : Packet) (output : HmacBlock) (depth : Nat)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (supported : ((Sum.inr (stored, Sum.inr pending), some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number bit
        attachedVerify primitives baseImpl kem ancestors disclosed packet output depth)).run cache)) :
    AfterReached setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      packet output depth stored pending details cache after := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode,
        map_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | pending prefixOutput ephemeral =>
      simp only [PqxdhLaterChallengeSampler.after] at supported
      split at supported
      · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
      · exact ⟨_, ‹_ = Sum.inr _›, prepared_reaches setup env callbacks owner number bit attachedVerify primitives baseImpl kem
          secretKey ciphertext _ output depth (adversary prefixOutput.context.selection.1) stored pending details cache after supported⟩

/-- The complete original sampler supplies the actual generated packet, preparation cache, and selected continuation for its pending capture. All later material draws preserve that reached cache. -/
theorem run_reaches (depth : Nat)
    (result : PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.2 = some details) :
    ∃ packet cache output,
      (packet, cache) ∈ support ((simulateQ hashImpl
        (PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem)).run ∅) ∧
      result.1.1 = (packet.secretKey, packet.ciphertext) ∧
      AfterReached setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
        packet output depth stored pending details cache after := by
  simp only [PqxdhLaterChallengeSampler.run, simulateQ_bind, StateT.run_bind,
    RawCtxSelectiveSharedRom.coins_complete, bind_map_left, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨packet, cache⟩, prepared, output, _, ⟨⟨localPacket, metadata⟩, current⟩, reached, parent, _, nonce, _, chain, _, same⟩ := supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  change metadata = some details at captured
  rw [shape, captured] at reached
  exact ⟨packet, cache, output, prepared, rfl, after_reaches setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    packet output depth stored pending details cache after reached⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.prepared_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.prepared_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.after_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.after_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.run_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology.run_reaches
