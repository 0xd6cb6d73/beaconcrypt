-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy

/-! Remove the semantic resource guard from the actual before-source reduction using the source-derived proof certificate. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded
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

/-- A proof allowance for the exact generated before observation; complementary outcomes require no callback certificate. -/
noncomputable def KeyFits (qPost : Nat) (key : Key) : Prop :=
  match key with
  | none => True
  | some (_, _, _, details, _, _, _, _, _, _) => PqxdhLaterChallengeBeforeConsumer.Fits setup owner number qPost details

/-- The actual source-carrier certificate supplies the complete before-client allowance without inspecting or testing a semantic predicate at runtime. -/
theorem key_fits (q : Nat) (result : Carrier × Option program.Selection) (cache : CtxRO.QueryCache)
    (valid : PqxdhLaterChallengeSamplerFits.PacketFits setup owner number q (result.1.1.2.1.1.1, result.1.2)) :
    KeyFits setup program owner number (1 + q)
      (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, cache)) := by
  rcases result with ⟨⟨⟨credentials, ⟨⟨⟨packet, parent⟩, target⟩, nonce, next⟩⟩, captured⟩, selection⟩
  rcases packet with decision | ⟨stored, decision | pending⟩
  · trivial
  · trivial
  · cases captured with
    | none => trivial
    | some details =>
      simp only [PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey]
      split
      · exact valid
      · trivial

/-- Execute the same complete saved callback using a supplied proof; only the original decidable byte-address exclusion remains as a branch. -/
noncomputable def client (qPost : Nat) (bit : Bool) (key : Key) (valid : KeyFits setup program owner number qPost key) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := by
  classical
  exact match key, valid with
  | none, _ => pure false
  | some (credentials, start, output, details, native, parent, target, nonce, next, _), fits =>
    if RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address details.callback.original then
      PqxdhLaterChallengeBeforeConsumer.decision setup <$> PqxdhLaterChallengeSavedMonitor.resume
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem credentials.1 credentials.2)
        (initialLocal (A := A) (N := BareState 1) (env0).source start.selectedMessage zeroRoot (PqxdhInitialSampledParent.response (start, output)))
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem credentials.1 credentials.2))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
        (view (productionStream env.source.crypto) (PqxdhLaterChallengeCollectorCoupling.detach native).1.store.1)
        target nonce next env.senderId env.route env.decode (PqxdhInitialSampledParent.marker env.source (start, output))
        ⟨0, Nat.zero_lt_succ _⟩ owner number bit details parent.material qPost (PqxdhLaterChallengeBeforeConsumer.callback_fits setup owner number qPost details fits)
        (PqxdhLaterChallengeCollectorCoupling.detach native).1 none
    else pure false

/-- The source-certified executable continuation is literally the prior guarded client. The derived proof removes the resource branch without deleting any oracle call or refusal path. -/
theorem client_eq (qPost : Nat) (bit : Bool) (key : Key) (valid : KeyFits setup program owner number qPost key) :
    client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key valid =
    PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit key := by
  cases key with
  | none => rfl
  | some payload =>
    rcases payload with ⟨credentials, start, output, details, native, parent, target, nonce, next, selection⟩
    simp only [KeyFits] at valid
    simp only [client, PqxdhLaterChallengeBeforeConsumer.client, dite_eq_left valid]

/-- A single reduction executes the full original generated prelude and proof-certified saved client. Proof attachment adds no observable operation or test. -/
noncomputable def compiled (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let result ← simulateQ RawCtxSourceSharedRom.forward
    (PqxdhLaterChallengeGeneratedFits.certified setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded)
  client setup env callbacks program owner number attachedVerify primitives baseImpl kem
    (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget) continuationBit
    (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result.1, ∅))
    (key_fits setup program owner number _ result.1 ∅ result.2)

/-- The entire guard-free source reduction equals the complete prior two-bit program, not just a selected callback or evaluated marginal. Every prelude and continuation query remains present. -/
theorem compiled_eq (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool) :
    compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit =
    PqxdhLaterChallengeRandomCompiled.client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      ancestors disclosed depth (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget) prefixBit continuationBit := by
  have erased := congrArg (simulateQ RawCtxSourceSharedRom.forward)
    (PqxdhLaterChallengeGeneratedFits.certified_erase setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded)
  rw [simulateQ_map] at erased
  unfold compiled PqxdhLaterChallengeRandomCompiled.client
  simp only [client_eq]
  rw [← erased, bind_map_left]

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.key_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.key_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.client_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.client_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.compiled_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded.compiled_eq
