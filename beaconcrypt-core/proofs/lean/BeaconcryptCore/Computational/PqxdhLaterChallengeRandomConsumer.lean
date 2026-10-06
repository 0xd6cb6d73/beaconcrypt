-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBefore

/-! Execute the actual source-derived before callback with its literal private credentials and retained parent material, keeping all refusal and terminal monitor events. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer
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
local notation "Key" => PqxdhLaterChallengeRandomBefore.Key setup program (M := M) (P := P) (I := I) (K := K) (A := A) (X := X) (Response := Response) (KemSK := KemSK)

local notation "backend" => PqxdhLaterChallengeRandomBackend.handler (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
local notation "impl" => confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto

/-- Execute the literal before consumer from the complete component state reached by the actual forwarded prefix. Every complementary outcome contributes false without conditioning. -/
noncomputable def resume (qPost : Nat) (bit : Bool) (key : Key) : ProbComp Bool :=
  match key with
  | none => pure false
  | some (payload, state) => Prod.fst <$> (simulateQ impl
      (PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number
        attachedVerify primitives baseImpl kem qPost bit (some payload))).run state

/-- A reached random prefix imports its actual source chronology through the exact public dictionary projection and resumes from its entire reached component state. -/
theorem reached (depth qPost : Nat) (sourceBit : Bool)
    (result : Carrier × Option program.Selection) (after : RandomState)
    (supported : (result, after) ∈ support ((simulateQ backend
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number sourceBit
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run randomInitial)) :
    𝒟[resume setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost false
      (PqxdhLaterChallengeRandomBefore.beforeKey setup program (result, after))] {true} =
    𝒟[resume setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost true
      (PqxdhLaterChallengeRandomBefore.beforeKey setup program (result, after))] {true} := by
  have source := PqxdhLaterChallengeRandomProjection.supported
    (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto _ randomInitial after result supported
  have paired := PqxdhLaterChallengeBeforeConsumer.generated_random setup env callbacks program adversary owner number
    attachedVerify primitives baseImpl kem ancestors disclosed depth qPost sourceBit result
    (PqxdhLaterChallengeRandomProjection.cache after) source after
  rw [PqxdhLaterChallengeRandomBefore.retained]
  cases key : PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program
      (result, PqxdhLaterChallengeRandomProjection.cache after) with
  | none => rfl
  | some payload =>
    simpa only [key, resume, Option.map_some] using paired

/-- Complete generated prefix followed by the concrete monitored before consumer from its actual reached state. The two parameters expose the adjacent prefix and continuation changes. -/
noncomputable def run (depth qPost : Nat) (prefixBit continuationBit : Bool) : ProbComp Bool :=
  (simulateQ backend (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
    attachedVerify primitives baseImpl kem ancestors disclosed depth)).run randomInitial >>= fun result =>
    resume setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost continuationBit
      (PqxdhLaterChallengeRandomBefore.beforeKey setup program result)

/-- Keep the actual complete generated prefix distribution fixed and change the concrete monitored continuation, using source chronology for every reached result. -/
theorem same_prefix (depth qPost : Nat) (sourceBit : Bool) :
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost sourceBit false] {true} =
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost sourceBit true] {true} := by
  simp only [run, evalDist_apply_singleton, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro result
  by_cases actual : result ∈ support ((simulateQ backend
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number sourceBit
        attachedVerify primitives baseImpl kem ancestors disclosed depth)).run randomInitial)
  · have equal := reached setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      ancestors disclosed depth qPost sourceBit result.1 result.2 actual
    simp only [evalDist_apply_singleton] at equal
    rw [equal]
  · have zero := probOutput_eq_zero_of_not_mem_support actual
    rw [zero, zero_mul, zero_mul]

/-- For any fixed continuation world, the complete before observation, including the full reached component state, gives the same actual resumed distribution in either generated prefix world. -/
theorem same_continuation (depth qPost : Nat) (first second bit : Bool) :
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost first bit] =
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost second bit] := by
  apply evalDist_eq_of_evalSPMF_eq
  apply evalSPMF_eq_of_relTriple_eqRel
  have paired := relTriple_bind (PqxdhLaterChallengeRandomBefore.carried setup env callbacks program
    adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth first second randomInitial)
    (fun left right same => by
      cases same
      exact relTriple_refl (resume setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit left))
  simpa only [bind_map_left, run] using paired

/-- The actual forwarded random prefix and concrete monitored before continuation have equal success probability in both challenge worlds, retaining all histories and complementary/refusal mass. -/
theorem random (depth qPost : Nat) :
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost false false] {true} =
    𝒟[run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost true true] {true} := by
  exact (same_prefix setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    depth qPost false).trans (congrArg (fun measure => measure {true})
      (same_continuation setup env callbacks program adversary owner number
        attachedVerify primitives baseImpl kem ancestors disclosed depth qPost false true true))

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.reached

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.same_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.same_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.same_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.same_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer.random
