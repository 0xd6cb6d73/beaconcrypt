-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderConsumer
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded

/-! Recover the actual source-selected outside continuation of every generated initial Builder cut. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource
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

/-- Restoring the literal carried outside wrapper after callback normalization returns the complete original Builder descriptor, including its frontend, publication trace and origin. -/
theorem whole_original (bit : Bool) (selection : program.Selection)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (saved : PqxdhInitialBuilderContext.Builder (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))
    (same : context.original = .inr saved)
    (outside : saved.outside = fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit
      (adversary selection reply) PqxdhRecordConfidentialityChallenge.initial) :
    whole setup program adversary owner number bit selection { saved with outside := pure } context.trace context.origin = context := by
  calc
    _ = PqxdhLaterChallengeCapture.append saved.outside (PqxdhLaterChallengeSavedMonitor.builderOnly saved context.trace context.origin) := by
      simp only [whole, PqxdhLaterChallengeCapture.append, PqxdhLaterChallengeSavedMonitor.builderOnly, pure_bind, outside]
    _ = context := PqxdhLaterChallengeSavedMonitor.builder_append context saved same

/-- An actual generated initial-Builder cut supplies the original selection and literal outside continuation used by the executable consumer. This is a support consequence, not a conditional distribution or probability assertion. -/
theorem generated_whole (bit : Bool) (depth : Nat) (result : Carrier × Option program.Selection)
    (stored : Input × HmacBlock) (pending : Pending)
    (supported : result ∈ support (PqxdhLaterChallengeGeneratedContinuation.run
      setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (initialCut : result.1.2 = none) :
    ∃ selection saved, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection ∧
      pending.1.original = .inr saved ∧
      whole setup program adversary owner number bit selection { saved with outside := pure }
        pending.1.trace pending.1.origin = pending.1 := by
  obtain ⟨selection, selected, post, continued⟩ := PqxdhLaterChallengeGeneratedContinuation.run_capture
    setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth result stored pending supported shape
  simp only [PqxdhLaterChallengeBuilderContinuation.Continuation, initialCut] at continued
  rcases continued with ⟨saved, same, outside⟩
  exact ⟨selection, saved, selected, post, same, whole_original setup program adversary owner number bit selection pending.1 saved same outside⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource.whole_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource.whole_original

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource.generated_whole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderSource.generated_whole
