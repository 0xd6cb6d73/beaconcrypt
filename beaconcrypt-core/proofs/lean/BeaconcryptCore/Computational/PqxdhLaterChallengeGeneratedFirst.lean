import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleFirst

/-! The actual generated inside cut stops before its first KDF query and carries the same complete native state reached by the original prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFirst
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
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
    (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- The same evaluated inside packet retains its complete native state as the end of the actual source prefix, together with the literal pre-request frontend, history, request and parent address. -/
theorem source_start (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.1.2 = some details)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside) :
    ∃ selection, result.2 = some selection ∧ ∃ start secret challenge output cache,
      PqxdhLaterChallengeSampleFirst.First env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number bit (adversary selection) pending details cache after := by
  obtain ⟨selection, selected, start, secret, challenge, output, cache, reached⟩ :=
    PqxdhLaterChallengeCarriedChronology.carried_reaches setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth result stored pending details after supported shape captured
  exact ⟨selection, selected, start, secret, challenge, output, cache,
    PqxdhLaterChallengeSampleFirst.reached_first env0 callbacks baseImpl kem attachedVerify primitives secret challenge start output
      depth owner number bit (adversary selection) pending details cache after reached
      classified⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFirst

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFirst.source_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFirst.source_start
