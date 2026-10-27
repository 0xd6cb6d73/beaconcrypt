import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleMonitor

/-! The actual generated pending packet supplies its complete native source prefix with an unchanged private challenge monitor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedPrefix
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

/-- Outside the used phase, the same evaluated generated packet supplies an actual marker-preserving native prefix ending at its captured request. The recorded selection, Builder execution, callback-local scan and cache stay fixed; the source view is universally quantified. -/
theorem prefix_unmarked (depth : Nat)
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
    (notUsed : PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .used) :
    ∃ selection, result.2 = some selection ∧ ∃ start secret challenge output cache,
      PqxdhLaterChallengeSampleMonitor.Marked env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number bit (adversary selection) pending details cache after := by
  obtain ⟨selection, selected, start, secret, challenge, output, cache, reached⟩ :=
    PqxdhLaterChallengeCarriedChronology.carried_reaches setup env callbacks program adversary owner number bit attachedVerify
      primitives baseImpl kem ancestors disclosed depth result stored pending details after supported shape captured
  exact ⟨selection, selected, start, secret, challenge, output, cache,
    PqxdhLaterChallengeSampleMonitor.reached_marked env0 callbacks baseImpl kem attachedVerify primitives secret challenge start output
      depth owner number bit (adversary selection) pending details cache after reached
      (PqxdhLaterChallengeSampleMonitor.phase_unused details notUsed)⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedPrefix.prefix_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedPrefix.prefix_unmarked
