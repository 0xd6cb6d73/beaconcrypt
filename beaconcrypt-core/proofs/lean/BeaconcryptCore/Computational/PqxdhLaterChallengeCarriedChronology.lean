import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology

/-! The actual generated sampler carries the same selection used by the historical wrapper chronology. This transports complete evaluated support, not marginal distributions or probabilities. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology
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

/-- The evaluated generated pending packet and its recorded callback arise from the original adversary selected by that same packet. The exact historical cache, callback, pending descriptor and final cache are retained. -/
theorem carried_reaches (depth : Nat)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : PqxdhLaterChallengeGeneratedChronology.Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit attachedVerify primitives
        baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.1.2 = some details) :
    ∃ selection, result.2 = some selection ∧ ∃ start secret challenge output cache,
      PqxdhLaterChallengeSampleChronology.Reached env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number bit (adversary selection) pending details cache after := by
  simp only [PqxdhLaterChallengeGeneratedContinuation.run, simulateQ_bind, StateT.run_bind,
    RawCtxSelectiveSharedRom.coins_complete, bind_map_left, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨packet, cache⟩, prepared, output, _, ⟨⟨localPacket, metadata⟩, current⟩, reached, parent, _, nonce, _, chain, _, same⟩ :=
    supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  change metadata = some details at captured
  rw [shape, captured] at reached
  have chronology := PqxdhLaterChallengeGeneratedChronology.after_reaches setup env callbacks program adversary owner number bit
    attachedVerify primitives baseImpl kem ancestors disclosed packet output depth stored pending details cache after reached
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision => exact chronology.elim
  | pending prefixOutput ephemeral =>
      obtain ⟨start, _, _, witness⟩ := chronology
      exact ⟨prefixOutput.context.selection.1, rfl, start, secretKey, ciphertext, output, cache, witness⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology.carried_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCarriedChronology.carried_reaches
