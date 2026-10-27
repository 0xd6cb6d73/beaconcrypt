import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology
import BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedInput

/-! The complete generated sampler retains the earlier challenge input at its literal saved callback, using the original unnormalized source start. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput
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

/-- The actual generated selection, original prepared start and chronological challenge input before the saved callback. -/
noncomputable def AfterInput (packet : Packet) (output : HmacBlock) (depth : Nat)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache : CtxRO.QueryCache) : Prop :=
  match packet.state with
  | .completed _ => False
  | .pending prefixOutput _ => ∃ start,
      input packet = Sum.inr start ∧
      stored = PqxdhErasedParentSample.forgetStart
        (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext
          (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit
            (adversary prefixOutput.context.selection.1)), output) ∧
      PqxdhLaterChallengeCapturedInput.BeforeInput env0 callbacks baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext
        start output depth owner number bit (adversary prefixOutput.context.selection.1) pending details cache

/-- The actual generated source prefix supplies its earlier challenge input without reconstructing the normalized start. -/
theorem after_input (packet : Packet) (output : HmacBlock) (depth : Nat)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (reached : PqxdhLaterChallengeGeneratedChronology.AfterReached setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed packet output depth stored pending details cache after)
    (target : PqxdhRecordConfidentialityChallenge.Target number details.request.before) :
    AfterInput setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      packet output depth stored pending details cache := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision => exact False.elim reached
  | pending prefixOutput ephemeral =>
      obtain ⟨start, shaped, storedEq, actual⟩ := reached
      exact ⟨start, shaped, storedEq,
        PqxdhLaterChallengeCapturedInput.reached_input env0 callbacks baseImpl kem attachedVerify primitives secretKey ciphertext
          start output depth owner number bit (adversary prefixOutput.context.selection.1) pending details cache after actual target⟩

/-- The whole actual generated sampler supplies the earlier input and its original source witness, with the same packet, selected continuation and saved cache. -/
theorem run_input (depth : Nat)
    (result : PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (result, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : result.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : result.2 = some details)
    (target : PqxdhRecordConfidentialityChallenge.Target number details.request.before) :
    ∃ packet cache output,
      (packet, cache) ∈ support ((simulateQ hashImpl
        (PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem)).run ∅) ∧
      result.1.1 = (packet.secretKey, packet.ciphertext) ∧
      AfterInput setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
        packet output depth stored pending details cache := by
  obtain ⟨packet, cache, output, prepared, same, reached⟩ :=
    PqxdhLaterChallengeGeneratedChronology.run_reaches setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth result stored pending details after supported shape captured
  exact ⟨packet, cache, output, prepared, same,
    after_input setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      packet output depth stored pending details cache after reached target⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput.after_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput.after_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput.run_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInput.run_input
