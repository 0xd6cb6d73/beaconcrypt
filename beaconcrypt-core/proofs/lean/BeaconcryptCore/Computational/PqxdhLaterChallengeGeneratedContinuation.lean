import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache
import BeaconcryptCore.Computational.PqxdhLaterChallengePreparedContinuation

/-! Retain the actual generated continuation beside the existing callback carrier, including initial Builder captures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation
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
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
    (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- The source-generated selection is retained as private compiler metadata. It supplies no separate identity, KEM or service-secret field; the original selection and any equal-byte correlations are retained. -/
abbrev Carrier := PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × Option program.Selection

/-- Carry the selection directly from the actual generated preparation. Every original branch, source callback and material draw still executes in its original order. -/
noncomputable def run (depth : Nat) : OracleComp HashSpec (Carrier setup program (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)) := do
  let packet ← PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
  let output ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  let localPacket ← PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem
    ancestors disclosed packet output depth
  let parent ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ FullOutput)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  let selection := match packet.state with
    | .completed _ => none
    | .pending before _ => some before.context.selection.1
  pure ((((packet.secretKey, packet.ciphertext),
    (((localPacket.1, fromOutput (PqxdhLaterSharedMessagePrefix.address setup localPacket.1) parent), nextChain parent), nonce, chain)), localPacket.2), selection)

/-- Erasing only the carried selection restores the complete original sampler syntax, rather than only its marginal distribution. -/
theorem run_erase (depth : Nat) :
    Prod.fst <$> run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth =
      PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth := by
  simp only [run, PqxdhLaterChallengeSampler.run, map_bind, map_pure]

/-- Carrying the original selection changes no all-reply budget, including weighted source costs. -/
theorem run_budget {Budget : Type} (depth : Nat) (budget : Budget)
    (allowed : HashSpec.Domain → Budget → Prop) (cost : HashSpec.Domain → Budget → Budget) :
    (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBound budget allowed cost ↔
    (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBound budget allowed cost := by
  rw [← run_erase setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth,
    isQueryBound_map_iff]

/-- Complete evaluation followed by any original state-dependent continuation is unchanged. The sampler's full final backend is passed onward in both programs. -/
theorem continued {State Result : Type} (depth : Nat)
    (impl : QueryImpl HashSpec (StateT State ProbComp)) (before : State)
    (continuation : PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) → State → ProbComp Result) :
    (do let result ← (simulateQ impl
          (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run before
        continuation result.1.1 result.2) =
    (do let result ← (simulateQ impl
          (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run before
        continuation result.1 result.2) := by
  rw [← run_erase setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]

/-- The normalized stored start retains the literal wrapper continuation passed to this prepared source call, including captures in the initial Builder. -/
theorem prepared_continuation (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : (Sum.inr (stored, Sum.inr pending), details) ∈ support
      (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)) :
    stored.1.post = fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (continuation reply)
      PqxdhRecordConfidentialityChallenge.initial := by
  simp only [PqxdhLaterChallengeSampler.prepared, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, _, same⟩ := supported
  rcases value with decision | ⟨returned, captured⟩
  all_goals simp only [Prod.mk.injEq, Sum.inr.injEq, reduceCtorEq, and_false, false_and] at same
  rw [same.1.1]
  rfl

/-- Every generated pending descriptor has the original source selection carried alongside it, and that exact selection supplies its stored Builder continuation. This includes a capture with no wrapper request. -/
theorem run_selection (depth : Nat)
    (result : Carrier setup program (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (supported : result ∈ support
      (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection := by
  simp only [run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, ⟨localPacket, details⟩, sampled, parent, _, nonce, _, chain, _, rfl⟩ := supported
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  rw [shape] at sampled
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode,
        map_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at sampled
  | pending prefixOutput ephemeral =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input,
        PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode] at sampled
      refine ⟨prefixOutput.context.selection.1, rfl, ?_⟩
      exact prepared_continuation setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secretKey ciphertext _ output depth (adversary prefixOutput.context.selection.1) stored pending details sampled

/-- The same carried selection identifies the original stored continuation after complete actual interpreter execution, with no caller-supplied selection or source-start premise. -/
theorem evaluated_selection {State : Type} (depth : Nat)
    (impl : QueryImpl HashSpec (StateT State ProbComp)) (before after : State)
    (result : Carrier setup program (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (supported : (result, after) ∈ support ((simulateQ impl
      (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run before))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection := by
  apply run_selection setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    depth result stored pending ?_ shape
  apply support_simulateQ_run'_subset impl _ before
  rw [StateT.run'_eq, support_map]
  exact ⟨(result, after), supported, rfl⟩

/-- For absent request metadata the descriptor's Builder outside continuation is the literal wrapper of `continuation`; later captures satisfy only the exact, continuation-independent `Joined` composition of their original callback and request continuation. -/
theorem prepared_capture (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : (Sum.inr (stored, Sum.inr pending), details) ∈ support
      (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)) :
    PqxdhLaterChallengeBuilderContinuation.Continuation owner number bit continuation (pending.1, details) := by
  simp only [PqxdhLaterChallengeSampler.prepared, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, reached, same⟩ := supported
  rcases value with decision | ⟨returned, captured⟩
  · simp only [Prod.mk.injEq, Sum.inr.injEq, reduceCtorEq, and_false, false_and] at same
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at same
    obtain ⟨⟨_, rfl⟩, rfl⟩ := same
    exact PqxdhLaterChallengePreparedContinuation.run_continuation _ callbacks baseImpl kem attachedVerify primitives
      secret challenge start output depth owner number bit continuation _ _ reached

/-- One carried source selection supplies the stored Post and, when `result.1.2 = none`, the descriptor's literal Builder outside wrapper for `adversary selection`. When `result.1.2 = some details`, `Continuation owner number bit (adversary selection) (pending.1, result.1.2)` ignores its adversary argument and is only the selection-independent `Joined` composition of the actual `details.callback` and `details.request.next`, which is not related to `adversary selection` by this theorem; see `GeneratedChronology.run_reaches`. No selection or function is chosen existentially from the descriptor. -/
theorem run_capture (depth : Nat)
    (result : Carrier setup program (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (supported : result ∈ support
      (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection ∧
      PqxdhLaterChallengeBuilderContinuation.Continuation owner number bit (adversary selection) (pending.1, result.1.2) := by
  simp only [run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, ⟨localPacket, details⟩, sampled, parent, _, nonce, _, chain, _, rfl⟩ := supported
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  rw [shape] at sampled
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode,
        map_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at sampled
  | pending prefixOutput ephemeral =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input,
        PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode] at sampled
      exact ⟨prefixOutput.context.selection.1, rfl,
        prepared_continuation setup env callbacks owner number bit attachedVerify primitives baseImpl kem
          secretKey ciphertext _ output depth (adversary prefixOutput.context.selection.1) stored pending details sampled,
        prepared_capture setup env callbacks owner number bit attachedVerify primitives baseImpl kem
          secretKey ciphertext _ output depth (adversary prefixOutput.context.selection.1) stored pending details sampled⟩

/-- After complete actual interpreter execution, the same carried selection still supplies the stored Post and, when `result.1.2 = none`, the literal Builder outside wrapper. When `result.1.2 = some details`, the descriptor satisfies the selection-independent `Joined` composition of `details.callback` and `details.request.next`, which is not related to `adversary selection` by this theorem; see `GeneratedChronology.run_reaches`. Only support is projected; no probability or budget is transferred. -/
theorem evaluated_capture {State : Type} (depth : Nat)
    (impl : QueryImpl HashSpec (StateT State ProbComp)) (before after : State)
    (result : Carrier setup program (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (supported : (result, after) ∈ support ((simulateQ impl
      (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run before))
    (shape : result.1.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending)) :
    ∃ selection, result.2 = some selection ∧
      stored.1.post = PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection ∧
      PqxdhLaterChallengeBuilderContinuation.Continuation owner number bit (adversary selection) (pending.1, result.1.2) := by
  apply run_capture setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    depth result stored pending ?_ shape
  apply support_simulateQ_run'_subset impl _ before
  rw [StateT.run'_eq, support_map]
  exact ⟨(result, after), supported, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.continued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.continued
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.prepared_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.prepared_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_selection
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.evaluated_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.evaluated_selection
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.prepared_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.prepared_capture
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.run_capture
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.evaluated_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedContinuation.evaluated_capture
