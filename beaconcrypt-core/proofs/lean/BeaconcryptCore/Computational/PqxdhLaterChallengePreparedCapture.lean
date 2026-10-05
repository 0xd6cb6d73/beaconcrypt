import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture
import BeaconcryptCore.Computational.PqxdhPreparedSharedParent
import BeaconcryptCore.Computational.PqxdhSharedParentCollect
import BeaconcryptCore.Computational.PqxdhErasedParentSample

/-! The concrete prepared-source sampler retains actual wrapper captures while running the original shared callback compiler and complete cached/common continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => PqxdhPreparedSharedPrefix.environment original callbacks
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "pre" => PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "application" => PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "selector" => PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge)
local notation "aux" => PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks

open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture

/-- Set only the literal challenge wrapper continuation at the source input boundary. The enclosing generated source supplies this same function. -/
noncomputable def withPost (start : Input) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) : Input :=
  { start with post := fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial }

/-- Run the existing shared-ROM predecessor scanner with the actual generated wrapper metadata, without installing or replacing the reached shared cache. -/
noncomputable def capturedPrefix (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :=
  let execution := PqxdhInitialSourceExperiment.execution (RawCtxSelectedInitialConstructor.response64 output)
    start.index start.metadata { start.ready with root := zeroRoot }
    (withPost (setup := setup) start owner number bit adversary).post start.before
  sharedCarried (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) execution.origin
    (env).senderId (env).route (env).decode execution.index execution.before execution.trace
    (env).source (env).recordWriter (depth + 1) pre application
    (initialLocal (env).source start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)) selector aux
    execution.initial execution.metadata execution.ready owner number bit adversary depth
    (PqxdhPreparedSharedPrefix.state original start output)

/-- The concrete shared predecessor sampler erases to the complete original prepared source before interpretation, retaining all source callbacks and private fields. -/
theorem prefix_erase (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    cutMap Prod.fst <$> capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary =
      PqxdhPreparedSharedPrefix.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        (withPost (setup := setup) start owner number bit adversary) output depth := by
  simp only [capturedPrefix, shared_erase]
  rfl

abbrev CapturedCut := RawCtxForwardScan.Cut
  (PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K)
    Bool Bool S (B + 1) × Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
  (PqxdhInitialNativeCarried.Final M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
  (Local A (BareState 1) RootOracle.QueryCache)

/-- A completed cut has no pending request. An actual pending cut retains the request emitted by its original callback constructor. -/
def requestAt (cut : CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)) :
    Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)) :=
  match cut with
  | .complete _ _ => none
  | .pending context _ => context.2

private def attachRequest {Pending : Type}
    (request : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))) : Bool ⊕ Pending → Bool ⊕ (Pending × Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
  | .inl decision => .inl decision
  | .inr pending => .inr (pending, request)

private theorem attach_erase {Pending : Type}
    (request : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1))) (input : Bool ⊕ Pending) :
    Sum.map id Prod.fst (attachRequest request input) = input := by
  cases input <;> rfl

/-- Execute the original collector first. Complete/cached decisions are kept verbatim, and only its actual pending result receives the existing generated capture. -/
noncomputable def collect (start : Input) (output : HmacBlock) (depth : Nat)
    (cut : CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)) :=
  attachRequest (requestAt cut) <$>
    PqxdhPreparedSharedParent.collect original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth (cutMap Prod.fst cut)

/-- Removing only the request capture restores the literal original completed/cached/missing collector, with no branch or callback change. -/
theorem collect_erase (start : Input) (output : HmacBlock) (depth : Nat)
    (cut : CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)) :
    Sum.map id Prod.fst <$> collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut =
      PqxdhPreparedSharedParent.collect original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth (cutMap Prod.fst cut) := by
  simp only [collect, Functor.map_map, attach_erase]
  exact congrFun Functor.map_id _

/-- The complete prepared sampler carries the actual cut metadata while using the unchanged prefix and full cached/common collector. -/
noncomputable def run (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) := do
  let cut ← capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary
  collect original callbacks baseImpl kem attachedVerify primitives secret challenge
    (withPost (setup := setup) start owner number bit adversary) output depth cut

/-- Metadata erasure is a complete oracle-program equality for the actual prepared sampler, including completed and cached decisions before a pending descriptor is returned. -/
theorem run_erase (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    Sum.map id Prod.fst <$> run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary =
      PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        (withPost (setup := setup) start owner number bit adversary) output depth := by
  simp only [run, map_bind, collect_erase]
  rw [← bind_map_left, prefix_erase]
  rfl

/-- Evaluating the complete captured sampler restores the literal audited source sampleOne distribution and its actual reached shared cache. -/
theorem run_source (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    (fun result => PqxdhSharedParentCollect.restore (Sum.map id Prod.fst result.1) result.2) <$>
      (simulateQ hashImpl (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run start.shared.2 =
      PqxdhErasedParentSample.sampleOne (env).source (env).recordWriter (env).senderId (env).route (env).decode depth
        (PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge
          (withPost (setup := setup) start owner number bit adversary), output) := by
  have actual := PqxdhPreparedSharedParent.source original callbacks baseImpl kem attachedVerify primitives secret challenge
    (withPost (setup := setup) start owner number bit adversary) output depth
  rw [← run_erase] at actual
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, withPost] using actual

/-- Complete query budgets are unchanged by carrying the generated captures; cached continuations and every source uniform/hash request remain billed. -/
theorem run_budget {Budget : Type} (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (budget : Budget) (canQuery : HashSpec.Domain → Budget → Prop) (cost : HashSpec.Domain → Budget → Budget) :
    (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary).IsQueryBound budget canQuery cost ↔
      (PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        (withPost (setup := setup) start owner number bit adversary) output depth).IsQueryBound budget canQuery cost := by
  rw [← run_erase, isQueryBound_map_iff]

/-- A supported concrete shared-prefix cut carries the literal callback composition established by the original Builder and wrapper syntax. -/
theorem prefix_joined (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (reached : Local A (BareState 1) RootOracle.QueryCache)
    (supported : RawCtxForwardScan.Cut.pending (context, details) reached ∈ support
      (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    JoinedCapture owner number bit (context, details) := by
  exact shared_joined _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ supported

/-- A pending result is the exact missing-address cut, carrying that cut's original callback metadata. Cached and completed branches cannot manufacture a pending descriptor. -/
theorem collect_pending (start : Input) (output : HmacBlock) (depth : Nat)
    (cut : CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B))
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (supported : Sum.inr (pending, details) ∈ support
      (collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut)) :
    cut = .pending (pending.1, details) pending.2 := by
  cases cut <;> simp only [collect, cutMap, PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect] at supported
  · simp only [map_pure, attachRequest, mem_support_pure_iff, reduceCtorEq] at supported
  · split at supported
    · simp only [map_pure, attachRequest, requestAt, mem_support_pure_iff, Sum.inr.injEq, Prod.mk.injEq] at supported
      obtain ⟨rfl, rfl⟩ := supported
      rfl
    · simp only [map_bind, map_pure, attachRequest, mem_support_bind_iff, mem_support_pure_iff, reduceCtorEq, and_false, exists_false] at supported

/-- The complete concrete prepared sampler returns only the composition certificate of its actual reached missing-address callback. -/
theorem run_joined (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (details : Option (Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)))
    (supported : Sum.inr (pending, details) ∈ support
      (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)) :
    JoinedCapture owner number bit (pending.1, details) := by
  simp only [run, mem_support_bind_iff] at supported
  obtain ⟨cut, reached, collected⟩ := supported
  have actual := collect_pending original callbacks baseImpl kem attachedVerify primitives secret challenge
    (withPost (setup := setup) start owner number bit adversary) output depth cut pending details collected
  rw [actual] at reached
  exact prefix_joined original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending.1 details pending.2 reached

end BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.prefix_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.prefix_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.collect_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.collect_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.prefix_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.prefix_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.collect_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.collect_pending
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture.run_joined
