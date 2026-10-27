import BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology

/-! Actual sampled wrapper cuts retain the reached source request and its unchanged chronological backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology
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

open PqxdhLaterChallengePreparedCapture
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "Details" => PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)
local notation "Cut" => CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)

/-- A pending collector result comes from the same actual pending cut and retains its reached ROM cache. Complete and cached branches keep their original Booleans. -/
theorem collect_evaluated (start : Input) (output : HmacBlock) (depth : Nat)
    (cut : Cut) (pending : Pending) (details : Option Details)
    (cache after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, details), after) ∈ support
      ((simulateQ hashImpl (collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut)).run cache)) :
    cut = .pending (pending.1, details) pending.2 ∧ after = cache := by
  have syntactic : Sum.inr (pending, details) ∈ support
      (collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut) :=
    support_simulateQ_run'_subset hashImpl _ cache (by
      simpa only [StateT.run'_eq, support_map, Set.mem_image] using
        (show ∃ result, result ∈ support ((simulateQ hashImpl
          (collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut)).run cache) ∧
          result.1 = Sum.inr (pending, details) from ⟨(Sum.inr (pending, details), after), supported, rfl⟩))
  have same := collect_pending original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut pending details syntactic
  subst cut
  refine ⟨rfl, ?_⟩
  simp only [collect, PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, cutMap] at supported
  split at supported
  · exact (Prod.mk.inj ((mem_support_pure_iff _ _).mp supported)).2
  · simp only [map_bind, map_pure, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at supported
    obtain ⟨result, _, impossible, _⟩ := supported
    cases impossible

/-- The complete evaluated prepared sampler returns a pending descriptor only at the identical shared prefix cut and its actual cache. No completed or cached continuation is discarded from the sampler. -/
theorem run_prefix (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Option Details) (cache after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache)) :
    (RawCtxForwardScan.Cut.pending (pending.1, details) pending.2, after) ∈ support
      ((simulateQ hashImpl (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache) := by
  simp only [PqxdhLaterChallengePreparedCapture.run, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨cut, current⟩, reached, collected⟩ := supported
  obtain ⟨rfl, rfl⟩ := collect_evaluated original callbacks baseImpl kem attachedVerify primitives secret challenge
    (withPost (setup := setup) start owner number bit adversary) output depth cut pending details current after collected
  exact reached

/-- The existing concrete audited source callbacks at the same prepared input. This is the mathematical source interpreter, including its original private KEM data and full logs/caches. -/
noncomputable def native (start : Input) (output : HmacBlock) (depth : Nat) :=
  PqxdhInitialNativeAudit.handler (S := S) (B := B + 1) (env).source (env).recordWriter (depth + 1)
    (fun query => localLift (pre query)) (fun reply => localLift (application reply))
    (fun secrets => localLift (initialLocal (env).source start.selectedMessage zeroRoot
      (RawCtxSelectedInitialConstructor.response64 output) secrets))
    (fun query => localLift (selector query)) (fun query => localLift (aux query))

/-- Actual Builder and wrapper chronology for this prepared source draw. The source prefix and callback-local cut retain the full audited backend; the captured request is not reconstructed from a matching result. -/
def Reached (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache) : Prop :=
  let execution := PqxdhInitialSourceExperiment.execution (RawCtxSelectedInitialConstructor.response64 output)
    start.index start.metadata { start.ready with root := zeroRoot }
    (withPost (setup := setup) start owner number bit adversary).post start.before
  let impl := native original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  let marker := PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage
  ∃ built backend front history ambient,
    (built, backend) ∈ support ((simulateQ impl (simulateQ RawCtxForwardAnnotation.erase
      (PqxdhInitialOriginForwardBuilder.program (env).source marker execution.origin (env).senderId (env).route (env).decode
        execution.initial execution.index execution.metadata execution.ready pure execution.before execution.trace))).run
      (attach (PqxdhPreparedSharedPrefix.state original start output) cache)) ∧
    PqxdhRecordConfidentialityTrace.Reaches (PqxdhLaterChallengeCutChronology.postImpl marker (env).senderId (env).route (env).decode impl)
      owner number bit (adversary built.1) PqxdhRecordConfidentialityChallenge.initial (built.2, backend)
      ((PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)).query details.request.query >>= details.request.next)
      details.request.before ((front, history), ambient) ∧
    RawCtxForwardScan.Cut.pending details.callback (attach pending.2 after) ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativeAuditCarried.selected depth) (native_selection depth) impl
        (PqxdhInitialOriginForwardPost.program marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history)
        (PqxdhInitialOriginForwardPost.program_covered marker (env).senderId (env).route (env).decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front history) ambient)

/-- The actual prepared shared prefix supplies the complete native reached-request witness, including the initial Builder result and the same callback's source input history. -/
theorem prefix_reaches (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (supported : (RawCtxForwardScan.Cut.pending (pending.1, some details) pending.2, after) ∈ support
      ((simulateQ hashImpl (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache)) :
    Reached original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending details cache after := by
  exact PqxdhLaterChallengeCutChronology.shared_reaches (env).source (env).recordWriter (depth + 1) pre application
    (initialLocal (env).source start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)) selector aux
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) _ (env).senderId (env).route (env).decode
    _ _ _ _ _ _ owner number bit adversary depth (PqxdhPreparedSharedPrefix.state original start output) cache pending.2 after pending.1 details supported

/-- The complete concrete prepared sampler supplies actual source chronology for its returned wrapper capture. Its current cache, initial Builder result and original callback remain the same ones used by the full source run. -/
theorem run_reaches (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (pending : Pending) (details : Details) (cache after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache)) :
    Reached original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending details cache after :=
  prefix_reaches original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary
    pending details cache after
    (run_prefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary pending (some details) cache after supported)

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.collect_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.collect_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.run_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.run_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.prefix_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.prefix_reaches
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.run_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampleChronology.run_reaches
