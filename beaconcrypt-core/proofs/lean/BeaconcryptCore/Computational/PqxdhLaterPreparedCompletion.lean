import BeaconcryptCore.Computational.PqxdhLaterSavedSampler

/-! The actual later-prefix output supplies every descriptor and callback premise of the complete saved source continuation. The endpoint here is the evaluated selected-material completion; its source equation retains all optional replies and the full outside Post. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterPreparedCompletion
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
open PqxdhNativeSharedPrefix PqxdhSelectedFirstRecord RawCtxSelectedParentTable PqxdhJointKdfGame RawCtxSelectedMessageDriver PqxdhJointKdf
local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
noncomputable def evaluated (result : PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × CtxRO.QueryCache)
    (start : PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (S := S) (B := B) × HmacBlock)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (key : RootOutput)
    (component : AdaptiveCtxDynamicKnownKeys.SourceState) (qPost : Nat) (fits : PqxdhInitialOriginCertificates.Fits qPost pending.1) :
    ProbComp (Bool × ((Front × Trace) × RawCtxSharedPrimitive.SharedState (Local A (BareState 1) RootOracle.QueryCache))) :=
  PqxdhLaterSavedContext.complete
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.1.1.1 result.1.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.1.1.1 result.1.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.1.1.1 result.1.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.1.2.1.2) (result.1.2.2.1) (result.1.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode qPost pending.1 ((result.1.2.1.1.2)).material fits (pending.2, component)

noncomputable def native (result : PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × CtxRO.QueryCache)
    (start : PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (S := S) (B := B) × HmacBlock)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (key : RootOutput) :
    ProbComp ((Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState A (BareState 1) RootOracle.QueryCache) :=
  (simulateQ (PqxdhInitialNativeRetained.retained env.source env.recordWriter
    (privateTable (view (productionStream env.source.crypto) pending.2.store.1) (some (result.1.2.1.1.2)) (result.1.2.1.2) (RawCtxSelectedMessageKdf.response key (result.1.2.2.1) (result.1.2.2.2)))
    (PqxdhInitialOriginFinishPath.withInitial env.source start.1.selectedMessage zeroRoot
      (PqxdhInitialSampledParent.response start) start.1.other))
    (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode pending.1
      (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
        (RawCtxSelectedParentEntry.realize (result.1.2.1.1.2) (result.1.2.1.2))))).run
    (PqxdhInitialNativeRetained.project (attach pending.2 result.2).1)

/-- The exact supported sampler output completes through concrete source callbacks without a quiet-tail, parser-provenance or callback-factorization assumption. The saved request starts from the supplied component state with its existing cache equal to the reached source cache; the compared source result projects component bookkeeping to that cache. -/
theorem source (result : PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × CtxRO.QueryCache)
    (start : PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (S := S) (B := B) × HmacBlock)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (key : RootOutput)
    (component : AdaptiveCtxDynamicKnownKeys.SourceState) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (supported : result ∈ support ((simulateQ hashImpl (PqxdhLaterSavedSampler.run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth)).run ∅))
    (shape : result.1.2.1.1.1 = .inr (start, .inr pending)) (cache : component.cache = result.2) :
    native setup env result start pending key =
      (fun value => ((value.1, value.2.1), retainedOf value.2.2)) <$>
        evaluated setup env callbacks attachedVerify primitives baseImpl kem result start pending key component
          (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)
          (PqxdhLaterSavedSampler.pending_scope setup env callbacks program post attachedVerify primitives baseImpl kem
            selected number ancestors disclosed c depth result supported start pending shape).1 := by
  have scopeFacts := PqxdhLaterSavedSampler.pending_scope setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed c depth result supported start pending shape
  have external := PqxdhSelectedFirstRecord.prepared_lifted setup env callbacks ∅ baseImpl kem attachedVerify primitives
    result.1.1.1 result.1.1.2 start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start)
  rw [← scopeFacts.2.2.2] at external
  have actual := PqxdhLaterSavedContext.retained_complete
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.1.1.1 result.1.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.1.1.1 result.1.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.1.1.1 result.1.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter
    (view (productionStream env.source.crypto) pending.2.store.1) key (result.1.2.1.2) (result.1.2.2.1) (result.1.2.2.2) (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode
    (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.1.2.1.1.2)).material scopeFacts.1 scopeFacts.2.1 (pending.2, component)
  rw [external] at actual
  have parentEq : Entry.mk (PqxdhInitialBuilderContext.address pending.1.original) ((result.1.2.1.1.2)).material = (result.1.2.1.1.2) := by
    rw [← scopeFacts.2.2.1]
  rw [parentEq] at actual
  simpa only [native, evaluated, retainedOf, RawCtxSelectedReceiveCompiler.project,
    PqxdhInitialNativeRetained.project, attach, cache, PqxdhSourceSharedPreparation.environment, PqxdhPreparedSharedPrefix.environment] using actual

end BeaconcryptCore.Computational.PqxdhLaterPreparedCompletion

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterPreparedCompletion.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterPreparedCompletion.source
