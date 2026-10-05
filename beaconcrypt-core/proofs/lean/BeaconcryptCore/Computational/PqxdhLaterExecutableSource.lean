import BeaconcryptCore.Computational.PqxdhLaterExecutableCompletion
import BeaconcryptCore.Computational.PqxdhLaterPreparedCompletion

/-! The actual certified sampler supplies every premise for the source side of the saved-continuation comparison. No new descriptor, parser, callback or continuation premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableSource
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
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
  (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
open PqxdhFirstRecordConfidentiality

noncomputable def pendingOriginal (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (key : RootOutput) (component : AdaptiveCtxDynamicKnownKeys.SourceState) := by
  let fits : PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
    simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
  exact
  PqxdhLaterSavedPostComparison.original
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.val.2.1.2) (result.val.2.2.1) (result.val.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.val.2.1.1.2)).material fits (pending.2, component)

noncomputable def pendingCompiled (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (key : RootOutput) (component : AdaptiveCtxDynamicKnownKeys.SourceState) := by
  let fits : PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
    simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
  exact
  PqxdhLaterSavedPostComparison.compiled
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.val.2.1.2) (result.val.2.2.1) (result.val.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode ⟨0, Nat.zero_lt_succ _⟩ (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.val.2.1.1.2)).material fits (pending.2, component)

/-- On every actual pending output, the comparison's complete source projection is the literal saved native resumption. Its descriptor and callback premises all come from the same executed sampler. -/
theorem pending_native (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (cache : CtxRO.QueryCache)
    (supported : (result, cache) ∈ support ((simulateQ hashImpl
      (PqxdhLaterExecutableCertificates.certified env callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅))
    (key : RootOutput) (component : AdaptiveCtxDynamicKnownKeys.SourceState) (sameCache : component.cache = cache) :
    (fun final => ((final.1, (tracedProj key final.2).1), retainedOf (tracedProj key final.2).2)) <$>
      pendingOriginal setup env callbacks program post attachedVerify primitives baseImpl kem c result start pending shape key component =
    (fun final => ((some final.1.1, final.1.2), final.2)) <$>
      PqxdhLaterPreparedCompletion.native setup env (result.val, cache) start pending key := by
  have actual := PqxdhLaterPreparedCompletion.source setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed (result.val, cache) start pending key component c depth
    (PqxdhLaterExecutableCertificates.evaluated_support env callbacks baseImpl kem attachedVerify primitives program post
      selected number ancestors disclosed c depth (result, cache) supported) shape sameCache
  rw [actual]
  let fits : PqxdhInitialOriginCertificates.Fits
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 := by
    simpa only [PqxdhLaterExecutableCertificates.PacketFits, shape] using result.property
  have projected := PqxdhLaterSavedPostComparison.original_source
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem result.val.1.1 result.val.1.2)
    (initialLocal (A := A) (N := BareState 1) (env0).source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem result.val.1.1 result.val.1.2))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) env.source env.recordWriter (view (productionStream env.source.crypto) pending.2.store.1) key (result.val.2.1.2) (result.val.2.2.1) (result.val.2.2.2)
    (PqxdhInitialSampledParent.marker env.source start) env.senderId env.route env.decode (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ((result.val.2.1.1.2)).material fits (pending.2, component)
  have lifted := congrArg (fun work => (fun value => ((value.1, value.2.1), retainedOf value.2.2)) <$> work) projected
  simpa only [pendingOriginal, PqxdhLaterPreparedCompletion.evaluated, Functor.map_map] using lifted

/-- On the pending branch, the actual whole-client suffix is precisely the full component computation appearing in the saved-source comparison; outer refusal and every poststate field are retained. -/
theorem pending_compiled (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (result : PqxdhLaterExecutableCertificates.Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) (start : Input × HmacBlock) (pending : Pending)
    (shape : result.val.2.1.1.1 = .inr (start, .inr pending))
    (key : RootOutput) (component : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto key)
      (PqxdhLaterExecutableCompletion.suffix setup env callbacks program post attachedVerify primitives baseImpl kem c result)).run component =
    (fun final => ((Sum.inr (result.val, (final.1, final.2.1)) : PqxdhLaterExecutableCompletion.Output
      (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response)
      (A := A) (KemSK := KemSK) (S := S) (B := B)), final.2.2)) <$>
      pendingCompiled setup env callbacks program post attachedVerify primitives baseImpl kem c result start pending shape key component := by
  unfold PqxdhLaterExecutableCompletion.suffix
  split
  · rename_i decision impossible
    simp only [shape, reduceCtorEq] at impossible
  · rename_i start' decision impossible
    simp only [shape, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at impossible
  · rename_i start' pending' same
    have fields : start = start' ∧ pending = pending' := by
      simpa only [shape, Sum.inr.injEq, Prod.mk.injEq] using same
    rcases fields with ⟨rfl, rfl⟩
    simp only [pendingCompiled, PqxdhLaterSavedPostComparison.compiled, bind_pure_comp,
      simulateQ_map, StateT.run_map, Functor.map_map, PqxdhSelectedStateInterpreter.pair]

end BeaconcryptCore.Computational.PqxdhLaterExecutableSource

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableSource.pending_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableSource.pending_native
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableSource.pending_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableSource.pending_compiled
