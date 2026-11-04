-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache
import BeaconcryptCore.Computational.RegistrationNativeHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler

/-! Every actual corrected typed source callback extends the same shared cache, retaining all allocator, writer and primitive failures and external poststates. Dynamic private-key restoration preserves this cache literally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWorldCache (cache)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (law : RegistrationNativePlatformSdkCache.Keeps RegistrationNativePlatformSdkCache.serverCache work)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) :
    cache before ≤ cache result.1.2 := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact law before.server previous inner possible

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every literal corrected typed callback retains all earlier shared-cache entries on every outcome. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    cache before ≤ cache result.1.2 := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query =
      RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      cache before ≤ cache result.1.2 := by
    rw [same] at supported
    exact RegistrationNativeHandlerCache.handler setup checks wire route representation created credential query before result.1
      (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index => exact RegistrationNativePlatformPublicationCache.native_bundle coins setup checks representation created writer index before previous result supported
    | finish index packet =>
      exact RegistrationNativeWorldCache.beacon setup checks representation created _ before result.1
        (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
      exact server _ (RegistrationNativePlatformAcceptCache.accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route source.verify representation created packet)
        { before with parsedAccepts := before.parsedAccepts + 1 } previous result supported
    | build handle application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact server _ (RegistrationNativePlatformBuildCache.build coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer handle application) before previous middle called
    | _ => exact ordinary rfl

/-- Arbitrary adaptive corrected typed work extends its single source cache without losing failed platform effects. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer) work).run before).run previous)) :
    cache before ≤ cache result.1.2 := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact (handler coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before previous middle called).trans
        (ih middle.1.1 middle.1.2 middle.2 result continued)


/-- Actual true-count table restoration preserves cache extension without a cache, history or security premise. -/
theorem table (realSource : RegistrationNativeMldsa.Source)
    (opaqueCredential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource realSource))
    (fallback : RegistrationNativeMldsa.Credential realSource) (pool : RegistrationNativeMldsaOpaque.Pool realSource)
    (server : RegistrationNativeMldsaOpaque.Live realSource pool opaqueCredential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) (previous : Platform)
    (owners : RegistrationNativeMldsaPoolMap.StateLive realSource pool before)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) × Platform) × RegistrationNativeMldsaOpaque.Pool realSource)
    (supported : result ∈ support (RegistrationNativePlatformMldsaTableProgram.runState realSource
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created opaqueCredential view failure allocation
        reserveRegistration reservePeer erased helper writer query) before previous pool)) :
    cache before ≤ cache result.1.1.2 := by
  have actual : RegistrationNativePlatformMldsaTableRestore.observe realSource fallback result ∈ support
      (((RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created realSource fallback
        view failure allocation reserveRegistration reservePeer erased helper writer query).run
          (RegistrationNativeMldsaMap.nativeState (RegistrationNativeMldsaOpaque.restore realSource fallback pool) before)).run previous) := by
    rw [← RegistrationNativePlatformMldsaTableHandler.restored realSource setup checks wire route representation created opaqueCredential
      view failure allocation reserveRegistration reservePeer erased helper writer fallback pool server query before previous owners, support_map]
    exact ⟨result, supported, rfl⟩
  exact handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created fallback
    view failure allocation reserveRegistration reservePeer erased helper writer query _ previous _ actual

end BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache.table
