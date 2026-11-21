-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCached
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCached
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant

/-! Cached validity of the complete actual corrected native signing history is an execution invariant. Actual source bundle/build publication derives new receipts from preceding hashes, while all incoming and ordinary callbacks preserve their literal prefix and extend the same cache. No complete-handler validity or protocol-security premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev Valid (before : RegistrationNativeExperiment.State n KemSK source) : Prop :=
  RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (keeps : RegistrationNativePlatformSdkCached.Keeps RegistrationNativePlatformSdkCached.serverProject work)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform) (valid : Valid before)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) : Valid result.1.2 := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact keeps before.server previous inner valid called

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential
  view failure allocation reserveRegistration reservePeer erased helper writer

/-- Every complete actual corrected typed callback derives validity of every earlier and newly attempted signing receipt, including all failed source outcomes. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (valid : Valid before) (supported : result ∈ support (((callback query).run before).run previous)) : Valid result.1.2 := by
  have ordinary (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query) : Valid result.1.2 := by
    have history := RegistrationNativePlatformReceiptPreservation.source_handler coins setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer query allowed before previous result supported
    have extension := RegistrationNativePlatformHandlerCache.handler coins setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer query before previous result supported
    change result.1.2.server.world.world.2 = before.server.world.world.2 at history
    change RegistrationSigningShared.Cached (result.1.2.server.world.world.2, result.1.2.server.world.world.1.primitive.2)
    rw [history]
    exact RegistrationSigningShared.cached_extend _ _ _ extension valid
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId =>
      exact RegistrationNativeMldsaInvariant.handler setup checks wire route representation created credential (.inr (.create edPin mlPin keyId)) before valid result.1
        (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
    | bundle index => exact RegistrationNativePlatformBundleCached.native_bundle source setup checks representation created writer index before previous result valid supported
    | build index application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact server _ (RegistrationNativePlatformServerCached.build setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer index application) before previous middle valid called
    | _ => exact ordinary trivial

/-- Arbitrary adaptive corrected typed work retains the complete actual cache/history invariant. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (valid : Valid before) (supported : result ∈ support (((simulateQ callback work).run before).run previous)) : Valid result.1.2 := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1.1 middle.1.2 middle.2 result
      (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        query before previous middle valid called) continued

end BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant.program
