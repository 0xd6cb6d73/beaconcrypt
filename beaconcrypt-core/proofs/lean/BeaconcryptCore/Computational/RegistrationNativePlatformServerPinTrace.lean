-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativeServerPinCached

/-! The configured Server pin is immutable in the actual corrected source callbacks, including effectful Init publication and assigned-ID finish. Actual constructor field provenance therefore remains true at every reached source cut; selecting the pin performs no hash query. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeServerPinCached (Configured)
variable (referenceBinding : pqxdh.ServerBinding) (referencePublicKey : Std.Array U8 1952#usize)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept

private def Keeps (work : StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → result.1.2.server.pin = before.server.pin

private theorem program_keeps {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp)))
    (law : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) : Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      intro before previous result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      intro before previous result supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact (ih middle.1.1 middle.1.2 middle.2 result continued).trans (law query before previous middle called)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (law : ∀ before previous result, result ∈ support ((work.run before).run previous) → result.1.2.pin = before.pin) :
    Keeps (source := source) (KemSK := KemSK) (RegistrationNativePlatformExperiment.server work) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact law before.server previous inner possible

private theorem bundle_query (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) :
    Keeps (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer query) := by
  cases query with
  | inl query =>
      intro before previous result supported
      exact RegistrationNativeServerPinTrace.trusted_pin setup checks representation created query before result.1
        (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
  | inr query =>
      intro before previous result supported
      simp only [RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
        StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Keeps (RegistrationNativePlatformExperiment.bundle (n := n) coins setup checks representation created source writer index) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_apply, mem_support_bind_iff] at supported
  obtain ⟨middle, called, returned⟩ := supported
  simp only [pure_apply, support_pure, Set.mem_singleton_iff] at returned
  cases returned
  exact program_keeps _ (bundle_query coins setup checks representation created writer) _ before previous middle called

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every literal corrected typed callback preserves its original configured Server pin on all outcomes. -/
theorem handler_pin (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    result.1.2.server.pin = before.server.pin := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query =
      RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      result.1.2.server.pin = before.server.pin := by
    rw [same] at supported
    exact RegistrationNativeServerPinTrace.handler_pin setup checks wire route representation created credential query before result.1
      (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index => exact bundle coins setup checks representation created writer index before previous result supported
    | finish index packet =>
      exact RegistrationNativeServerPinTrace.beacon_pin setup checks representation created _ before result.1
        (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
      exact server _ (RegistrationNativePlatformServerPinFields.accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route source.verify representation created packet)
        { before with parsedAccepts := before.parsedAccepts + 1 } previous result supported
    | build handle application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact server _ (RegistrationNativePlatformServerPinFields.build coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer handle application) before previous middle called
    | _ => exact ordinary rfl

/-- Arbitrary adaptive corrected work retains the same configured Server pin and full external poststate. -/
theorem program_pin (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer) work).run before).run previous)) :
    result.1.2.server.pin = before.server.pin :=
  program_keeps _ (handler_pin coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer) work before previous result supported


/-- The exact configured pin fields survive every corrected callback, including failed source allocation and publication. -/
theorem handler_configured (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (cached : Configured before.server.pin referenceBinding referencePublicKey)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    Configured result.1.2.server.pin referenceBinding referencePublicKey := by
  rw [handler_pin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before previous result supported]
  exact cached

/-- Every reached typed continuation retains the same configured pin fields. -/
theorem program_configured (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (cached : Configured before.server.pin referenceBinding referencePublicKey)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer) work).run before).run previous)) :
    Configured result.1.2.server.pin referenceBinding referencePublicKey := by
  rw [program_pin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work before previous result supported]
  exact cached

/-- The configured public fields at each reached source cut follow from actual startup and the literal adaptive program. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (previous : Platform)
    (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation initial.created source initial.credential
      view failure allocation reserveRegistration reservePeer erased helper writer) work).run initial.state).run previous)) :
    Configured result.1.2.server.pin
      ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey :=
  program_configured
    (referenceBinding := ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩)
    (referencePublicKey := initial.credential.publicKey)
    coins setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer work initial.state previous
    (RegistrationNativeServerPinCached.start_fields setup ensureInit identityIndex serverKeyId initial started) result supported

section Table
variable (realSource : RegistrationNativeMldsa.Source)
    (opaqueCredential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource realSource))
    (fallback : RegistrationNativeMldsa.Credential realSource) (pool : RegistrationNativeMldsaOpaque.Pool realSource)
    (live : RegistrationNativeMldsaOpaque.Live realSource pool opaqueCredential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) (previous : Platform)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) × Platform) × RegistrationNativeMldsaOpaque.Pool realSource)
    (supported : result ∈ support (RegistrationNativePlatformMldsaTableProgram.runState realSource
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created opaqueCredential view failure allocation
        reserveRegistration reservePeer erased helper writer query) before previous pool))

include supported live

private theorem restored : RegistrationNativePlatformMldsaTableRestore.observe realSource fallback result ∈ support
      (((RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created realSource fallback
        view failure allocation reserveRegistration reservePeer erased helper writer query).run
          (RegistrationNativeMldsaMap.nativeState (RegistrationNativeMldsaOpaque.restore realSource fallback pool) before)).run previous) := by
  rw [← RegistrationNativePlatformMldsaTableHandler.restored realSource setup checks wire route representation created opaqueCredential
    view failure allocation reserveRegistration reservePeer erased helper writer fallback pool live query before previous, support_map]
  exact ⟨result, supported, rfl⟩

/-- Actual private-table key restoration leaves the configured Server pin literal across every corrected callback. -/
theorem table_pin : result.1.1.2.server.pin = before.server.pin :=
  handler_pin RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created fallback view failure allocation reserveRegistration reservePeer erased helper writer query _ previous _
    (restored setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer realSource opaqueCredential fallback pool live query before previous result supported)

/-- Configured pin-field provenance transports through the actual table with every returned source state retained. -/
theorem table_configured (prior : Configured before.server.pin referenceBinding referencePublicKey) :
    Configured result.1.1.2.server.pin referenceBinding referencePublicKey := by
  rw [table_pin setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer realSource opaqueCredential fallback pool live query before previous result supported]
  exact prior

end Table

omit primitive in
/-- Actual source table startup establishes the configured binding and complete ML public key. -/
theorem table_initialized (realSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) × RegistrationNativeMldsaOpaque.Pool realSource)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate realSource
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) (member : initial ∈ started.1) :
    Configured initial.state.server.pin
      ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey := by
  obtain ⟨fallback, live, _owners⟩ := RegistrationNativeMldsaTableStart.initialized realSource setup ensureInit identityIndex serverKeyId started startup initial member
  let actualInitial := RegistrationNativeMldsaMap.initial (RegistrationNativeMldsaOpaque.restore realSource fallback started.2) initial
  have actual : some actualInitial ∈ support (RegistrationNativeExperiment.start setup realSource ensureInit identityIndex serverKeyId) := by
    rw [← RegistrationNativeMldsaTableStart.start realSource setup ensureInit identityIndex serverKeyId, support_map]
    refine ⟨started, startup, ?_⟩
    have selected : started.1 = some initial := member
    simp only [RegistrationNativeMldsaTableStart.restored, selected, Option.bind_some, live, Option.map_some]
    rfl
  exact RegistrationNativeServerPinCached.start_fields setup ensureInit identityIndex serverKeyId actualInitial actual

end BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.handler_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.handler_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.program_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.program_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.handler_configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.handler_configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.program_configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.program_configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace.table_initialized
