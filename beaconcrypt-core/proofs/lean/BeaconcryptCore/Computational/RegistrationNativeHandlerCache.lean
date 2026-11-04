-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerCache
import BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover

/-! All complete original native typed callbacks extend their single shared CTX cache. Actual opaque-table restoration preserves that cache literally, so the same monotonicity applies to the true-count dynamic generation family. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHandlerCache
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build
private theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (persistent : ∀ before result, result ∈ support (work.run before) → before.primitive.2 ≤ result.2.primitive.2)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) : RegistrationNativeWorldCache.cache before ≤ RegistrationNativeWorldCache.cache result.2 := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact persistent before.server.world.world.1 inner possible

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (keeps : ∀ before result, result ∈ support (work.run before) →
      before.world.world.1.primitive.2 ≤ result.2.world.world.1.primitive.2)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) : RegistrationNativeWorldCache.cache before ≤ RegistrationNativeWorldCache.cache result.2 := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact keeps before.server inner possible

private theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) : RegistrationNativeWorldCache.cache before ≤ RegistrationNativeWorldCache.cache result.2 := by
  cases query with
  | inl query => exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr (.inl query)))) before result supported
  | inr pair =>
      rcases pair with ⟨owner, command⟩
      cases command with
      | inl plaintext =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          cases found : before.beacons[owner]? with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact le_refl _
          | some selected =>
              simp only [found] at supported
              exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before result supported
      | inr raw =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          cases found : before.beacons[owner]? with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact le_refl _
          | some selected =>
              simp only [found] at supported
              exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before result supported

/-- Every original typed callback extends the literal shared cache, including all optional failures and terminal outcomes. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    RegistrationNativeWorldCache.cache before ≤ RegistrationNativeWorldCache.cache result.2 := by
  cases query with
  | inl coin => exact world _ (RegistrationWorldCache.effects_cache (.inl coin)) before result supported
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeWorldCache.beacon setup checks representation created _ before result supported
    | bundle owner => exact RegistrationNativeWorldCache.beacon setup checks representation created _ before result supported
    | build session application =>
        exact server _
          (RegistrationNativeServerCache.build_cache setup (RegistrationNativeWire.ledgerCodec wire) checks
            (RegistrationNativeMldsa.owned source credential) wire.encodeResponse session application) before result supported
    | accept packet =>
        have law : (RegistrationNativeExperiment.handler setup checks wire route representation created source credential
            (.inr (.accept packet))).run before =
            (fun result => (result.1, { before with parsedAccepts := before.parsedAccepts + 1, server := result.2 })) <$>
              (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
                representation created packet).run before.server := by
          simp only [RegistrationNativeExperiment.handler, StateT.run]
          rfl
        rw [law, support_map] at supported
        obtain ⟨inner, possible, same⟩ := supported
        cases same
        exact RegistrationNativeServerCache.accept_cache setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
          representation created packet before.server inner possible
    | finish owner packet => exact RegistrationNativeWorldCache.beacon setup checks representation created _ before result supported
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact le_refl _
    | hash bytes => exact world _ (RegistrationWorldCache.effects_cache (.inr (.hash bytes))) before result supported
    | serverSend keyId plaintext => exact record setup wire route (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record setup wire route (.inl (.inr raw)) before result supported
    | beaconSend owner plaintext => exact record setup wire route (.inr (owner, .inl plaintext)) before result supported
    | beaconRaw owner raw => exact record setup wire route (.inr (owner, .inr raw)) before result supported

/-- The exact actual private-table callback extends the same literal cache; dynamic key restoration changes only credentials. -/
theorem table (mlSource : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource mlSource))
    (fallback : RegistrationNativeMldsa.Credential mlSource) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) mlSource)
    (safe : RegistrationNativeMldsaTableStop.Safe mlSource credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) mlSource)
    (supported : result ∈ support ((RegistrationNativeMldsaTableStop.callback mlSource setup checks wire route representation created credential query).run before)) :
    RegistrationNativeWorldCache.cache before.1 ≤ RegistrationNativeWorldCache.cache result.2.1 := by
  simp only [RegistrationNativeMldsaTableStop.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  have restored : RegistrationNativeMldsaTableRestore.observe mlSource fallback inner ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource fallback query).run
        (RegistrationNativeMldsaMap.nativeState (RegistrationNativeMldsaOpaque.restore mlSource fallback before.2) before.1)) := by
    rw [← RegistrationNativeMldsaTableHandler.restored mlSource setup checks wire route representation created credential fallback before.2
      safe.server query before.1 safe.owners, support_map]
    exact ⟨inner, reached, rfl⟩
  exact handler setup checks wire route representation created fallback query _ _ restored

/-- A single actual simultaneous-family callback extends its retained global cache, including every failed generation or signing path. -/
theorem family {cap : Nat} (mlSource : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource mlSource))
    (fallback : RegistrationNativeMldsa.Credential mlSource) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaGhostFamily.State mlSource cap n KemSK)
    (safe : RegistrationNativeMldsaFamilyCover.Safe mlSource credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeMldsaGhostFamily.State mlSource cap n KemSK)
    (supported : result ∈ support ((RegistrationNativeMldsaGhostFamily.callback mlSource setup checks wire route representation created credential query).run before)) :
    RegistrationNativeWorldCache.cache before.1 ≤ RegistrationNativeWorldCache.cache result.2.1 := by
  apply table mlSource setup checks wire route representation created credential fallback query
    (RegistrationNativeMldsaGhostFamily.nativeState mlSource before) safe.1.safe
    (result.1, RegistrationNativeMldsaGhostFamily.nativeState mlSource result.2)
  rw [← RegistrationNativeMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeHandlerCache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHandlerCache.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHandlerCache.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHandlerCache.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHandlerCache.table

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHandlerCache.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHandlerCache.family
