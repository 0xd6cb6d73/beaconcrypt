-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Computational.RegistrationNativeServerPinStartup
import BeaconcryptCore.Computational.RegistrationNativeHandlerCache

/-! The actual extracted Server fingerprint helper issues one public-key hash at each call. Its free request program retains optional primitive failures and admits a common stateful native interpreter. A retained pin-cache receipt makes recomputation deterministic while preserving the extra hash-effect charge. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute
open PqxdhRecordLiftInterface
variable {n : Nat}

abbrev HashReply := RustM (core.option.Option (Std.Array U8 64#usize))
abbrev PinReply := RustM (core.option.Option session.ServerAuthenticationPin)
abbrev Spec := registration.HashRequest →ₒ HashReply

def request (publicKey : Std.Array U8 1952#usize) : registration.HashRequest :=
  .Single (Std.Array.to_slice publicKey)

def program (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) : OracleComp Spec PinReply := do
  let fingerprint ← Spec.query (request publicKey)
  pure (do
    let value ← fingerprint
    (⟨binding, publicKey⟩ : registration.PinFingerprint).resume value)

/-- Kernel-checked specialization of the complete extracted helper, including failed and divergent primitive results. -/
theorem source [beaconcrypt.auth.Operations]
    (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    Id.run (simulateQ (fun query => pure (beaconcrypt.auth.execute_hash query) : QueryImpl Spec Id)
      (program binding publicKey)) =
      beaconcrypt_public_wrapper.auth.fingerprint_pin binding publicKey := by
  simp only [program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, pure_bind]
  unfold beaconcrypt_public_wrapper.auth.fingerprint_pin registration.begin_server_pin
    registration.PinFingerprint.request
  rfl

noncomputable def nativeHash : QueryImpl Spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) := fun query => do
  let digest ← PqxdhRecordLiftWorld.effects (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes query)))
  pure (.ok (.Some (RegistrationAuthenticationShared.digestArray digest)))

noncomputable def native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp PinReply := simulateQ nativeHash (program binding publicKey)

theorem native_run (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : PqxdhRecordLiftWorld.State n) :
    (native binding publicKey).run before = (do
      let hashed ← (PqxdhRecordLiftWorld.effects (.inr (.hash (PqxdhRefinement.absBytes publicKey)))).run before
      pure (.ok (.Some (⟨binding, publicKey, RegistrationAuthenticationShared.digestArray hashed.1⟩ : session.ServerAuthenticationPin)), hashed.2)) := by
  simp only [native, program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, nativeHash,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, request,
    BeaconcryptCore.Refinement.RegistrationInputs.hashBytes, Std.Array.to_slice]
  rfl

def Cached (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache) : Prop :=
  ∃ digest, cache ((), PqxdhRefinement.absBytes pin.public_key) = some digest ∧
    RegistrationAuthenticationShared.digestArray digest = pin.fingerprint

/-- Cache hits retain the exact World and uniform count while recording one additional hash-effect request. -/
theorem hash_hit (input : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest)
    (before : PqxdhRecordLiftWorld.State n) (cached : before.primitive.2 ((), input) = some digest) :
    (PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before =
      pure (digest, PqxdhRecordLiftWorld.chargeEffect (.inr (.hash input)) before) := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run]
  have hit : (CtxRomAuth.ctxRandomOracle ((), input)).run
      (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash input)) before).primitive.2 =
      pure (digest, before.primitive.2) := QueryImpl.withCaching_run_some _ cached
  simp only [StateT.run] at hit
  rw [hit]
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_pure]
  rfl

/-- A stored actual pin-cache receipt makes repeated recomputation return the same pin, with the literal extra hash charge. -/
theorem native_hit (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n)
    (cached : Cached pin before.primitive.2) :
    (native pin.binding pin.public_key).run before =
      pure (.ok (.Some pin), PqxdhRecordLiftWorld.chargeEffect (.inr (.hash (PqxdhRefinement.absBytes pin.public_key))) before) := by
  obtain ⟨digest, hit, fingerprint⟩ := cached
  rw [native_run, hash_hit _ _ _ hit]
  simp only [pure_bind, fingerprint]

/-- The repeated cached helper emits zero underlying uniform queries; its hash-effect request remains charged. -/
theorem native_hit_uniform (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n)
    (cached : Cached pin before.primitive.2) :
    ((native pin.binding pin.public_key).run before).IsTotalQueryBound 0 := by
  rw [native_hit pin before cached]
  trivial

theorem program_hashes (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    (program binding publicKey).IsTotalQueryBound 1 := by
  rw [program, isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

theorem charged_counts (input : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n) :
    let after := PqxdhRecordLiftWorld.chargeEffect (.inr (.hash input)) before
    after.primitive.2 = before.primitive.2 ∧ after.primitive.1.uniform = before.primitive.1.uniform ∧
      after.primitive.1.native = before.primitive.1.native ∧
      after.primitive.1.effects .hash = before.primitive.1.effects .hash + 1 := by
  simp only [PqxdhRecordLiftWorld.chargeEffect, effectKind, Function.update_self, and_self]

theorem hash_cached (input : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n)
    (result : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before)) :
    result.2.primitive.2 ((), input) = some result.1 := by
  have projected : (result.1, ((), result.2.primitive.2)) ∈ support
      (Prod.map id RegistrationWorldAuthentication.project <$>
        (PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [RegistrationWorldAuthentication.hash_project, support_map] at projected
  obtain ⟨queried, reached, same⟩ := projected
  have facts := (MldsaSharedAuthentication.query_cached input before.primitive.2 queried reached).2
  have digest := congrArg Prod.fst same
  have cache := congrArg (fun value => value.2.2) same
  change queried.1 = result.1 at digest
  change queried.2 = result.2.primitive.2 at cache
  simpa only [cache, digest] using facts

section Adapter
open BeaconcryptCore.Refinement.PublicWrapperPlatform
variable [Material] [Platform] [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [LocalOperations] [CryptoOperations] [beaconcrypt.auth.Operations]

/-- The original Server helper performs its actual ordered getters before the same exact lifted fingerprint request program. Getter failures remain literal RustM failures. -/
theorem server_source (self : beaconcrypt_public_wrapper.server.Server) :
    beaconcrypt_public_wrapper.server.Server.authentication_pin self = (do
      let key ← beaconcrypt_public_wrapper.server.Server.identity_pk self
      let bytes ← beaconcrypt_crypto.crypto_sign.PublicKey.as_bytes key
      let keyId ← beaconcrypt_public_wrapper.server.Server.identity_key_kid self
      let publicKey ← beaconcrypt_public_wrapper.server.Server.mldsa_public_key self
      Id.run (simulateQ (fun query => pure (beaconcrypt.auth.execute_hash query) : QueryImpl Spec Id)
        (program ⟨bytes, keyId⟩ publicKey))) := by
  simp only [source]
  rfl
end Adapter

/-- Startup's actual shared fingerprint call establishes the cache receipt needed by every later repeated helper. -/
theorem initialize_cached {Auxiliary : Type} (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before after : RegistrationWorldServerReplay.Global n Auxiliary) (pin : session.ServerAuthenticationPin)
    (supported : (.ok (.Some pin), after) ∈ support
      ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before)) :
    Cached pin after.2.world.1.primitive.2 := by
  rw [RegistrationWorldServerFrontend.initializePin_native] at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨hashed, reached, returned⟩ := supported
  cases returned
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at reached
  obtain ⟨world, actual, same⟩ := reached
  cases same
  exact ⟨world.1, hash_cached _ _ _ actual, rfl⟩

/-- The free helper's stateful interpretation is exactly the actual native startup fingerprint on the whole retained Global state. -/
theorem initialize_native {Auxiliary : Type} (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) :
    (RegistrationWorldServerFrontend.initializePin binding publicKey).run before =
      (fun result => (result.1, (before.1, { before.2 with world := (result.2, before.2.world.2) }))) <$>
        (native binding publicKey).run before.2.world.1 := by
  rw [RegistrationWorldServerFrontend.initializePin_native, native_run]
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, map_bind, map_pure, bind_map_left]

/-- Repeated cache-hit recomputation passes its exact charged poststate to every adaptive continuation. -/
theorem native_hit_bind {Value : Type} (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n)
    (cached : Cached pin before.primitive.2)
    (next : PinReply → StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    ((native pin.binding pin.public_key >>= next).run before) =
      (next (.ok (.Some pin))).run
        (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash (PqxdhRefinement.absBytes pin.public_key))) before) := by
  rw [StateT.run_bind, native_hit pin before cached, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit_uniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.program_hashes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.program_hashes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.charged_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.charged_counts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_hit_bind
