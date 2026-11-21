-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.Computational.RegistrationWorldServerFrontend

/-! Current Server pin selection is pure and retains the complete supplied binding and ML public key. Its native interpretation preserves every World coordinate and performs no oracle query. Generic hash-cache lemmas below concern actual transcript hash operations, not pin selection. -/
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

def program (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) : OracleComp Spec PinReply :=
  pure (do let pin ← registration.begin_server_pin binding publicKey; ok (.Some pin))

/-- The complete current extracted helper selects the supplied pin without a primitive callback. -/
theorem source [beaconcrypt.auth.Operations]
    (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    Id.run (simulateQ (fun query => pure (beaconcrypt.auth.execute_hash query) : QueryImpl Spec Id)
      (program binding publicKey)) = beaconcrypt_public_wrapper.auth.server_pin binding publicKey := rfl

noncomputable def nativeHash : QueryImpl Spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) := fun query => do
  let digest ← PqxdhRecordLiftWorld.effects (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes query)))
  pure (.ok (.Some (RegistrationAuthenticationShared.digestArray digest)))

noncomputable def native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp PinReply := simulateQ nativeHash (program binding publicKey)

theorem native_run (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : PqxdhRecordLiftWorld.State n) :
    (native binding publicKey).run before =
      pure (.ok (.Some (⟨binding, publicKey⟩ : session.ServerAuthenticationPin)), before) := rfl

/-- Repeated selection returns the complete stored pin and leaves the World unchanged. -/
theorem native_exact (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n) :
    (native pin.binding pin.public_key).run before = pure (.ok (.Some pin), before) := by
  cases pin
  rfl

theorem native_no_uniform (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n) :
    ((native pin.binding pin.public_key).run before).IsTotalQueryBound 0 := by
  rw [native_exact]
  trivial

theorem program_no_queries (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    (program binding publicKey).IsTotalQueryBound 0 := by trivial

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

/-- The actual Server helper preserves the ordered key getters before pure pin selection. Getter failures remain literal RustM failures. -/
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

/-- The stateful free helper and native startup preserve the whole retained Global state. -/
theorem initialize_native {Auxiliary : Type} (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) :
    (RegistrationWorldServerFrontend.initializePin binding publicKey).run before =
      (fun result => (result.1, (before.1, { before.2 with world := (result.2, before.2.world.2) }))) <$>
        (native binding publicKey).run before.2.world.1 := by
  rw [RegistrationWorldServerFrontend.initializePin_native, native_run, map_pure]

/-- Pure pin selection passes the original state to every adaptive continuation. -/
theorem native_bind {Value : Type} (pin : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n)
    (next : PinReply → StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) :
    ((native pin.binding pin.public_key >>= next).run before) = (next (.ok (.Some pin))).run before := by
  rw [StateT.run_bind, native_exact, pure_bind]

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

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_no_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_no_uniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.program_no_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.program_no_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.hash_hit

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

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.initialize_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute.native_bind
