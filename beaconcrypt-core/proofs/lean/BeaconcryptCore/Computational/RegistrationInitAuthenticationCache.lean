-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSdkSource
import BeaconcryptCore.Computational.RegistrationAuthenticationNative
import BeaconcryptCore.Computational.RegistrationWorldAuthentication

/-! The actual accepted Init request/cache receipts need only the Server authentication source. The Native dispatcher and typed accept wrappers reuse these exact declarations under their original namespace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitAuthentication
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationWorldAuthentication.begin
  RegistrationServerNativeSource.authenticate RegistrationAuthenticationShared.begin
  RegistrationAuthenticationShared.implementation RawCtxSourceHkdf.kdfImpl
  RegistrationAuthenticationExecutor.execute RegistrationAuthenticationExecutor.begin
  registration.begin_init_authentication

def withWorld (before : State n) (world : PqxdhRecordLiftWorld.State n) : State n :=
  { before with world := { before.world with world := (world, before.world.world.2) } }

/-- Actual SDK authentication retains the original Server state and literal global signing-attempt list. -/
theorem authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) :
    (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before =
      Prod.map id (withWorld before) <$>
        (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1 := by
  simp only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run, Functor.map_map, Prod.map, id_eq]
  rfl

/-- The current hash/Ed trace gives its literal reached request-hash receipt. Keeping this generic avoids unfolding a concrete KDF while elaborating controller support. -/
private theorem shared_cache_receipt {Auxiliary : Type}
    (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    ∃ digest,
      after.2 ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  obtain ⟨initial, _began, _fields, _pin, preimage, executed⟩ := RegistrationAuthenticationNative.begin_parts
    crypto verify writer kdf pin packet before after events (.Accepted authenticated) supported
  have sharedSource : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (RegistrationAuthenticationExecutor.begin pin packet)).run before) := by
    simpa only [RegistrationAuthenticationShared.begin] using supported
  have execution := RegistrationAuthenticationExecutor.simulated_begin_sound
    (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
    pin packet events (.Accepted authenticated) before after sharedSource
  obtain ⟨_, _, _tail, recorded⟩ := BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.accepted_request_provenance
    pin packet events authenticated execution
  have trace := RegistrationAuthenticationInterpretation.execute_trace
    (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
    5 (.HashRequested initial) events (.Accepted authenticated) before after executed
  rw [recorded] at trace
  cases trace with
  | cons first rest =>
    obtain ⟨digest, sameEvent, _, cached⟩ := RegistrationInitGateExecutor.hash_edge_receipt
      crypto verify writer kdf initial _ _ _ _ first
    have hashEq : authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
      simpa only [BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event.hash.injEq,
        core.option.Option.Some, Option.some.injEq] using sameEvent
    have extension := RegistrationAuthenticationNative.program_cache_persists crypto verify writer kdf _ _ _
      (RegistrationAuthenticationInterpretation.trace_execute _ rest)
    have cachedAt : after.2 ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage pin packet) = some digest := by
      rw [← preimage]
      exact extension cached
    exact ⟨digest, cachedAt, hashEq⟩

/-- Same actual accepted Init authentication cut retains its reached global request-hash cache entry and consumed digest; no token-birth or path assumption is needed. -/
theorem authenticated_cache (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : State n) (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    ∃ digest,
      after.world.world.1.primitive.2 ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage before.pin packet) = some digest ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have valueEq : inner.1 = .ok (events, .Accepted authenticated) := congrArg Prod.fst same
  have native : (.ok (events, .Accepted authenticated), inner.2) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1) := by
    simpa only [← valueEq, Prod.mk.eta] using called
  have source := RegistrationWorldAuthentication.begin_native_support setup codec route verify before.pin packet
    before.world.world.1 inner.2 events authenticated native
  obtain ⟨digest, cached, hashEq⟩ := shared_cache_receipt setup.source.crypto verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) before.pin packet
    (RegistrationWorldAuthentication.project before.world.world.1) (RegistrationWorldAuthentication.project inner.2)
    events authenticated source
  have worldEq : (RegistrationNativeInitAuthentication.withWorld before inner.2) = after := congrArg Prod.snd same
  rw [← worldEq]
  exact ⟨digest, cached, hashEq⟩

end BeaconcryptCore.Computational.RegistrationNativeInitAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticated_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticated_cache
