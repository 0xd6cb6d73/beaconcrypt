-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld
import BeaconcryptCore.Computational.MldsaSharedSource

/-!
The instrumented global World retains every earlier entry of its actual shared CTX cache. Primitive persistence follows from the fixed source HKDF and actual ROM/AEAD/writer implementation, rather than a cache-preservation hypothesis. This supports retaining outgoing signing receipts through later registration and record operations.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationWorldCache

open CtxRomAuth
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every actual World primitive extends the shared cache, including optional AEAD and writer failures. -/
theorem primitive_cache (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : PqxdhRecordLiftWorld.Primitive)
    (result : RawCtxMixedOwner.NativeSpec.Range query × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.primitives setup codec query).run state)) :
    state.2 ≤ result.2.2 := by
  have projected : (result.1, result.2.2) ∈ support
      (Prod.map id Prod.snd <$> (PqxdhDeploymentNative.primitives setup codec query).run ((), state.2)) := by
    rw [← PqxdhRecordLiftWorld.primitives_forget setup codec query state, support_map]
    exact ⟨result, supported, rfl⟩
  rw [support_map] at projected
  obtain ⟨native, member, same⟩ := projected
  exact (congrArg Prod.snd same) ▸
    MldsaSharedSource.query_cache_persists setup.source codec.frameWrite (.inr query) ((), state.2) native member

/-- Complete native record work retains all earlier hash receipts, including its literal writer log. -/
theorem primitive_program_cache {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRecordLiftWorld.Primitive)
    (result : Result × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) work).run state)) :
    state.2 ≤ result.2.2 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | query_bind query next ih =>
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, first, rest⟩ := supported
    exact (primitive_cache setup codec query state step first).trans (ih step.1 step.2 result rest)

/-- Instrumenting any source randomness changes its uniform counter and retains the exact cache. -/
theorem sampled_cache {Result : Type} (work : ProbComp Result) (state : PqxdhRecordLiftWorld.State n)
    (result : Result × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run state)) :
    result.2.primitive.2 = state.primitive.2 := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, _member, rfl⟩ := supported
  rfl

/-- Both known and hidden kernel resolution preserve the actual shared cache. -/
theorem resolve_cache (role : Role) (ref : KernelRef n) (state : PqxdhRecordLiftWorld.State n)
    (result : ConcreteRatchetKernel × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.resolve role ref).run state)) :
    result.2.primitive.2 = state.primitive.2 := by
  cases ref with
  | known kernel =>
    simp only [PqxdhRecordLiftWorld.resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact congrArg (fun output => output.2.primitive.2) supported
  | hidden slot =>
    obtain ⟨_seed, _kernel, _present, _persist, _used, _server, _owners, _raw, _produced,
      cached, _native, _effects⟩ := PqxdhRecordLiftWorld.resolve_hidden_facts role slot state result supported
    exact cached

private theorem markUsed_cache (state : PqxdhRecordLiftWorld.State n) (role : Role) (ref : KernelRef n) :
    (PqxdhRecordLiftWorld.markUsed state role ref).primitive.2 = state.primitive.2 := by
  cases ref <;> rfl

/-- Server installation preserves the shared cache across admission, rejection and hidden seed allocation. -/
theorem installServer_cache (keyId : Std.U64) (binding : PeerBinding) (ref : KernelRef n)
    (state : PqxdhRecordLiftWorld.State n) (result : Bool × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installServer keyId binding ref).run state)) :
    result.2.primitive.2 = state.primitive.2 := by
  cases found : state.server with
  | none =>
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, found, support_pure,
      Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some server =>
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, found] at supported
    split_ifs at supported with admitted
    · simp only [bind_pure_comp, support_map] at supported
      obtain ⟨resolved, member, rfl⟩ := supported
      exact (markUsed_cache resolved.2 .server ref).trans (resolve_cache .server ref state resolved member)
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl

/-- Beacon installation likewise preserves the exact shared cache. -/
theorem installBeacon_cache (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : PqxdhRecordLiftWorld.State n) (result : Bool × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installBeacon owner shell ref).run state)) :
    result.2.primitive.2 = state.primitive.2 := by
  simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨resolved, member, rfl⟩ := supported
    exact (markUsed_cache resolved.2 .beacon ref).trans (resolve_cache .beacon ref state resolved member)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- Every World capability extends the cache; a hash stores its actual returned digest. -/
theorem capability_cache (query : (CapabilitySpec n).Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : (CapabilitySpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.capability query).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 := by
  cases query with
  | installServer keyId binding ref => exact (installServer_cache keyId binding ref state result supported).ge
  | installBeacon owner shell ref => exact (installBeacon_cache owner shell ref state result supported).ge
  | peerPresent keyId =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | ownerPresent owner =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | appendOwner sender pin phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | hash bytes =>
    simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run,
      bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have actual : inner.1 ∈ support ((ctxRandomOracle ((), bytes)).run state.primitive.2) := by
      rw [← PqxdhRecordLiftWorld.countCoin_forget ((ctxRandomOracle ((), bytes)).run state.primitive.2)
        state.primitive.1.uniform, support_map]
      exact ⟨inner, member, rfl⟩
    exact (MldsaSharedAuthentication.query_cached bytes state.primitive.2 inner.1 actual).1
  | advanceOwner owner phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run] at supported
    split at supported
    · split_ifs at supported <;>
        simp only [support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact le_refl _
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact le_refl _

/-- Source coins and administrative capabilities preserve every prior cache entry. -/
theorem effects_cache (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : (EnvEffects n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects query).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 := by
  cases query with
  | inl coin => exact (sampled_cache (unifSpec.query coin)
      (PqxdhRecordLiftWorld.chargeEffect (.inl coin) state) result supported).ge
  | inr request => exact capability_cache request (PqxdhRecordLiftWorld.chargeEffect (.inr request) state) result supported

/-- Actual Server record execution preserves cache receipts through all raw and send branches. -/
theorem server_cache (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhRecordLiftWorld.State n)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.serverStep setup codec route query).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 := by
  cases found : state.server with
  | none =>
    rcases query with _ | _ <;>
      simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, found, support_pure,
        Set.mem_singleton_iff] at supported <;>
      subst result <;> exact le_refl _
  | some server =>
    simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact primitive_program_cache setup codec _ state.primitive inner member

/-- Actual Beacon record execution retains every earlier signing/authentication hash. -/
theorem beacon_cache (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.beaconStep setup codec owner query).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 := by
  cases found : state.owners[owner]? with
  | none =>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, support_pure,
      Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | some phase =>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact primitive_program_cache setup codec _ state.primitive inner member

/-- Every actual global request preserves all earlier entries of the one instrumented CTX cache. -/
theorem handler_cache (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : PqxdhRecordLiftWorld.State n)
    (result : (WorldSpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 := by
  cases query with
  | inl created =>
    cases found : state.server <;>
      simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.initializeServer, StateT.run,
        found, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact le_refl _
  | inr outer =>
    cases outer with
    | inl effect => exact effects_cache effect state result supported
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => exact server_cache setup codec route (.inl send) state result supported
        | inr raw => exact server_cache setup codec route (.inr raw) state result supported
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => exact beacon_cache setup codec owner (.inl plaintext) state result supported
        | inr raw => exact beacon_cache setup codec owner (.inr raw) state result supported

/-- Any complete adaptive World continuation preserves a frozen prefix's cache receipts. -/
theorem program_cache {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftWorld.State n) (result : Result × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run state)) :
    state.primitive.2 ≤ result.2.primitive.2 :=
  simulateQ_run_preservesInv (PqxdhRecordLiftWorld.handler setup codec route)
    (fun current => state.primitive.2 ≤ current.primitive.2)
    (fun query current earlier after member => earlier.trans (handler_cache setup codec route query current after member))
    work state (le_refl _) result supported

end BeaconcryptCore.Computational.RegistrationWorldCache

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.primitive_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.primitive_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.primitive_program_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.primitive_program_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.sampled_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.sampled_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.resolve_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.resolve_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.installServer_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.installServer_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.installBeacon_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.installBeacon_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.capability_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.capability_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.effects_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.effects_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.server_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.server_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.beacon_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.beacon_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.handler_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.handler_cache
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCache.program_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCache.program_cache
