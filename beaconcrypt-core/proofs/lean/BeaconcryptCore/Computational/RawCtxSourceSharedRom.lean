import BeaconcryptCore.Computational.RawCtxSelectedChallengeReceive
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer

/-!
The native source record backend factors through one explicit uniform/hash interface. Private and public HKDF evaluations remain the actual fixed source function; known-key seal/open and the optional source writer remain local deterministic work. Every commitment and public hash is forwarded unchanged, so the cache is constructed by executing the prefix rather than installed at a later cut. These operational statements do not claim that arbitrary external callbacks respect the ROM interface.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceSharedRom
open PqxdhJointKdfGame CtxRomAuth AdaptiveCtxSharedHash

/-- The real native callback leaves all known primitive computations local and exposes every hash request. -/
noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp HashSpec)
  | .inl request => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inl input) => pure (some (source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => pure (RawCtxSourceOpen.baseOpen source.crypto input)
  | .inr (.inr (.inr (.inl bytes))) => (fun digest => some digest.toList) <$> HashSpec.query (.inr ((), bytes))
  | .inr (.inr (.inr (.inr frame))) => pure (writer frame)

/-- Both native commitments and public queries use this single explicit hash interface. -/
noncomputable def backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxServerServices.BackendSpec (OracleComp HashSpec)
  | .inl coin => HashSpec.query (.inl coin)
  | .inr (.inl query) => native source writer query
  | .inr (.inr query) => pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address))

set_option backward.isDefEq.respectTransparency false in
/-- Actual native source replies and the entire shared state are retained by the explicit ROM factorization. -/
theorem native_step {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (ambient : A) (cache : CtxRO.QueryCache) :
    (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run (ambient, cache) =
      (fun result => (result.1, (ambient, result.2))) <$>
        (simulateQ hashImpl (native source writer query)).run cache := by
  rcases query with request | (input | (opening | (bytes | frame)))
  · rfl
  · rfl
  · rfl
  · rw [RawCtxMixedShared.shared_hash]
    change (do
      let result ← (ctxRandomOracle ((), bytes)).run cache
      pure (some result.1.toList, (ambient, result.2))) =
      (fun result => (result.1, (ambient, result.2))) <$>
        (simulateQ hashImpl ((fun digest => some digest.toList) <$> HashSpec.query (.inr ((), bytes)))).run cache
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source coins, real public HKDF, and every native callback retain their exact replies and cache in the factored backend. -/
theorem backend_step {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxServerServices.BackendSpec.Domain) (ambient : A) (cache : CtxRO.QueryCache) :
    (RawCtxProtocolBackend.backend source writer query).run (ambient, cache) =
      (fun result => (result.1, (ambient, result.2))) <$>
        (simulateQ hashImpl (backend source writer query)).run cache := by
  rcases query with coin | (query | query)
  · change (do let reply ← unifSpec.query coin; pure (reply, (ambient, cache)) : ProbComp _) =
      (fun result => (result.1, (ambient, result.2))) <$>
        (simulateQ hashImpl (HashSpec.query (.inl coin))).run cache
    simp only [simulateQ_spec_query]
    rw [AdaptiveCtxSharedModes.hash_uniform_step]
    simp only [bind_pure_comp]
    change ((fun reply => (reply, (ambient, cache))) <$> (unifSpec.query coin : ProbComp _)) = _
    rw [Functor.map_map]
  · exact native_step source writer query ambient cache
  · rfl

/-- The complete original source computation builds the same ROM cache by executing all previous requests. No precomputed cache is installed. -/
theorem backend_program {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (client : OracleComp RawCtxServerServices.BackendSpec Result)
    (ambient : A) (cache : CtxRO.QueryCache) :
    (simulateQ (RawCtxProtocolBackend.backend source writer) client).run (ambient, cache) =
      (fun result => (result.1, (ambient, result.2))) <$>
        (simulateQ hashImpl (simulateQ (backend source writer) client)).run cache := by
  simpa only [QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
    (map_run_simulateQ_eq_of_query_map_eq (hashImpl ∘ₛ backend source writer)
      (RawCtxProtocolBackend.backend source writer) (fun after => (ambient, after))
      (fun query after => (backend_step source writer query ambient after).symm) client cache).symm

/-- The forwarding program contains no selected key and uses the selected challenger's one shared public ROM. -/
noncomputable def forward : QueryImpl HashSpec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) :=
  RawCtxSelectedSealConsumer.liftSelected ∘ₛ AdaptiveCtxSharedTarget.forward

def install (before : AdaptiveCtxDynamicKnownKeys.SourceState)
    (after : AdaptiveCtxSharedTarget.SharedState) : AdaptiveCtxDynamicKnownKeys.SourceState :=
  RawCtxSelectedSealConsumer.install before
    (AdaptiveCtxSharedModes.replaceShared (before.selected, before.cache) after)

/-- The entire ordinary component state survives the prefix; only its shared cache and complete forwarded-query history change. -/
theorem forward_complete (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type} (work : OracleComp HashSpec Result)
    (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (simulateQ forward work)).run before =
      (fun result => (result.1, install before result.2)) <$>
        (simulateQ AdaptiveCtxSharedTarget.sharedImpl work).run (before.cache, before.selected.1.publicInputs) := by
  rw [forward, QueryImpl.simulateQ_compose, RawCtxSelectedSealConsumer.lifted_complete,
    AdaptiveCtxSharedModes.forward_complete]
  simp only [Functor.map_map, Prod.map_def, id_eq, install]

/-- Erasing only instrumentation after executing the prefix gives the exact original source ROM computation. -/
theorem forward_cache (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type} (work : OracleComp HashSpec Result)
    (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (simulateQ forward work)).run before =
        (simulateQ hashImpl work).run before.cache := by
  rw [forward_complete]
  simpa only [Functor.map_map, install, RawCtxSelectedSealConsumer.install,
    AdaptiveCtxSharedModes.replaceShared, Prod.map_def, id_eq] using
    AdaptiveCtxSharedTarget.cache_schedule work (before.cache, before.selected.1.publicInputs)

/-- All original native/private/public source work is executed through the ordinary component before the cut, preserving actual cache coincidences and optional results. -/
theorem backend_dynamic {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (key : CtxKey) (client : OracleComp RawCtxServerServices.BackendSpec Result)
    (ambient : A) (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, (ambient, result.2.cache))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode source.crypto key)
        (simulateQ forward (simulateQ (backend source writer) client))).run before =
      (simulateQ (RawCtxProtocolBackend.backend source writer) client).run (ambient, before.cache) := by
  rw [backend_program]
  have same := congrArg (fun work => (fun result => (result.1, (ambient, result.2))) <$> work)
    (forward_cache real decode source.crypto key (simulateQ (backend source writer) client) before)
  simpa only [Functor.map_map] using same

def backendClass (hash : Bool) : RawCtxServerServices.BackendSpec.Domain → Prop
  | .inl _ => hash = false
  | .inr (.inl (.inr (.inr (.inr (.inl _))))) => hash = true
  | _ => False

instance (hash : Bool) : DecidablePred (backendClass hash) := fun query => by
  rcases query with coin | ((request | (sealing | (opening | (bytes | frame)))) | view)
  all_goals unfold backendClass; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every private/public source hash and caller coin is charged at the exact forwarded interface. Native local primitive calls retain their separate source ledger. -/
theorem backend_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (hash : Bool)
    (client : OracleComp RawCtxServerServices.BackendSpec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (backendClass hash) bound) :
    (simulateQ (backend source writer) client).IsQueryBoundP (HashClass hash) bound := by
  apply RawCtxSourceOpen.simulate_bound (backend source writer) (backendClass hash) (HashClass hash) client bound bounded
  rintro (coin | ((request | (sealing | (opening | (bytes | frame)))) | view))
  all_goals cases hash <;> simp [backend, native, backendClass, HashClass, isQueryBoundP_query_iff]

/-- A complete original replicated finite family, including its actual live-reveal history and optional outputs, executes the prefix backend through the same challenger ROM. -/
theorem family_source {M P I D K A Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (real : Bool) (decoder : AdaptiveCtxReceive.RawDecoder) (key : CtxKey)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B)
    (ambient : A) (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, (ambient, result.2.cache))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decoder source.crypto key)
        (simulateQ forward (simulateQ (backend source writer)
          ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run state)))).run before =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxProtocolReveals.sourceImpl source writer S B sender route decode) client).run
          (state, (ambient, before.cache)) := by
  rw [backend_dynamic]
  exact RawCtxProtocolReveals.schedule_interpretation source writer S B sender route decode client state (ambient, before.cache)

end BeaconcryptCore.Computational.RawCtxSourceSharedRom

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.native_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward_cache

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_dynamic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_dynamic

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.backend_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSharedRom.family_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSharedRom.family_source
