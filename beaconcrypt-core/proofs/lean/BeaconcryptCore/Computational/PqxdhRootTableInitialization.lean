import BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds
import BeaconcryptCore.Refinement.ProtocolComposition

/-!
The same consistent uniform-root family feeds repeated actual extracted Server/Beacon initializations. Each source 64-byte response uses the supplied fixed HKDF function and the existing 64/76 prefix contract. Complete query/run equalities retain actual kernel replies, all private initialization history and the root table; owner and orientation labels do not select independent roots. Public fixed-HKDF projections remain real and share the source function.

The initializer interface, kernel replies and retained root history are private protocol or analysis context, not a new network service. Arbitrary prior caches/histories are allowed by the execution equations; the alias invariant is separately derived from actual empty-state execution. The source initializer runs on every call, including root-cache hits. Caller coins cost U, root misses cost at most 32*I, and logical initial 64-byte/public 76-byte source evaluations are bounded by I+P. Deterministic HKDF/byte/cache/kernel work is not free.

This is a structural factorization of the uniform-family continuation. It proves neither independent chains per ownership event nor native role creation/registration installation, owner-label uniqueness, network declassification, evolving input secrecy or global protocol security. The constructed response instantiates the supplied functional source; native library/ABI/error/runtime correspondence remains its existing explicit contract.
-/

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open PqxdhRefinement BeaconcryptCore.Refinement.ProtocolComposition
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhRootTableInitialization
open PqxdhSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhJointKdf PqxdhJointKdfGame

/-- The supplied fixed source is evaluated at the exact requested 64-byte initialization width. -/
def initialResponse (c : Pqxdh.Crypto) (request : ratchet.SymmetricRatchetKdfRequest) :
    pqxdh.concrete.InitialRatchetKdfResponse :=
  ⟨⟨(c.hkdf (absBytes request.input) (absBytes request.info) 64).map concreteByte,
    by simp [c.hkdf_length]⟩⟩

theorem initialResponse_bytes (c : Pqxdh.Crypto) (request : ratchet.SymmetricRatchetKdfRequest) :
    absBytes (initialResponse c request).bytes = c.hkdf (absBytes request.input) (absBytes request.info) 64 := by
  simp [initialResponse, absBytes, List.map_map, Function.comp_def]

theorem initialResponse_law (c : Pqxdh.Crypto) : InitialKdfLaw c (initialResponse c) := by
  intro root
  rw [initialResponse_bytes]
  simp only [absBytes_ratchetSymmetricInfo]

/-- This conversion preserves the entire retained root, not a hash or new sample. -/
def rootArray (root : RootOutput) : Std.Array Std.U8 32#usize :=
  ⟨root.toList.map concreteByte, by simp⟩

theorem rootArray_bytes (root : RootOutput) : absBytes (rootArray root) = root.toList := by
  simp [rootArray, absBytes, List.map_map, Function.comp_def]

/-- Both native roles execute their extracted start/request/resume path with this same fixed source. -/
def initialKernelRun (source : FixedHkdfSha512NoSaltSource) (beacon : Bool) (root : RootOutput) :
    RustM ratchet.concrete.ConcreteRatchetKernel :=
  if beacon then initializeBeacon (rootArray root) (initialResponse source.crypto)
  else initializeServer (rootArray root) (initialResponse source.crypto)

/-- The actual 64-byte response shares its prefix with the same 76-byte ratchet stream. -/
theorem initialResponse_prefix (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    absBytes (initialResponse source.crypto ⟨rootArray root, ratchet.SYM_RATCHET_INFO⟩).bytes =
      (streamBytes (productionStream source.crypto (ratchetAddress root.toList))).take 64 := by
  rw [initialResponse_bytes, rootArray_bytes, absBytes_ratchetSymmetricInfo]
  exact source.prefixConsistent.ratchetPrefix root.toList

/-- Exact extracted kernels retain source byte origins and the complete zero-counter/empty-skipped refinement. -/
theorem initialize_refines {AD PT CT : Type} (source : FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beacon : Bool) (root : RootOutput) :
    ∃ kernel, initialKernelRun source beacon root = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain
        (if beacon then (Pqxdh.rootChains source.crypto root.toList).2 else (Pqxdh.rootChains source.crypto root.toList).1) ∧
      ChainBytesRefines kernel.refined.receive_chain
        (if beacon then (Pqxdh.rootChains source.crypto root.toList).1 else (Pqxdh.rootChains source.crypto root.toList).2) ∧
      ratchet.concrete.KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  cases beacon
  · simpa only [initialKernelRun, Bool.false_eq_true, ite_false, rootArray_bytes] using
      initializeServer_refines source.crypto cr (rootArray root) (initialResponse source.crypto) (initialResponse_law _)
  · simpa only [initialKernelRun, ite_true, rootArray_bytes] using
      initializeBeacon_refines source.crypto cr (rootArray root) (initialResponse source.crypto) (initialResponse_law _)

/-- Ownership and orientation are source bookkeeping; only the unchanged coordinates select a root-table entry. -/
structure InitRequest where
  owner : Nat
  beacon : Bool
  coordinates : Message
  deriving DecidableEq

abbrev InitOracle := InitRequest →ₒ RustM ratchet.concrete.ConcreteRatchetKernel
abbrev InitSpec := unifSpec + (InitOracle + JointKdfViewSpec)
/-- This retained root history is private analysis state, never a reply to the client. -/
abbrev InitHistory := List (InitRequest × RootOutput)
abbrev State := InitHistory × RootOracle.QueryCache

/-- Each original initialization executes the extracted role again, even when its root was already cached. -/
def initCompile (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl InitSpec (StateT InitHistory (OracleComp RootSpec)) := fun request history =>
  match request with
  | .inl coin => do
      let answer ← RootSpec.query (.inl coin)
      pure (answer, history)
  | .inr (.inl request) => do
      let root : RootOutput ← RootSpec.query (.inr request.coordinates)
      pure (initialKernelRun source request.beacon root, history ++ [(request, root)])
  | .inr (.inr request) =>
      pure (request.project (productionStream source.crypto request.address), history)

/-- A direct consistent root dictionary, independent of the initialization compiler. -/
noncomputable def sourceImpl (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl InitSpec (StateT State ProbComp) := fun request state =>
  match request with
  | .inl coin => do
      let answer ← unifSpec.query coin
      pure (answer, state)
  | .inr (.inl request) =>
      match state.2 request.coordinates with
      | some root => pure (initialKernelRun source request.beacon root,
          (state.1 ++ [(request, root)], state.2))
      | none => do
          let root ← $ᵗ RootOutput
          pure (initialKernelRun source request.beacon root,
            (state.1 ++ [(request, root)], state.2.cacheQuery request.coordinates root))
  | .inr (.inr request) =>
      pure (request.project (productionStream source.crypto request.address), state)

set_option backward.isDefEq.respectTransparency false in
/-- The complete interpreted query preserves the actual kernel reply, every prior initialization and the same private root cache. -/
theorem source_query (source : FixedHkdfSha512NoSaltSource) :
    ((uniformImpl.mapStateTBase (initCompile source)).flattenStateT) = sourceImpl source := by
  funext request state
  rcases request with coin | (request | publicQuery)
  · rfl
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$> ((do
        let root : RootOutput ← uniformImpl (.inr request.coordinates)
        pure (initialKernelRun source request.beacon root, state.1 ++ [(request, root)])).run state.2) = _
    rw [StateT.run_bind]
    cases hit : state.2 request.coordinates with
    | none =>
      simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none _ hit, StateT.run_pure, sourceImpl, hit,
        bind_pure_comp, Functor.map_map]
      rfl
    | some root =>
      simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
        QueryImpl.withCaching_run_some _ hit, StateT.run_pure, sourceImpl, hit,
        pure_bind, map_pure]
  · rfl

/-- Every adaptive continuation retains its complete result, initialization history and the same private root table. -/
theorem source_complete {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (history : InitHistory) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl ((simulateQ (initCompile source) client).run history)).run cache =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl source) client).run (history, cache) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, source_query]

/-- Existing coordinates reuse their exact root without another draw, while rerunning the original role initializer. -/
theorem source_cached (source : FixedHkdfSha512NoSaltSource) (request : InitRequest)
    (history : InitHistory) (cache : RootOracle.QueryCache) (root : RootOutput)
    (hit : cache request.coordinates = some root) :
    (sourceImpl source (.inr (.inl request))).run (history, cache) =
      pure (initialKernelRun source request.beacon root, (history ++ [(request, root)], cache)) := by
  simp only [sourceImpl, StateT.run, hit]

/-- A new coordinate samples one root and retains its full source initialization and cache entry. -/
theorem source_fresh (source : FixedHkdfSha512NoSaltSource) (request : InitRequest)
    (history : InitHistory) (cache : RootOracle.QueryCache)
    (miss : cache request.coordinates = none) :
    (sourceImpl source (.inr (.inl request))).run (history, cache) = (do
      let root ← $ᵗ RootOutput
      pure (initialKernelRun source request.beacon root,
        (history ++ [(request, root)], cache.cacheQuery request.coordinates root))) := by
  simp only [sourceImpl, StateT.run, miss]

/-- Full arbitrary client output after private initialization is a direct observation of the published uniform-root game. -/
theorem source_uniform_game {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) :
    (simulateQ (sourceImpl source) client).run' ([], ∅) =
      (simulateQ uniformImpl ((simulateQ (initCompile source) client).run' [])).run' ∅ := by
  have complete := congrArg (fun program => (fun result => result.1.1) <$> program)
    (source_complete source client [] ∅)
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using complete.symm

set_option backward.isDefEq.respectTransparency false in
/-- Already installed roots survive every later call, including another owner and arbitrary public projections. -/
theorem source_preserves_cached (source : FixedHkdfSha512NoSaltSource)
    (request : InitSpec.Domain) (state : State) (address : Message) (root : RootOutput)
    (hit : state.2 address = some root) (result : InitSpec.Range request × State)
    (supported : result ∈ support ((sourceImpl source request).run state)) :
    result.2.2 address = some root := by
  rcases request with coin | (request | publicQuery)
  · simp only [sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact hit
  · cases stored : state.2 request.coordinates with
    | some old =>
      simp only [sourceImpl, StateT.run, stored, mem_support_pure_iff] at supported
      subst result
      exact hit
    | none =>
      simp only [sourceImpl, StateT.run, stored, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨sampled, _, rfl⟩ := supported
      have different : address ≠ request.coordinates := by
        intro same
        rw [same, stored] at hit
        contradiction
      simpa only [QueryCache.cacheQuery_of_ne _ _ different] using hit
  · simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact hit

/-- Cache persistence holds through every supported full continuation, with no restriction on later owners, coordinates or public calls. -/
theorem source_run_preserves_cached {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (state : State) (address : Message) (root : RootOutput)
    (hit : state.2 address = some root) (result : Result × State)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run state)) :
    result.2.2 address = some root := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact hit
  | query_bind request next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, continued⟩ := supported
      exact ih step.1 step.2 (source_preserves_cached source request state address root hit step stepSupported)
        result continued

set_option backward.isDefEq.respectTransparency false in
/-- Every reached initialization retains its actual root, original request, complete kernel reply and installed cache entry. -/
theorem source_initial_result (source : FixedHkdfSha512NoSaltSource) (request : InitRequest)
    (state : State) (result : RustM ratchet.concrete.ConcreteRatchetKernel × State)
    (supported : result ∈ support ((sourceImpl source (.inr (.inl request))).run state)) :
    ∃ root, result.1 = initialKernelRun source request.beacon root ∧
      result.2.1 = state.1 ++ [(request, root)] ∧ result.2.2 request.coordinates = some root := by
  cases stored : state.2 request.coordinates with
  | some root =>
      simp only [sourceImpl, StateT.run, stored, mem_support_pure_iff] at supported
      subst result
      exact ⟨root, rfl, rfl, stored⟩
  | none =>
      simp only [sourceImpl, StateT.run, stored, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨root, _, rfl⟩ := supported
      exact ⟨root, rfl, rfl, QueryCache.cacheQuery_self _ _ _⟩

/-- All roots appearing in the private ownership history remain the exact values of the same coordinate cache. -/
def Aligned (state : State) : Prop :=
  ∀ entry ∈ state.1, state.2 entry.1.coordinates = some entry.2

set_option backward.isDefEq.respectTransparency false in
theorem source_aligned (source : FixedHkdfSha512NoSaltSource) (request : InitSpec.Domain)
    (state : State) (aligned : Aligned state) (result : InitSpec.Range request × State)
    (supported : result ∈ support ((sourceImpl source request).run state)) : Aligned result.2 := by
  rcases request with coin | (request | publicQuery)
  · simp only [sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact aligned
  · obtain ⟨root, _, history, installed⟩ := source_initial_result source request state result supported
    intro entry member
    rw [history, List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · exact source_preserves_cached source (.inr (.inl request)) state entry.1.coordinates entry.2
        (aligned entry previous) result supported
    · exact installed
  · simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact aligned

/-- The complete reachable history retains coordinate aliases through arbitrary adaptive initialization and public calls. -/
theorem source_run_aligned {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (state : State) (aligned : Aligned state)
    (result : Result × State)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run state)) : Aligned result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact aligned
  | query_bind request next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, continued⟩ := supported
      exact ih step.1 step.2 (source_aligned source request state aligned step stepSupported) result continued

/-- Repeated coordinate ownership events have the same retained root, regardless of owner or role labels. -/
theorem history_same_coordinates (state : State) (aligned : Aligned state)
    (first second : InitRequest × RootOutput) (firstMem : first ∈ state.1) (secondMem : second ∈ state.1)
    (same : first.1.coordinates = second.1.coordinates) : first.2 = second.2 := by
  have left := aligned first firstMem
  have right := aligned second secondMem
  rw [same] at left
  exact Option.some.inj (left.symm.trans right)

/-- The history property is derived from the actual empty-state execution, not imposed as a caller alias premise. -/
theorem source_history_same_coordinates {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (result : Result × State)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run ([], ∅)))
    (first second : InitRequest × RootOutput) (firstMem : first ∈ result.2.1) (secondMem : second ∈ result.2.1)
    (same : first.1.coordinates = second.1.coordinates) : first.2 = second.2 := by
  have aligned := source_run_aligned source client ([], ∅) (by simp [Aligned]) result supported
  exact history_same_coordinates result.2 aligned first second firstMem secondMem same

/-- Equal retained roots keep identical source initialization for the same orientation, even at distinct table addresses. -/
theorem equal_roots_kernel (source : FixedHkdfSha512NoSaltSource) (beacon : Bool)
    (first second : RootOutput) (same : first = second) :
    initialKernelRun source beacon first = initialKernelRun source beacon second := by
  rw [same]

/-- Actual initialization and the first two projections of the same 76-byte source stream give identical chain origins. -/
theorem initialize_stream_refines {AD PT CT : Type} (source : FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beacon : Bool) (root : RootOutput) :
    let chains := initialProjection (productionStream source.crypto (ratchetAddress root.toList))
    ∃ kernel, initialKernelRun source beacon root = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain (if beacon then chains.2 else chains.1) ∧
      ChainBytesRefines kernel.refined.receive_chain (if beacon then chains.1 else chains.2) ∧
      ratchet.concrete.KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  simpa only [rootChains_eq_initialProjection source.crypto source.prefixConsistent] using
    initialize_refines source cr beacon root

/-- Both extracted roles at a shared root have complementary complete initial kernels and identical opposite material streams. -/
theorem complementary_kernels {AD PT CT : Type} (source : FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (root : RootOutput) :
    ∃ beaconOrigin serverOrigin beacon server,
      initialKernelRun source true root = ok beacon ∧ initialKernelRun source false root = ok server ∧
      ConcreteSession cr beaconOrigin serverOrigin beacon server ∧
      beacon.refined.send_chain = server.refined.receive_chain ∧
      beacon.refined.receive_chain = server.refined.send_chain ∧
      ∀ n, Ratchet.msgKeyAt cr beacon.refined.send_chain n = Ratchet.msgKeyAt cr server.refined.receive_chain n ∧
        Ratchet.msgKeyAt cr server.refined.send_chain n = Ratchet.msgKeyAt cr beacon.refined.receive_chain n := by
  simpa only [initialKernelRun, ite_true, Bool.false_eq_true, ite_false] using
    initialize_establishes_concrete_session cr (rootArray root) (initialResponse source.crypto)

/-- Source classes track the actual forwarded coin/root request; public fixed-HKDF calls remain separate deterministic work. -/
def Forwarded (predicate : RootSpec.Domain → Prop) : InitSpec.Domain → Prop
  | .inl coin => predicate (.inl coin)
  | .inr (.inl request) => predicate (.inr request.coordinates)
  | .inr (.inr _) => False

instance (predicate : RootSpec.Domain → Prop) [DecidablePred predicate] : DecidablePred (Forwarded predicate)
  | .inl coin => inferInstanceAs (Decidable (predicate (.inl coin)))
  | .inr (.inl request) => inferInstanceAs (Decidable (predicate (.inr request.coordinates)))
  | .inr (.inr _) => inferInstanceAs (Decidable False)

set_option backward.isDefEq.respectTransparency false in
theorem compile_step (source : FixedHkdfSha512NoSaltSource)
    (predicate : RootSpec.Domain → Prop) [DecidablePred predicate]
    (request : InitSpec.Domain) (history : InitHistory) :
    ((initCompile source request).run history).IsQueryBoundP predicate
      (if Forwarded predicate request then 1 else 0) := by
  rcases request with coin | (request | publicQuery)
  · by_cases counted : predicate (.inl coin)
    all_goals simp [initCompile, StateT.run, Forwarded, counted]
  · by_cases counted : predicate (.inr request.coordinates)
    all_goals simp [initCompile, StateT.run, Forwarded, counted]
  · trivial

noncomputable local instance : OracleSpec.UniformAnswerMeasure RootOracle :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

/-- Every original adaptive class cap transfers to the root compiler through its complete stateful continuation. -/
theorem compile_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (predicate : RootSpec.Domain → Prop) [DecidablePred predicate]
    (client : OracleComp InitSpec Result) (q : Nat)
    (bounded : client.IsQueryBoundP (Forwarded predicate) q) (history : InitHistory) :
    ((simulateQ (initCompile source) client).run history).IsQueryBoundP predicate q := by
  exact bounded.simulateQ_run_of_step
    (fun request selected history => by simpa only [selected, ite_true] using compile_step source predicate request history)
    (fun request omitted history => by simpa only [omitted, ite_false] using compile_step source predicate request history) history

/-- Actual root misses cost 32 draws; every caller coin remains charged once, and public fixed-HKDF evaluations add no sampling. -/
theorem source_uniform_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (qCoins qInitial : Nat)
    (coins : client.IsQueryBoundP (Forwarded PqxdhCorrelatedExpandQueryBounds.IsCoin) qCoins)
    (initial : client.IsQueryBoundP (Forwarded IsRoot) qInitial) (state : State) :
    ((simulateQ (sourceImpl source) client).run state).IsTotalQueryBound (qCoins + 32 * qInitial) := by
  have bounded := PqxdhCorrelatedExpandQueryBounds.uniform_run_uniform
    ((simulateQ (initCompile source) client).run state.1) qCoins qInitial
    (compile_bound source _ client qCoins coins state.1) (compile_bound source _ client qInitial initial state.1) state.2
  rw [source_complete] at bounded
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded

set_option backward.isDefEq.respectTransparency false in
/-- The history counts every actual initializer call, including a cached-root replay by the same owner. -/
theorem source_initial_count (source : FixedHkdfSha512NoSaltSource) (request : InitSpec.Domain)
    (state : State) (result : InitSpec.Range request × State)
    (supported : result ∈ support ((sourceImpl source request).run state)) :
    result.2.1.length = state.1.length + (if Forwarded IsRoot request then 1 else 0) := by
  rcases request with coin | (request | publicQuery)
  · simp only [sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    simp [Forwarded, IsRoot]
  · obtain ⟨root, _, history, _⟩ := source_initial_result source request state result supported
    simp only [history, List.length_append, List.length_singleton, Forwarded, IsRoot, ite_true]
  · simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [Forwarded]

/-- Every initialization consumes one of the original adaptive source slots, irrespective of whether its root cache lookup hits. -/
theorem source_run_initial_count {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp InitSpec Result) (qInitial : Nat)
    (bounded : client.IsQueryBoundP (Forwarded IsRoot) qInitial) (state : State) (result : Result × State)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run state)) :
    result.2.1.length ≤ state.1.length + qInitial := by
  induction client using OracleComp.inductionOn generalizing qInitial state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      change state.1.length ≤ state.1.length + qInitial
      omega
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, continued⟩ := supported
      have later := ih step.1 _ (bounded.2 step.1) step.2 result continued
      have count := source_initial_count source request state step stepSupported
      have positive := bounded.1
      by_cases selected : Forwarded IsRoot request
      · simp only [selected, ite_true] at later count
        have := positive.resolve_left (not_not.mpr selected)
        omega
      · simp only [selected, ite_false] at later count
        omega

/-- The source's actual reached initializer returns a valid complete native kernel with the same cached root and private ownership history. -/
theorem source_initial_kernel {AD PT CT : Type} (source : FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (request : InitRequest) (state : State) (result : RustM ratchet.concrete.ConcreteRatchetKernel × State)
    (supported : result ∈ support ((sourceImpl source (.inr (.inl request))).run state)) :
    ∃ root kernel, result.1 = ok kernel ∧ result.2.1 = state.1 ++ [(request, root)] ∧
      result.2.2 request.coordinates = some root ∧
      ChainBytesRefines kernel.refined.send_chain
        (if request.beacon then (Pqxdh.rootChains source.crypto root.toList).2 else (Pqxdh.rootChains source.crypto root.toList).1) ∧
      ChainBytesRefines kernel.refined.receive_chain
        (if request.beacon then (Pqxdh.rootChains source.crypto root.toList).1 else (Pqxdh.rootChains source.crypto root.toList).2) ∧
      ratchet.concrete.KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  obtain ⟨root, reply, history, cached⟩ := source_initial_result source request state result supported
  obtain ⟨kernel, actual, send, receive, refined⟩ := initialize_refines source cr request.beacon root
  exact ⟨root, kernel, reply.trans actual, history, cached, send, receive, refined⟩

/-- Public calls use the actual fixed source stream and preserve the entire initialization/root state. -/
theorem source_public (source : FixedHkdfSha512NoSaltSource) (request : JointKdfViewQuery) (state : State) :
    (sourceImpl source (.inr (.inr request))).run state =
      pure (request.project (productionStream source.crypto request.address), state) := by
  rfl

/-- Each public projection executes one real complete-stream HKDF evaluation. -/
def IsPublic : InitSpec.Domain → Prop
  | .inr (.inr _) => True
  | _ => False
instance : DecidablePred IsPublic
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inr (.inr _) => inferInstanceAs (Decidable True)

/-- Initial64 and public76 source evaluations have a combined logical call bound, including every repeated request. -/
theorem source_hkdf_calls {Result : Type} (client : OracleComp InitSpec Result) (qInitial qPublic : Nat)
    (initial : client.IsQueryBoundP (Forwarded IsRoot) qInitial)
    (publicCap : client.IsQueryBoundP IsPublic qPublic) :
    client.IsQueryBoundP (fun request => Forwarded IsRoot request ∨ IsPublic request) (qInitial + qPublic) := by
  induction client using OracleComp.inductionOn generalizing qInitial qPublic with
  | pure value => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at initial publicCap ⊢
      rcases request with coin | (request | publicQuery)
      · simp only [Forwarded, IsRoot, IsPublic, false_or, not_false_eq_true, ite_false] at initial publicCap ⊢
        exact ⟨Or.inl True.intro, fun answer => ih answer _ _ (initial.2 answer) (publicCap.2 answer)⟩
      · simp only [
          ite_eq_left (show Forwarded IsRoot (.inr (.inl request)) from True.intro),
          ite_eq_right (show ¬ IsPublic (.inr (.inl request)) from id),
          ite_eq_left (show Forwarded IsRoot (.inr (.inl request)) ∨
            IsPublic (.inr (.inl request)) from Or.inl True.intro)] at initial publicCap ⊢
        simp only [Forwarded, IsRoot, IsPublic, true_or, not_true_eq_false, false_or] at initial publicCap ⊢
        refine ⟨by omega, fun answer => ?_⟩
        exact (ih answer _ _ (initial.2 answer) (publicCap.2 answer)).mono (by omega)
      · simp only [
          ite_eq_right (show ¬ Forwarded IsRoot (.inr (.inr publicQuery)) from id),
          ite_eq_left (show IsPublic (.inr (.inr publicQuery)) from True.intro),
          ite_eq_left (show Forwarded IsRoot (.inr (.inr publicQuery)) ∨
            IsPublic (.inr (.inr publicQuery)) from Or.inr True.intro)] at initial publicCap ⊢
        simp only [Forwarded, IsPublic, false_or, not_true_eq_false] at initial publicCap ⊢
        refine ⟨by omega, fun answer => ?_⟩
        exact (ih answer _ _ (initial.2 answer) (publicCap.2 answer)).mono (by omega)

end BeaconcryptCore.Computational.PqxdhRootTableInitialization

/-! Persistent kernel-dependency audit for every statement in this module. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_law

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.rootArray_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.rootArray_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialResponse_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialize_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialize_refines

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_uniform_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_uniform_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_preserves_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_preserves_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_preserves_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_preserves_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_aligned

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_aligned

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.history_same_coordinates' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.history_same_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_history_same_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_history_same_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.equal_roots_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.equal_roots_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialize_stream_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.initialize_stream_refines

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.complementary_kernels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.complementary_kernels

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.compile_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.compile_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.compile_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_uniform_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_initial_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_run_initial_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_initial_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_public

/-- info: 'BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_hkdf_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRootTableInitialization.source_hkdf_calls
