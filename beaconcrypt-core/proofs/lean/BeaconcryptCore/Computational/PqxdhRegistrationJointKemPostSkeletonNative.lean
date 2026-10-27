import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonServices

/-!
# The native layer of the skeleton under the shared table (item 2, stage S1b, native layer)

This module relates the native layer of the grouped branch to the native layer of the services skeleton with the native services (`nativeServices`). In the grouped branch the native state holds the cache of the shared zero-key 192-byte Extract table, the KEM candidate is an argument of the private interpreters, and the analysis observers are erased after every step. In the skeleton the native state holds the game state and the marks of the hidden Server session, and every table read is an oracle query. `opRoot hmac candidate` answers these queries on a cache: a direct read at `x` reads the lazily sampled table at `x`; a hidden read at 128-byte coordinates `m` reads it at `familyInput m candidate = padFF32 ‖ m ‖ candidate` and returns the root by real Expand. These are the table-consistency lemmas of the plan: the Server root (`PqxdhServerAuthNative.romRootBytes`), the Beacon root (`PqxdhServerAuthNative.sourceRoot`) and the public HMAC (`PqxdhRegistrationJointPublicShared.publicFamily`) read the same table, and the candidate's reads are hidden reads exactly because their 192-byte input ends in the candidate (`PqxdhRegistrationJointKemOpaqueClient.bytes`, `PqxdhRefinement.build_root_key_input_abs`, `PqxdhCorrelatedExtractFamily.familyInput_source`).

The relation is state splitting (`SplitN`, `SplitC`): the erased step of the source handler from the native state `join cache state` is the step of the skeleton from `state` followed by `opRoot` at `cache`. `liftT_split` lifts it from native programs to the exposed encapsulation interface; `split_bind` composes it along programs whose continuations never read the observers. The main results are `groupedImpl_split` and `resumeImpl_split`: every step of the erased grouped native backend and of the erased private resumption interpreter splits into the corresponding step of the skeleton. These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree PqxdhRegistrationJointBeaconOpaqueFinish
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhServerAuthNative (NativeGame NativeState eraseObservers)

/-! ### The shared table at a candidate -/

section Table

variable {KemSK : Type}

/-- The table oracles answered by one lazily sampled table: a hidden read at `m` reads it at `familyInput m candidate` and applies real Expand, a direct read at `x` reads it at `x`. -/
noncomputable def opRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) :
    QueryImpl (TSpec RootOutput) (StateT HmacOracle.QueryCache ProbComp) :=
  (fun point => StateT.mk fun cache => (fun result => (PqxdhSecretInputKdf.expandRoot hmac result.1, result.2)) <$>
      (HmacOracle.randomOracle (PqxdhCorrelatedExtractFamily.familyInput point candidate)).run cache :
    QueryImpl (ValueOracle RootOutput) (StateT HmacOracle.QueryCache ProbComp)) +
  (fun point => HmacOracle.randomOracle point :
    QueryImpl PqxdhExtractRomHiddenSuffix.TableOracle (StateT HmacOracle.QueryCache ProbComp))

/-- The native state of the grouped branch represented by a table cache and a skeleton state: no family history, the game state without analysis observers. -/
def join {V : Type} (cache : HmacOracle.QueryCache) (state : SkelState KemSK V) : NativeState KemSK :=
  (⟨[], cache⟩, clean state.1)

/-- The coins of the exposed encapsulation interface. -/
def coinsEnc {α : Type} (work : ProbComp α) : OracleComp (Enc KemSK) α := simulateQ coinLift work

/-- The native programs of the grouped branch and of the skeleton split: the erased native step from `join cache state` is the skeleton step from `state` followed by the table at `cache`. -/
def SplitN {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (work : NativeGame KemSK α) (free : NGame KemSK RootOutput α) : Prop :=
  ∀ cache state, Prod.map id eraseObservers <$> work.run (join cache state) =
    (fun result : (α × SkelState KemSK RootOutput) × HmacOracle.QueryCache => (result.1.1, join result.2 result.1.2)) <$>
      (simulateQ (tableAt (fun work => work) (opRoot hmac candidate)) (free.run state)).run cache

/-- The same relation on the exposed encapsulation interface. -/
def SplitC {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (work : PqxdhRegistrationJointKemEncapsulation.Client KemSK α) (free : SClient KemSK RootOutput α) : Prop :=
  ∀ cache state, Prod.map id eraseObservers <$> work.run (join cache state) =
    (fun result : (α × SkelState KemSK RootOutput) × HmacOracle.QueryCache => (result.1.1, join result.2 result.1.2)) <$>
      (simulateQ (tableAt coinsEnc (opRoot hmac candidate)) (free.run state)).run cache

theorem eraseObservers_join {V : Type} (cache : HmacOracle.QueryCache) (state : SkelState KemSK V) :
    eraseObservers (join cache state) = join cache state := rfl

/-- Native coins on the exposed encapsulation interface are its coin channel. -/
theorem lift_native_run {α : Type} (work : NativeGame KemSK α) (state : NativeState KemSK) :
    (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK) (PqxdhRegistrationJointOpenBackend.native work)).run
        state = simulateQ (coinLift (KemSK := KemSK)) (work.run state) := by
  simp only [PqxdhRegistrationJointKemEncapsulation.lift, PqxdhRegistrationJointOpenBackend.native,
    PqxdhLiveKemBirth.coins, StateT.run]
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem gameStep_run {V α : Type} (work : StateT (GameState KemSK) ProbComp α) (state : SkelState KemSK V) :
    (gameStep work).run state = (fun result => (result.1, (result.2, state.2))) <$>
      OracleComp.liftComp (work.run (clean state.1)) (SkelSpec V) := rfl

theorem tableAt_liftComp {α : Type} (op : QueryImpl (TSpec RootOutput) (StateT HmacOracle.QueryCache ProbComp))
    (work : ProbComp α) (cache : HmacOracle.QueryCache) :
    (simulateQ (tableAt (fun work => work) op) (OracleComp.liftComp work (SkelSpec RootOutput))).run cache =
      (fun reply => (reply, cache)) <$> work :=
  tableAt_lift _ op work cache

/-- A split native program splits on the exposed encapsulation interface. -/
theorem liftT_split {α : Type} {hmac : PqxdhSecretInputKdf.HmacSha512} {candidate : MlKemSharedSecret}
    {work : NativeGame KemSK α} {free : NGame KemSK RootOutput α} (split : SplitN hmac candidate work free) :
    SplitC hmac candidate (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native work))
      (liftT free) := by
  intro cache state
  rw [lift_native_run, ← simulateQ_map, split cache state, simulateQ_map,
    push_stateless coinLift (fun work => work) coinsEnc (opRoot hmac candidate) (fun _ => rfl)]
  rfl

/-- Splitting composes along continuations that never read the observers. -/
theorem split_bind {α β : Type} {hmac : PqxdhSecretInputKdf.HmacSha512} {candidate : MlKemSharedSecret}
    {work : NativeGame KemSK α} {free : NGame KemSK RootOutput α}
    {next : α → NativeGame KemSK β} {nextFree : α → NGame KemSK RootOutput β}
    (first : SplitN hmac candidate work free) (rest : ∀ value, SplitN hmac candidate (next value) (nextFree value))
    (oblivious : ∀ value, Oblivious (next value)) :
    SplitN hmac candidate (work >>= next) (free >>= nextFree) := by
  intro cache state
  have erased : ∀ start : NativeState KemSK,
      (work.run start >>= fun result => Prod.map id eraseObservers <$> (next result.1).run result.2) =
        (Prod.map id eraseObservers <$> work.run start) >>= fun result =>
          Prod.map id eraseObservers <$> (next result.1).run result.2 := by
    intro start
    rw [bind_map_left]
    exact bind_congr fun result => oblivious result.1 result.2
  simp only [StateT.run_bind, map_bind]
  rw [erased, first cache state, bind_map_left, simulateQ_bind, StateT.run_bind, map_bind]
  exact bind_congr fun result => rest result.1.1 result.2 result.1.2

theorem split_pure {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (value : α) :
    SplitN (KemSK := KemSK) hmac candidate (pure value) (pure value) := by
  intro cache state
  simp only [StateT.run_pure, map_pure, simulateQ_pure]
  rfl

/-- A native program that acts on the game state alone splits into the same game-state computation. -/
theorem split_game {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (work : NativeGame KemSK α) (game : StateT (GameState KemSK) ProbComp α)
    (framed : ∀ family current, work.run (family, current) =
      (fun result => (result.1, (family, result.2))) <$> game.run current) :
    SplitN hmac candidate work (gameStep game) := by
  intro cache state
  rw [gameStep_run, simulateQ_map, StateT.run_map, tableAt_liftComp, join, framed]
  simp only [Functor.map_map]
  rfl

end Table

/-! ### Table-consistency lemmas for the native reads -/

section Reads

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem tableRead_eq {V : Type} (point : Pqxdh.Bytes) (state : SkelState KemSK V) :
    (tableRead point).run state =
      (fun reply => (reply, state)) <$> ((SkelSpec V).query (.inr (.inr point)) : OracleComp (SkelSpec V) _) := rfl

theorem valueRead_eq {V : Type} (point : PqxdhCorrelatedExtractFamily.Message) (state : SkelState KemSK V) :
    (valueRead point).run state =
      (fun reply => (reply, state)) <$> ((SkelSpec V).query (.inr (.inl point)) : OracleComp (SkelSpec V) _) := rfl

theorem opRoot_inr (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (point : Pqxdh.Bytes) :
    opRoot hmac candidate (.inr point) = HmacOracle.randomOracle point := rfl

theorem opRoot_inl (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (point : PqxdhCorrelatedExtractFamily.Message) (cache : HmacOracle.QueryCache) :
    (opRoot hmac candidate (.inl point)).run cache =
      (fun result => (PqxdhSecretInputKdf.expandRoot hmac result.1, result.2)) <$>
        (HmacOracle.randomOracle (PqxdhCorrelatedExtractFamily.familyInput point candidate)).run cache := rfl

/-- The table operation on a direct read is the lazily sampled table at the full byte string. -/
theorem tableRead_run (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (point : Pqxdh.Bytes)
    (state : SkelState KemSK RootOutput) (cache : HmacOracle.QueryCache) :
    (simulateQ (tableAt (fun work => work) (opRoot hmac candidate)) ((tableRead point).run state)).run cache =
      (fun result => ((result.1, state), result.2)) <$> (HmacOracle.randomOracle point).run cache := by
  rw [tableRead_eq, simulateQ_map, simulateQ_spec_query, StateT.run_map, tableAt_inr, opRoot_inr]
  rfl

/-- The table operation on a hidden read is the lazily sampled table at the candidate-suffixed input, with real Expand. -/
theorem valueRead_run (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (point : PqxdhCorrelatedExtractFamily.Message) (state : SkelState KemSK RootOutput) (cache : HmacOracle.QueryCache) :
    (simulateQ (tableAt (fun work => work) (opRoot hmac candidate)) ((valueRead point).run state)).run cache =
      (fun result => ((PqxdhSecretInputKdf.expandRoot hmac result.1, state), result.2)) <$>
        (HmacOracle.randomOracle (PqxdhCorrelatedExtractFamily.familyInput point candidate)).run cache := by
  rw [valueRead_eq, simulateQ_map, simulateQ_spec_query, StateT.run_map, tableAt_inr, opRoot_inl, Functor.map_map]

/-- A direct read followed by a pure map. -/
theorem map_tableRead_run {β : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (f : HmacBlock → β) (point : Pqxdh.Bytes) (state : SkelState KemSK RootOutput) (cache : HmacOracle.QueryCache) :
    (simulateQ (tableAt (fun work => work) (opRoot hmac candidate)) ((f <$> tableRead point).run state)).run cache =
      (fun result => ((f result.1, state), result.2)) <$> (HmacOracle.randomOracle point).run cache := by
  rw [StateT.run_map, simulateQ_map, StateT.run_map, tableRead_run, Functor.map_map]

theorem sourceRoot_run (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput)
    (state : NativeState KemSK) :
    (PqxdhServerAuthNative.sourceRoot hmac input).run state =
      (fun result => (some (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot hmac result.1)),
        ({ state.1 with cache := result.2 }, state.2))) <$>
        (HmacOracle.randomOracle (absBytes input.bytes)).run state.1.cache := rfl

/-- The Beacon tail's root callback reads the shared table at its full input; the skeleton reads it directly. -/
theorem split_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.sourceRoot hmac input)
      ((fun block => some (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot hmac block))) <$>
        tableRead (absBytes input.bytes)) := by
  intro cache state
  rw [sourceRoot_run, map_tableRead_run, Functor.map_map, Functor.map_map]
  rfl

/-- A shared-cache computation of the native layer acts on the game state alone. -/
theorem split_ctx {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.nativeCtx work) (gameStep (ctxGame work)) :=
  split_game _ _ _ _ fun _ _ => by
    simp only [ctxGame, StateT.run, Functor.map_map]
    rfl

/-- The Beacon tail callbacks of the source backend split. -/
theorem split_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (candidate : MlKemSharedSecret)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    SplitN setup.hmac candidate (PqxdhServerAuthNative.sourceBeaconTail setup codec query) (tailStep setup codec query) := by
  rcases query with query | (input | request | response)
  · exact split_ctx _ _ _
  · have same : tailStep (V := RootOutput) setup codec (.inr (.root input)) =
        (fun block => some (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac block))) <$>
          tableRead (absBytes input.bytes) := by
      simp only [tailStep, bind_pure_comp]
    rw [same]
    exact split_sourceRoot setup.hmac candidate input
  · exact split_ctx _ _ _
  · exact split_ctx _ _ _

/-- The adversary's public HMAC reads the shared table on the zero-key 192-byte slice and is the real function elsewhere. -/
theorem split_hmac (setup : Setup baseSpec KemSK) (candidate : MlKemSharedSecret) (key : HmacBlock)
    (message : Pqxdh.Bytes) :
    SplitN setup.hmac candidate (PqxdhRegistrationJointPublicShared.hmac setup key message) (hmacStep setup key message) := by
  intro cache state
  by_cases slice : key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192
  · simp only [PqxdhRegistrationJointPublicShared.hmac, hmacStep, slice, and_self, ite_true, StateT.run_bind,
      tableRead_run]
    simp only [PqxdhServerAuthNative.nativeTouch, PqxdhServerAuthNative.localState, StateT.run,
      PqxdhRegistrationJointPublicShared.publicFamily, slice, and_self, ite_true, join, pure_bind, bind_pure_comp,
      Functor.map_map]
    rfl
  · simp only [PqxdhRegistrationJointPublicShared.hmac, hmacStep, slice, ite_false]
    simp only [StateT.run, PqxdhRegistrationJointPublicShared.publicFamily, slice, ite_false, join, map_pure]
    rfl

theorem romRootBytes_run (hmac : PqxdhSecretInputKdf.HmacSha512) (point : PqxdhJointDhExtractFamily.Message)
    (bytes : Pqxdh.Bytes) (state : NativeState KemSK) :
    (PqxdhServerAuthNative.romRootBytes (A := GameState KemSK) hmac point bytes).run state =
      (fun result : HmacBlock × HmacOracle.QueryCache => (PqxdhSecretInputKdf.expandRoot hmac result.1,
        ((⟨state.1.history ++ [.derive point (some result.1),
            .publicHmac result.1 PqxdhSecretInputKdf.rootExpandInput (hmac.eval result.1 PqxdhSecretInputKdf.rootExpandInput)],
          result.2⟩ : PqxdhJointDhExtractFamily.State), state.2))) <$>
        (HmacOracle.randomOracle bytes).run state.1.cache := rfl

/-- A Server root read on a candidate-suffixed input is a hidden read. -/
theorem split_romRoot_value (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (point : PqxdhJointDhExtractFamily.Message) (coordinates : PqxdhCorrelatedExtractFamily.Message)
    (bytes : Pqxdh.Bytes) (same : bytes = PqxdhCorrelatedExtractFamily.familyInput coordinates candidate) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.romRootBytes hmac point bytes)
      (valueRead coordinates) := by
  intro cache state
  rw [romRootBytes_run, valueRead_run, same, Functor.map_map, Functor.map_map]
  rfl

/-- Any other Server root read is a direct read. -/
theorem split_romRoot_table (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (point : PqxdhJointDhExtractFamily.Message) (bytes : Pqxdh.Bytes) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.romRootBytes hmac point bytes)
      ((fun block => PqxdhSecretInputKdf.expandRoot hmac block) <$> tableRead bytes) := by
  intro cache state
  rw [romRootBytes_run, map_tableRead_run, Functor.map_map, Functor.map_map]
  rfl

theorem split_touch (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (touch : Touch) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.nativeTouch touch) (pure ()) := by
  intro cache state
  rfl

theorem split_mark (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (touch : Touch)
    (index : Nat) (value : RootOutput) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.nativeTouch touch) (mark index value) := by
  intro cache state
  rfl

theorem split_consume (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (rid : beaconcrypt_core.pqxdh.RegistrationId) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.nativeConsume rid) (consumeGame rid) := by
  intro cache state
  rfl

theorem split_set (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (game : GameState KemSK) :
    SplitN hmac candidate (PqxdhServerAuthNative.nativeSet game) (setGame game) := by
  intro cache state
  rfl

theorem split_publish (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (slot : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) :
    SplitN (KemSK := KemSK) hmac candidate
      (PqxdhServerAuthNative.nativeModify fun current => { current with pending := Function.update current.pending slot (some token) })
      (modifyGame fun current => { current with pending := Function.update current.pending slot (some token) }) := by
  intro cache state
  rfl

/-- The private native tail of the Server's resumption splits: its root request on the challenge marker is a hidden read, on a known decapsulation result a direct read. -/
theorem split_resumeTail (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (candidate : MlKemSharedSecret)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    SplitN hmac candidate (PqxdhRegistrationJointKemOpaqueTail.impl hmac index candidate query)
      (resumeTail hmac index (nativeServices setup codec checks) query) := by
  rcases query with (input | aux) | mutation
  · obtain ⟨verified, ephemeral, ciphertext, converted, first, second, third, fourth, shared⟩ := input
    cases shared with
    | challenge =>
        refine split_bind (split_romRoot_value hmac candidate _ _ _ ?_) (fun root =>
          split_bind (split_mark hmac candidate _ index root) (fun _ => split_pure hmac candidate root)
            (fun _ => oblivious_pure _)) (fun root => oblivious_bind (oblivious_touch _) fun _ => oblivious_pure _)
        exact (PqxdhCorrelatedExtractFamily.familyInput_source _ candidate).symm
    | known secret =>
        refine split_bind (split_romRoot_table hmac candidate _ _) (fun root =>
          split_bind (split_touch hmac candidate _) (fun _ => split_pure hmac candidate root)
            (fun _ => oblivious_pure _)) (fun root => oblivious_bind (oblivious_touch _) fun _ => oblivious_pure _)
  · cases aux with
    | eraseShared => exact split_pure hmac candidate ()
    | eraseInput => exact split_pure hmac candidate ()
    | consume rid => exact split_consume hmac candidate rid
  · cases mutation with
    | install game => exact split_set hmac candidate game
    | publish slot token => exact split_publish hmac candidate slot token

/-- The native services' response tail is the source's for every session. -/
theorem buildService_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (marks : Marks RootOutput) (session : Nat) :
    buildService setup codec checks (nativeServices setup codec checks) marks session =
      nativeResponse setup codec checks := by
  rcases marks with _ | ⟨slot, value⟩
  · rfl
  · by_cases same : slot = session
    · simp only [buildService, same, ite_true]
      rfl
    · simp only [buildService, same, ite_false]

/-- The Server build splits, with the native services. -/
theorem split_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : MlKemSharedSecret) (session : Nat) (payload : Option Pqxdh.Bytes) :
    SplitN setup.hmac candidate (PqxdhServerAuthNative.nativeBuild setup codec checks session payload)
      (buildStep setup codec checks (nativeServices setup codec checks) session payload) := by
  intro cache state
  change Prod.map id eraseObservers <$>
      PqxdhServerAuthNative.nativeBuild setup codec checks session payload (join cache state) =
    (fun result => (result.1.1, join result.2 result.1.2)) <$>
      (simulateQ (tableAt (fun work => work) (opRoot setup.hmac candidate))
        (buildStep (V := RootOutput) setup codec checks (nativeServices setup codec checks) session payload state)).run
          cache
  simp only [PqxdhServerAuthNative.nativeBuild, PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeGet,
    PqxdhServerAuthNative.localState, pure_bind, join, clean, buildStep]
  rcases found : state.1.pending session with _ | token
  · simp only [PqxdhServerAuthNative.native_pure_run, map_pure, simulateQ_pure, StateT.run_pure]
    rfl
  · simp only [PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeCoins,
      PqxdhServerAuthNative.nativeSet, buildService_native, bind_pure_comp,
      simulateQ_map, StateT.run_map, tableAt_liftComp, Functor.map_map, PqxdhServerAuthNative.native_map_run,
      PqxdhServerAuthNative.localState, map_pure, nativeResponse]
    rfl

/-- The source's continuation after a Beacon root, on the prepared state with the opaque handle, is the native continuation of `PqxdhPhase2DhRootConsumer` on the embedded prepared state: both read only the response and the cleared metadata. -/
theorem afterRoot_embed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (pending : Pending Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    simulateQ (tailNative setup codec) (PqxdhBeaconPhase2Shared.afterRoot decode pending root) =
      simulateQ (beaconNative setup codec) (PqxdhPhase2DhRootConsumer.afterRoot decode (embed pending) root) := by
  have calls : PqxdhBeaconPhase2Shared.TailCalls (fun _ => zeroWord) (beaconNative setup codec) (tailNative setup codec) :=
    ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have auxiliary (query : PqxdhBeaconPhase2Publication.AuxQuery Response) :
      simulateQ (beaconNative setup codec) (PqxdhBeaconPhase2Publication.nativeTailAdapter (.inr query)) =
        beaconNative setup codec (.inr query) :=
    simulateQ_spec_query (beaconNative setup codec) (.inr query)
  unfold PqxdhPhase2DhRootConsumer.afterRoot PqxdhBeaconPhase2Publication.afterRoot
    PqxdhBeaconPhase2Publication.initialRun PqxdhBeaconPhase2Shared.afterRoot
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, auxiliary]
  refine bind_congr fun response => bind_congr fun raw => ?_
  cases raw with
  | none => simp only [simulateQ_pure]
  | some raw =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [PqxdhBeaconPhase2Bounds.native_raw_lift,
        PqxdhBeaconPhase2Shared.raw_realization (fun _ => zeroWord) _ _ calls]
      rfl

/-- The native answer to a grouped finish request, as one native program. -/
noncomputable def groupNativeN (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (candidate : MlKemSharedSecret) (pending : Pending Response) :
    NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged) := do
  let root ← markedRoot setup.hmac candidate pending.root
  match root with
  | none => pure none
  | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (tailNative setup codec)
      (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root))

theorem groupNative_lift (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (candidate : MlKemSharedSecret) (pending : Pending Response) :
    groupNative setup codec candidate pending =
      PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
        (groupNativeN setup codec candidate pending)) := by
  apply StateT.ext
  intro state
  rw [lift_native_run, groupNative, groupNativeN, StateT.run_bind, StateT.run_bind, lift_native_run, simulateQ_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | root, after⟩
  · rfl
  · exact lift_native_run _ _

/-- The grouped Beacon finish splits, with the native services: on the challenge marker the root is a hidden read at the root input's coordinates, on a known decapsulation result a direct read at the root input. -/
theorem split_group (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : MlKemSharedSecret) (pending : Pending Response) :
    SplitN setup.hmac candidate (groupNativeN setup codec candidate pending)
      (groupStep setup codec (nativeServices setup codec checks) pending) := by
  intro cache state
  obtain ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ := pending
  by_cases nonzero : Pqxdh.dhNonZero (absBytes dh1, absBytes dh2, absBytes dh3, absBytes dh4)
  · obtain ⟨input, built, -⟩ := (build_root_key_input_abs
      (PqxdhBeaconPhase2Shared.concreteSecrets (interpret candidate) ⟨dh1, dh2, dh3, dh4, shared⟩)).1 nonzero
    have bytes := PqxdhPhase2InputBytes.root_input _ input built
    have sside : groupNativeN (KemSK := KemSK) setup codec candidate
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ =
        PqxdhServerAuthNative.sourceRoot setup.hmac input >>= fun root => match root with
          | none => pure none
          | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (tailNative setup codec)
              (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead
                ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ root)) := by
      simp only [groupNativeN, markedRoot, built]
    rw [sside, StateT.run_bind, sourceRoot_run, bind_map_left, map_bind]
    cases shared with
    | challenge =>
        have tside : groupStep (KemSK := KemSK) setup codec (nativeServices setup codec checks)
            ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .challenge⟩⟩ =
            valueRead (message dh1 dh2 dh3 dh4) >>= fun value =>
              gameStep (ctxGame ((nativeHidden setup codec checks value).hiddenAfter
                (embed ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .challenge⟩⟩))) := by
          simp only [groupStep, nonzero, ite_true]
          rfl
        have same : absBytes input.bytes = PqxdhCorrelatedExtractFamily.familyInput (message dh1 dh2 dh3 dh4) candidate := by
          rw [bytes, message, PqxdhCorrelatedExtractFamily.familyInput_source]
          simp only [PqxdhBeaconPhase2Shared.concreteSecrets, interpret, PqxdhPhase2DecapsulationRouting.materialize,
            PqxdhPhase2InputBytes.word_rootArray]
        rw [tside, StateT.run_bind, simulateQ_bind, StateT.run_bind, valueRead_run, bind_map_left, map_bind]
        change (do
            let result ← (HmacOracle.randomOracle (absBytes input.bytes)).run cache
            _) = _
        rw [same]
        refine bind_congr fun result => ?_
        rw [nativeHidden]
        dsimp only
        rw [← afterRoot_embed setup codec codec.frameRead]
        exact split_ctx setup.hmac candidate _ result.2 state
    | known secret =>
        have tside : groupStep (KemSK := KemSK) setup codec (nativeServices setup codec checks)
            ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ =
            tableRead (PqxdhHiddenRoot.hiddenRootIKM (PqxdhPhase2InputBytes.coordinates dh1 dh2 dh3 dh4) secret) >>=
              fun block => gameStep (ctxGame (simulateQ (tailNative setup codec)
                (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead
                  ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩
                  (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac block))))) := by
          simp only [groupStep, nonzero, ite_true]
        have same : absBytes input.bytes = PqxdhHiddenRoot.hiddenRootIKM
            (PqxdhPhase2InputBytes.coordinates dh1 dh2 dh3 dh4) secret := by
          rw [bytes]
          simp only [PqxdhBeaconPhase2Shared.concreteSecrets, interpret, PqxdhPhase2DecapsulationRouting.materialize,
            PqxdhPhase2InputBytes.word_rootArray]
        rw [tside, StateT.run_bind, simulateQ_bind, StateT.run_bind, tableRead_run, bind_map_left, map_bind]
        change (do
            let result ← (HmacOracle.randomOracle (absBytes input.bytes)).run cache
            _) = _
        rw [same]
        exact bind_congr fun result => split_ctx setup.hmac candidate _ result.2 state
  · have rejected := (build_root_key_input_abs
      (PqxdhBeaconPhase2Shared.concreteSecrets (interpret candidate) ⟨dh1, dh2, dh3, dh4, shared⟩)).2 nonzero
    have sside : groupNativeN (KemSK := KemSK) setup codec candidate
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ = pure none := by
      simp only [groupNativeN, markedRoot, rejected, pure_bind]
    have tside : groupStep (KemSK := KemSK) setup codec (nativeServices setup codec checks)
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ = pure none := by
      simp only [groupStep, nonzero, ite_false]
    rw [sside, tside]
    exact split_pure setup.hmac candidate none cache state

/-- The Server's logged root of a raw accept is a direct read at its actual root input. -/
theorem split_loggedRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.loggedRoot hmac index input original)
      (PqxdhSecretInputKdf.expandRoot hmac <$> tableRead (absBytes original.root_key_input.bytes)) := by
  have tside : (PqxdhSecretInputKdf.expandRoot hmac <$> tableRead (KemSK := KemSK) (V := RootOutput)
      (absBytes original.root_key_input.bytes)) =
      (PqxdhSecretInputKdf.expandRoot hmac <$> tableRead (absBytes original.root_key_input.bytes)) >>= fun root =>
        (pure () : NGame KemSK RootOutput Unit) >>= fun _ => pure root := by
    simp only [pure_bind, bind_pure]
  rw [tside]
  exact split_bind (split_romRoot_table hmac candidate _ _) (fun root =>
    split_bind (split_touch hmac candidate _) (fun _ => split_pure hmac candidate root) (fun _ => oblivious_pure _))
    (fun _ => oblivious_bind (oblivious_touch _) fun _ => oblivious_pure _)

/-- The Server's core acceptance and root of a raw accept split. -/
theorem split_client (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    SplitN (KemSK := KemSK) hmac candidate (PqxdhServerAuthNative.nativeClient hmac index control binding input)
      (clientStep hmac control binding input) := by
  unfold PqxdhServerAuthNative.nativeClient clientStep
  cases PqxdhServerRelatedRootInput.accept control binding input with
  | ok result =>
      cases result with
      | Err error => exact split_pure hmac candidate _
      | Ok pair =>
          exact split_bind (split_loggedRoot hmac candidate index input _) (fun root =>
            split_bind (split_consume hmac candidate _) (fun _ => split_pure hmac candidate _)
              (fun _ => oblivious_pure _))
            (fun _ => oblivious_bind (oblivious_consume _) fun _ => oblivious_pure _)
  | fail error => exact split_pure hmac candidate _
  | div => exact split_pure hmac candidate _

/-- The Server's accept tail splits. -/
theorem split_acceptTail (setup : Setup baseSpec KemSK) (candidate : MlKemSharedSecret) (publicIdentity : PublicIdentity)
    (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    SplitN setup.hmac candidate (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected)
      (acceptTail setup publicIdentity before collected) := by
  have publishOblivious : ∀ returned : RustM (Option PqxdhServerRelatedRootConsumer.Returned),
      Oblivious (KemSK := KemSK) (match returned with
        | .ok (some token) => do
            PqxdhServerAuthNative.nativeModify fun current =>
              { current with pending := Function.update current.pending before.sessions (some token) }
            pure (some before.sessions)
        | _ => pure none) := by
    intro returned
    split
    · exact oblivious_bind (oblivious_publish _ _) fun _ => oblivious_pure _
    · exact oblivious_pure _
  unfold PqxdhRegistrationJointServerAccept.tail acceptTail
  refine split_bind (split_set setup.hmac candidate _) (fun _ => ?_) (fun _ => ?_)
  · rcases collected with ⟨_ | input, consumed⟩
    · exact split_pure setup.hmac candidate none
    · refine split_bind (split_client setup.hmac candidate _ _ _ input) (fun returned => ?_) publishOblivious
      cases returned with
      | ok value =>
          cases value with
          | none => exact split_pure setup.hmac candidate none
          | some token =>
              exact split_bind (split_publish setup.hmac candidate _ _) (fun _ => split_pure setup.hmac candidate _)
                (fun _ => oblivious_pure _)
      | fail error => exact split_pure setup.hmac candidate none
      | div => exact split_pure setup.hmac candidate none
  · rcases collected with ⟨_ | input, consumed⟩
    · exact oblivious_pure _
    · exact oblivious_bind (oblivious_client _ _ _ _ _) publishOblivious

/-- Forwarded requests of the exposed encapsulation interface leave the table untouched. -/
theorem tableAt_encLift {α : Type} (op : QueryImpl (TSpec RootOutput) (StateT HmacOracle.QueryCache ProbComp))
    (work : OracleComp (Enc KemSK) α) (cache : HmacOracle.QueryCache) :
    (simulateQ (tableAt coinsEnc op) (simulateQ (encLift (V := RootOutput)) work)).run cache =
      (fun reply => (reply, cache)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have handler : (tableAt coinsEnc op ∘ₛ encLift (KemSK := KemSK) (V := RootOutput)) = keep (Enc KemSK) _ := by
    funext query
    simp only [QueryImpl.apply_compose, encLift, simulateQ_spec_query]
    rfl
  rw [handler, keep_run]

/-- A forwarded request of the exposed encapsulation interface splits. -/
theorem split_forward (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (query : (Enc KemSK).Domain) :
    SplitC hmac candidate
      (fun state => (fun reply => (reply, state)) <$> ((Enc KemSK).query query : OracleComp (Enc KemSK) _))
      (fun state => (fun reply => (reply, state)) <$> encLift (V := RootOutput) query) := by
  intro cache state
  change Prod.map id eraseObservers <$> ((fun reply => (reply, join cache state)) <$>
      ((Enc KemSK).query query : OracleComp (Enc KemSK) _)) =
    (fun result => (result.1.1, join result.2 result.1.2)) <$>
      (simulateQ (tableAt coinsEnc (opRoot hmac candidate))
        ((fun reply => (reply, state)) <$> encLift (V := RootOutput) query)).run cache
  rw [simulateQ_map, StateT.run_map, encLift, simulateQ_spec_query, tableAt_inl]
  simp only [Functor.map_map]
  rfl

/-- The Server's raw accept with its encapsulation exposed splits. -/
theorem split_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (raw : Pqxdh.Bytes) :
    SplitC setup.hmac candidate
      (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw)
      (acceptStep setup codec checks identityIndex publicIdentity raw) := by
  intro cache state
  have getStep : ∀ start : NativeState KemSK, (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
      (PqxdhRegistrationJointOpenBackend.native PqxdhServerAuthNative.nativeGet)).run start = pure (start.2, start) :=
    fun start => by
      rw [lift_native_run]
      rfl
  have stepS : (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
      (join cache state) =
      ((fun result => (result, join cache state)) <$>
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
          (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.1.server.consumed) >>=
        fun result => (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
          (PqxdhRegistrationJointServerAccept.tail setup publicIdentity (clean state.1) result.1))).run result.2 := by
    simp only [PqxdhRegistrationJointKemEncapsulation.accept, StateT.run_bind, getStep, pure_bind]
    rfl
  have stepT : (acceptStep (V := RootOutput) setup codec checks identityIndex publicIdentity raw).run state =
      ((fun result => (result, state)) <$> simulateQ (encLift (V := RootOutput))
        ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
          (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.1.server.consumed)) >>=
        fun result => (liftT (acceptTail setup publicIdentity (clean state.1) result.1)).run result.2 := rfl
  rw [stepS, stepT, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map, tableAt_encLift, Functor.map_map,
    bind_map_left, bind_map_left, map_bind, map_bind]
  exact bind_congr fun collected =>
    liftT_split (split_acceptTail setup candidate publicIdentity (clean state.1) collected) cache state

end Reads

/-! ### Every native-layer step splits -/

section Handlers

open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every step of the grouped native backend splits into the native layer of the skeleton with the native services. -/
theorem groupedImpl_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret)
    (query : (GSpec KemSK Response).Domain) :
    SplitC setup.hmac candidate (groupedImpl setup codec checks identityIndex publicIdentity candidate query)
      (skelImpl setup codec checks identityIndex publicIdentity (nativeServices setup codec checks) query) := by
  rcases query with ((pool | tail) | shared) | pending
  · have source : groupedImpl setup codec checks identityIndex publicIdentity candidate (.inl (.inl (.inl pool))) =
        fun state => (fun reply => (reply, state)) <$> ((Enc KemSK).query (.inl pool) : OracleComp (Enc KemSK) _) := by
      funext state
      simp only [groupedImpl]
      exact simulateQ_map _ _ _
    rw [source]
    exact split_forward setup.hmac candidate (.inl pool)
  · exact liftT_split (split_tail setup codec candidate tail)
  · cases shared with
    | accept raw => exact split_accept setup codec checks identityIndex publicIdentity candidate raw
    | build session payload => exact liftT_split (split_build setup codec checks candidate session payload)
    | hmac key message => exact liftT_split (split_hmac setup candidate key message)
    | hash bytes =>
        exact liftT_split (split_game setup.hmac candidate _ (hashGame bytes) fun _ _ => by
          simp only [PqxdhServerAuthNative.nativeHash, hashGame, StateT.run, Functor.map_map])
    | reveal keyId =>
        exact liftT_split (split_game setup.hmac candidate _ (fun game => pure (revealKernel keyId game, game))
          fun _ _ => by simp only [PqxdhServerAuthNative.localState, StateT.run, map_pure])
  · change SplitC setup.hmac candidate (groupNative setup codec candidate pending) _
    rw [groupNative_lift]
    exact liftT_split (split_group setup codec checks candidate pending)

/-- Every step of the Server's private resumption interpreter splits into the native layer of the skeleton with the native services. -/
theorem resumeImpl_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (candidate : MlKemSharedSecret)
    (query : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain) :
    SplitC setup.hmac candidate (liftImpl clientNative setup index candidate forwardClient query)
      (resumeImpl setup.hmac index (nativeServices setup codec checks) query) := by
  rcases query with query | query
  · exact split_forward setup.hmac candidate query
  · exact liftT_split (split_resumeTail setup.hmac index candidate setup codec checks query)

end Handlers


end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.eraseObservers_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.eraseObservers_join

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.lift_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.lift_native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.gameStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.gameStep_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_liftComp' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_liftComp

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.liftT_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.liftT_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableRead_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableRead_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.valueRead_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.valueRead_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opRoot_inr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opRoot_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opRoot_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opRoot_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableRead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableRead_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.valueRead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.valueRead_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.map_tableRead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.map_tableRead_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.sourceRoot_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.sourceRoot_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_sourceRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.romRootBytes_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.romRootBytes_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_romRoot_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_romRoot_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_romRoot_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_romRoot_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_touch

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_mark

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_consume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_publish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_resumeTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_resumeTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.buildService_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.buildService_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.afterRoot_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.afterRoot_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupNative_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupNative_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_group

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_loggedRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_loggedRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_acceptTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_encLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_encLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedImpl_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedImpl_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resumeImpl_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resumeImpl_split
