-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes

/-!
# Record-lift CTX privacy link: one privacy hybrid step as the three-mode challenger (items 4 and 5, stage S4)

**The reduction.** `reduction target modes` is the key-free private interpreter of one step of the privacy hybrids. It is the reduction of `PqxdhRecordLiftCtxLink` with one change: every hidden coordinate other than the selected one becomes a known call of `PqxdhRecordLiftCtxPrivModes` in its own mode (`routeKeyed`), so the other coordinates may be in random mode as well as in real or replay mode. Public coins and public BLAKE2b queries are forwarded through the reserved known slot (`coinForward`, `hashForward`), the selected coordinate's openings and seals go to the challenger, and caller-known native records run with their commitment hashes forwarded. The reduction receives no key of the selected coordinate. It reuses the explicit-key worlds `ctxRunWith`, the counter-erased CTX interpreter, the slot code `slotOf` and the state projection `linkProj` of `PqxdhRecordLiftCtxLink`.

**The link.** `linked_step` and `linked_schedule` show, for every service and every state and without a reachability or mode premise, that the reduction run against the challenger's source state (`PqxdhRecordLiftCtxPrivModes.sourceImpl` with the world's sampler `uniformBytes`, so that a random known call is exactly `PqxdhRecordLiftIdeal.randomImpl`) realizes the counter-erased CTX world with the selected key supplied externally and the selected coordinate in the challenger's mode (`selectedModesM`). `link` concludes: the challenger's game in mode `sel` against the key-free client `linkClient` is the CTX world in which the selected coordinate's key is a fresh uniform key in mode `sel`, every other hidden coordinate keeping its table key and its mode.

**Contracts.** No theorem of this module has an assumption or contract hypothesis or uses a contract: no proof uses a field of the primitive record or a security game (fields reached only inside definitions are structural). New Claude work, adapted from Claude's `PqxdhRecordLiftCtxLink`; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftCtxProtocol (Bare bareInterpreter bareSeeds erasePrivate)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-- The selected coordinate in the challenger's mode `sel`; every other coordinate keeps its mode. -/
def selectedModesM (target : Label n) (sel : KeyMode) (modes : Label n → KeyMode) (label : Label n) : KeyMode :=
  if label = target then sel else modes label

/-! ### The key-free reduction of one privacy hybrid step -/

open PqxdhRecordLiftCtxPrivModes (KnownCall uniformBytes)

/-- A public request forwarded through the reserved known slot in real mode (coins and public hashes are mode-independent). -/
def publicCall (decode : RawDecoder) (request : ReceiveSpec.Domain) : KnownCall :=
  ⟨⟨0, publicKey, decode, request⟩, .real⟩

/-- Forward a uniform coin through the reserved known slot. -/
def coinForward (decode : RawDecoder) : QueryImpl unifSpec (OracleComp PqxdhRecordLiftCtxPrivModes.Spec) :=
  fun query => PqxdhRecordLiftCtxPrivModes.Spec.query (.inr (publicCall decode (.inl (.inl query))))

/-- Forward a public BLAKE2b query through the reserved known slot. -/
def hashForward (decode : RawDecoder) : QueryImpl CtxRO (OracleComp PqxdhRecordLiftCtxPrivModes.Spec) :=
  fun query => PqxdhRecordLiftCtxPrivModes.Spec.query (.inr (publicCall decode (.inl (.inr (.inl query)))))

/-- Route a keyed request: the selected coordinate to the challenger; every other coordinate to a known call at its own slot with its table key and in its own mode (real, replay or random). -/
noncomputable def routeKeyed (target : Label n) (modes : Label n → KeyMode) (decode : RawDecoder)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) :
    QueryImpl (KeyedSpec n) (OracleComp PqxdhRecordLiftCtxPrivModes.Spec) := fun query =>
  if query.1 = target then PqxdhRecordLiftCtxPrivModes.Spec.query (.inl query.2)
  else PqxdhRecordLiftCtxPrivModes.Spec.query
    (.inr ⟨⟨slotOf query.1, (materialAt table query.1).1, decode, query.2⟩, modes query.1⟩)

/-- The key-free reduction of one hybrid step. It holds the counter-erased chain-world state (its cache field is unused: the shared cache is the challenger's); public coins and hashes are forwarded through the reserved slot, the selected coordinate's records go to the challenger, and every other hidden coordinate's records are known calls with their table keys. No selected key is an argument. -/
noncomputable def reduction (target : Label n) (modes : Label n → KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (Bare n) (OracleComp PqxdhRecordLiftCtxPrivModes.Spec))
  | .allocate slot => fun state => do
      let result ← simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead))
        ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
      pure ((), { state with seeds := result.2 })
  | .coin coin => fun state => do
      let reply ← coinForward (RawCtxUniversalDecoder.decoder codec.frameRead) coin
      pure (reply, state)
  | .hash bytes => fun state => do
      let reply ← hashForward (RawCtxUniversalDecoder.decoder codec.frameRead) ((), bytes)
      pure (reply, state)
  | .charge kind => fun state => pure ((), { state with
      effects := Function.update state.effects kind (state.effects kind + 1) })
  | .lookup coordinate => fun state => do
      let result ← simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead))
        ((PqxdhRecordLiftCtxOracle.bareLookup setup.source (bareSeeds state) (fun _ => true) coordinate).run state.chain)
      pure ((), { state with chain := result.2 })
  | .opening pending => fun state => do
      let reply ← simulateQ (routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) state.chain)
        (hiddenOpening (bareSeeds state) state.chain pending)
      pure (reply, state)
  | .sealing pending => fun state => do
      let result ← simulateQ (routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) state.chain)
        ((hiddenSealing codec.frameWrite state.chain id pending).run state.pending)
      pure (result.1, { state with pending := result.2 })
  | .knownSend kernel context => fun state => do
      let result ← simulateQ (hashForward (RawCtxUniversalDecoder.decoder codec.frameRead))
        ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
          (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
            (RawCtxSourceSend.send kernel context)))).run state.pending)
      pure (result.1, { state with pending := result.2 })
  | .knownReceive kernel target' context => fun state => do
      let result ← simulateQ (hashForward (RawCtxUniversalDecoder.decoder codec.frameRead))
        ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
          (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive kernel target' context)))).run state.pending)
      pure (result.1, { state with pending := result.2 })
  | .publish tag => fun state => pure ((), { state with
      produced := state.produced ++ state.pending.map (fun frame => (tag, frame)), pending := [] })

/-- A forwarded coin leaves the whole challenger source state unchanged. -/
theorem coinForward_step (sel : KeyMode) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : unifSpec.Domain) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key) (coinForward decode' query)).run state =
      (fun reply => (reply, state)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [coinForward]
  change (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((AdaptiveCtxSharedModes.localImpl true decode' crypto publicKey (.inl (.inl query))).run (state.others 0))).run
        state.cache
    pure (result.1.1, { state with others := Function.update state.others 0 result.1.2, cache := result.2 })) = _
  simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl, StateT.run,
    bind_pure_comp, Functor.map_map, simulateQ_map, simulateQ_spec_query, stateT_map_apply]
  change (fun result => _) <$> ((fun reply => (reply, state.cache)) <$> (unifSpec.query query : ProbComp _)) = _
  simp only [Functor.map_map, Function.update_eq_self]

/-- Every forwarded probabilistic computation leaves the whole challenger source state unchanged and returns the computation's own law. -/
theorem coinForward_program {Result : Type} (sel : KeyMode) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (work : ProbComp Result) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key)
      (simulateQ (coinForward decode') work)).run state = (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure result => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, coinForward_step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result

/-- Simulating a forwarded public hash is one known call at the reserved slot. -/
theorem simulateQ_hashForward {σ : Type} (impl : QueryImpl PqxdhRecordLiftCtxPrivModes.Spec (StateT σ ProbComp))
    (decode : RawDecoder) (query : CtxRO.Domain) :
    simulateQ impl (hashForward decode query) = impl (.inr (publicCall decode (.inl (.inr (.inl query))))) := by
  unfold hashForward
  exact simulateQ_spec_query impl _

/-- A forwarded public hash is the shared random oracle on the challenger's cache; only the reserved slot's history changes. -/
theorem hashForward_step (sel : KeyMode) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxRO.Domain) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key) (hashForward decode' query)).run state =
      (fun result => (result.1, { state with
        others := Function.update state.others 0 (publicEntry (state.others 0) query), cache := result.2 })) <$>
        (ctxRandomOracle query).run state.cache := by
  rw [simulateQ_hashForward]
  change (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((AdaptiveCtxSharedModes.localImpl true decode' crypto publicKey (.inl (.inr (.inl query)))).run
        (state.others 0))).run state.cache
    pure (result.1.1, { state with others := Function.update state.others 0 result.1.2, cache := result.2 })) = _
  simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl, StateT.run,
    bind_pure_comp, Functor.map_map, simulateQ_map, simulateQ_spec_query, stateT_map_apply,
    AdaptiveCtxSharedHash.hashImpl, QueryImpl.add_apply_inr]
  rfl

/-- Every forwarded public-hash program is the shared random oracle on the challenger's cache and leaves every hidden coordinate's CTX state unchanged. -/
theorem hashForward_program {Result : Type} (target : Label n) (sel : KeyMode) (decode decode' : RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxKey) (work : OracleComp CtxRO Result)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, result.2.cache, keysOf target result.2)) <$>
      (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key)
        (simulateQ (hashForward decode') work)).run state =
      (fun result => (result.1, result.2, keysOf target state)) <$> (simulateQ ctxRandomOracle work).run state.cache := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hashForward_step, bind_map_left, map_bind]
      apply bind_congr
      intro result
      rw [ih]
      simp only [keysOf_reserved]

/-- One routed keyed request under the challenger's source state is the counter-erased keyed request with the selected coordinate's key supplied externally and its mode set by the challenger. -/
theorem routeKeyed_step (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode) (decode : RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxKey) (red : Bare n) (query : (KeyedSpec n).Domain)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id (fun after : AdaptiveCtxDynamicKnownKeys.SourceState =>
        (({ red with cache := after.cache } : Bare n), keysOf target after)) <$>
      (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key)
        (routeKeyed target modes decode red.chain query)).run state =
      (bareKeyed (selectedKey target key) (selectedModesM target sel modes) decode crypto query).run
        (({ red with cache := state.cache } : Bare n), keysOf target state) := by
  rcases query with ⟨label, request⟩
  by_cases same : label = target
  · subst same
    have routed : simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key)
        (routeKeyed label modes decode red.chain (label, request)) =
        PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key (.inl request) := by
      simp only [routeKeyed, ite_true]
      exact simulateQ_spec_query _ _
    have source : (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key (.inl request)).run state =
        (fun result => (result.1.1, { state with selected := result.1.2, cache := result.2 })) <$>
          (simulateQ AdaptiveCtxSharedHash.hashImpl
            ((keyImpl decode crypto key sel request).run state.selected)).run state.cache := by
      simp only [PqxdhRecordLiftCtxPrivModes.sourceImpl, StateT.run, bind_pure_comp]
    rw [routed, source, Functor.map_map]
    have entry : keysOf label state label = state.selected := by simp [keysOf]
    simp only [bareKeyed, selectedKey, selectedModesM, ite_true, StateT.run, bind_pure_comp, entry]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, keysOf_selected]
  · have routed : simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key)
        (routeKeyed target modes decode red.chain (label, request)) =
        PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key
          (.inr ⟨⟨slotOf label, (materialAt red.chain label).1, decode, request⟩, modes label⟩) := by
      simp only [routeKeyed, same, ite_false]
      exact simulateQ_spec_query _ _
    have source : (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode crypto key
          (.inr ⟨⟨slotOf label, (materialAt red.chain label).1, decode, request⟩, modes label⟩)).run
          state =
        (fun result => (result.1.1,
            { state with others := Function.update state.others (slotOf label) result.1.2, cache := result.2 })) <$>
          (simulateQ AdaptiveCtxSharedHash.hashImpl
            ((keyImpl decode crypto (materialAt red.chain label).1 (modes label)
              request).run (state.others (slotOf label)))).run state.cache := by
      simp only [PqxdhRecordLiftCtxPrivModes.sourceImpl, StateT.run, bind_pure_comp,
        PqxdhRecordLiftCtxPrivModes.knownLocal_uniform]
    rw [routed, source, Functor.map_map]
    have entry : keysOf target state label = state.others (slotOf label) := by simp [keysOf, same]
    simp only [bareKeyed, selectedKey, selectedModesM, same, ite_false, StateT.run, bind_pure_comp, entry]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, keysOf_other target label same]

/-- Every caller-known native program with its public hashes forwarded through the reserved slot is the counter-erased native program on the challenger's cache, and leaves every hidden coordinate's CTX state unchanged. -/
theorem known_link {Result : Type} (target : Label n) (sel : KeyMode) (decode decode' : RawDecoder)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (key : CtxKey) (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (red : Bare n)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, ({ red with cache := result.2.cache, pending := result.1.2 } : Bare n),
        keysOf target result.2)) <$>
      (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel decode setup.source.crypto key)
        (simulateQ (hashForward decode') ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
          work).run red.pending))).run state =
      (fun result => (result.1, ({ red with cache := result.2.1, pending := result.2.2 } : Bare n), keysOf target state)) <$>
        (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work).run
          (state.cache, red.pending) := by
  have forwarded := congrArg (fun program => (fun result : (Result × PqxdhRecordLiftLoggedAdapters.Frames) ×
      CtxRO.QueryCache × (Label n → KeyEntry) =>
        (result.1.1, ({ red with cache := result.2.1, pending := result.1.2 } : Bare n), result.2.2)) <$> program)
    (hashForward_program target sel decode decode' setup.source.crypto key
      ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite) work).run red.pending) state)
  simp only [Functor.map_map] at forwarded
  refine forwarded.trans ?_
  rw [PqxdhRecordLiftCtxProtocol.knownRom_program]
  change _ = _ <$> (PqxdhRecordLiftLoggedAdapters.swapResult <$> (simulateQ ctxRandomOracle
    ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite) work).run red.pending)).run
      state.cache)
  rw [Functor.map_map]
  rfl

/-- The reduction composed with the challenger's source state. -/
noncomputable def linked (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n)
      (StateT (Bare n × AdaptiveCtxDynamicKnownKeys.SourceState) ProbComp) :=
  ((PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    key).mapStateTBase (reduction target modes setup codec)).flattenStateT

/-- One service of the reduction composed with the challenger's source state. -/
theorem linked_run (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (red : Bare n) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (linked target modes sel key setup codec query).run (red, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key) ((reduction target modes setup codec query).run red)).run state := rfl

/-- Every service of the reduction, run against the challenger's source state, realizes the counter-erased CTX service with the selected coordinate's key supplied externally and its mode set by the challenger. No reachability premise is used. -/
theorem linked_step (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id (linkProj target) <$> (linked target modes sel key setup codec query).run state =
      (bareCtxInterpreter (selectedKey target key) (selectedModesM target sel modes) id setup codec query).run
        (linkProj target state) := by
  rcases state with ⟨red, source⟩
  rw [linked_run, Functor.map_map]
  cases query with
  | allocate slot =>
      have reduced : (reduction target modes setup codec (.allocate slot)).run red =
          (fun result => ((), ({ red with seeds := result.2 } : Bare n))) <$>
            simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead))
              ((PqxdhRecordLiftLazyTable.impl slot).run red.seeds) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, coinForward_program, Functor.map_map, Functor.map_map]
      simp only [bareCtxInterpreter, bareInterpreter, linkProj, StateT.run, bind_pure_comp, Functor.map_map]
      rfl
  | coin coin =>
      have reduced : (reduction target modes setup codec (.coin coin)).run red =
          (fun reply => (reply, red)) <$> coinForward (RawCtxUniversalDecoder.decoder codec.frameRead) coin := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, coinForward_step, Functor.map_map, Functor.map_map]
      simp only [bareCtxInterpreter, bareInterpreter, linkProj, StateT.run, bind_pure_comp, Functor.map_map]
      rfl
  | hash bytes =>
      have reduced : (reduction target modes setup codec (.hash bytes)).run red =
          (fun reply => (reply, red)) <$> hashForward (RawCtxUniversalDecoder.decoder codec.frameRead) ((), bytes) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, hashForward_step, Functor.map_map, Functor.map_map]
      simp only [bareCtxInterpreter, bareInterpreter, linkProj, StateT.run, bind_pure_comp, Functor.map_map,
        Prod.map_def, id_eq, keysOf_reserved]
  | charge kind => rfl
  | lookup coordinate =>
      have reduced : (reduction target modes setup codec (.lookup coordinate)).run red =
          (fun result => ((), ({ red with chain := result.2 } : Bare n))) <$>
            simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead))
              ((PqxdhRecordLiftCtxOracle.bareLookup setup.source (bareSeeds red) (fun _ => true) coordinate).run
                red.chain) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, coinForward_program, Functor.map_map, Functor.map_map]
      simp only [bareCtxInterpreter, bareInterpreter, linkProj, StateT.run, bind_pure_comp, Functor.map_map]
      rfl
  | opening pending =>
      have inner := map_run_simulateQ_eq_of_query_map_eq
        (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key ∘ₛ
          routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
        (bareKeyed (selectedKey target key) (selectedModesM target sel modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (fun after : AdaptiveCtxDynamicKnownKeys.SourceState => (({ red with cache := after.cache } : Bare n),
          keysOf target after))
        (fun request after => by
          simpa only [QueryImpl.compose] using routeKeyed_step target modes sel
            (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key red request after)
        (hiddenOpening (bareSeeds red) red.chain pending) source
      rw [QueryImpl.simulateQ_compose] at inner
      have reduced : (reduction target modes setup codec (.opening pending)).run red =
          (fun reply => (reply, red)) <$>
            simulateQ (routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
              (hiddenOpening (bareSeeds red) red.chain pending) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, Functor.map_map]
      refine Eq.trans ?_ inner
      rfl
  | sealing pending =>
      have inner := map_run_simulateQ_eq_of_query_map_eq
        (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key ∘ₛ
          routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
        (bareKeyed (selectedKey target key) (selectedModesM target sel modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (fun after : AdaptiveCtxDynamicKnownKeys.SourceState => (({ red with cache := after.cache } : Bare n),
          keysOf target after))
        (fun request after => by
          simpa only [QueryImpl.compose] using routeKeyed_step target modes sel
            (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key red request after)
        ((hiddenSealing codec.frameWrite red.chain id pending).run red.pending) source
      rw [QueryImpl.simulateQ_compose] at inner
      have reduced : (reduction target modes setup codec (.sealing pending)).run red =
          (fun result => (result.1, ({ red with pending := result.2 } : Bare n))) <$>
            simulateQ (routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
              ((hiddenSealing codec.frameWrite red.chain id pending).run red.pending) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, Functor.map_map]
      change _ = (do
        let result ← (simulateQ (bareKeyed (selectedKey target key) (selectedModesM target sel modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
            ((hiddenSealing codec.frameWrite red.chain id pending).run red.pending)).run
              (({ red with cache := source.cache } : Bare n), keysOf target source)
        pure (result.1.1, ({ result.2.1 with pending := result.1.2 }, result.2.2)))
      rw [← inner]
      simp only [bind_pure_comp, Functor.map_map]
      rfl
  | knownSend kernel context =>
      have fact := known_link target sel (RawCtxUniversalDecoder.decoder codec.frameRead)
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup codec key
        (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send kernel context))) red source
      have reduced : (reduction target modes setup codec (.knownSend kernel context)).run red =
          (fun result => (result.1, ({ red with pending := result.2 } : Bare n))) <$>
            simulateQ (hashForward (RawCtxUniversalDecoder.decoder codec.frameRead))
              ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
                (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
                  (RawCtxSourceSend.send kernel context)))).run red.pending) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, Functor.map_map]
      change _ = (fun result => (result.1, (result.2, keysOf target source))) <$>
        (PqxdhRecordLiftCtxProtocol.bareNative (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative
          (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))).run
            ({ red with cache := source.cache } : Bare n)
      simp only [PqxdhRecordLiftCtxProtocol.bareNative, PqxdhRecordLiftWorldCompiler.sendNative,
        QueryImpl.simulateQ_compose, StateT.run, bind_pure_comp, Functor.map_map]
      refine Eq.trans ?_ (fact.trans ?_)
      · rfl
      · rfl
  | knownReceive kernel target' context =>
      have fact := known_link target sel (RawCtxUniversalDecoder.decoder codec.frameRead)
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup codec key
        (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive kernel target' context))) red source
      have reduced : (reduction target modes setup codec (.knownReceive kernel target' context)).run red =
          (fun result => (result.1, ({ red with pending := result.2 } : Bare n))) <$>
            simulateQ (hashForward (RawCtxUniversalDecoder.decoder codec.frameRead))
              ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
                (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
                  (RawCtxOwnerOracle.receive kernel target' context)))).run red.pending) := by
        simp only [reduction, StateT.run, bind_pure_comp]
      rw [reduced, simulateQ_map, StateT.run_map, Functor.map_map]
      change _ = (fun result => (result.1, (result.2, keysOf target source))) <$>
        (PqxdhRecordLiftCtxProtocol.bareNative (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative
          (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
          (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target' context)))).run
            ({ red with cache := source.cache } : Bare n)
      simp only [PqxdhRecordLiftCtxProtocol.bareNative, PqxdhRecordLiftWorldCompiler.receiveNative,
        QueryImpl.simulateQ_compose, StateT.run, bind_pure_comp, Functor.map_map]
      refine Eq.trans ?_ (fact.trans ?_)
      · rfl
      · rfl
  | publish tag => rfl

/-- Every complete adaptive program of the reduction, run against the challenger's source state, realizes the counter-erased CTX world with the selected key supplied externally. -/
theorem linked_schedule {Result : Type} (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (red : Bare n)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, linkProj target (result.1.2, result.2))) <$>
      (simulateQ (PqxdhRecordLiftCtxPrivModes.sourceImpl uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key) ((simulateQ (reduction target modes setup codec) client).run red)).run state =
      (simulateQ (bareCtxInterpreter (selectedKey target key) (selectedModesM target sel modes) id setup codec)
        client).run (linkProj target (red, state)) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  exact map_run_simulateQ_eq_of_query_map_eq (linked target modes sel key setup codec)
    (bareCtxInterpreter (selectedKey target key) (selectedModesM target sel modes) id setup codec) (linkProj target)
    (linked_step target modes sel key setup codec) client (red, state)

/-- The key-free reduction client of one hybrid step: the whole program under `reduction`, then the decision on the permitted view with its coins forwarded through the reserved slot. -/
noncomputable def linkClient (target : Label n) (modes : Label n → KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (decision : View n E X → ProbComp Bool) :
    OracleComp PqxdhRecordLiftCtxPrivModes.Spec Bool := do
  let result ← (simulateQ (reduction target modes setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
  simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead)) (decision (viewOf result.1 result.2.produced))

/-- **Link of one privacy hybrid step.** The challenger's game in mode `sel`, with the world's sampler, against the key-free reduction client is the CTX world in which the selected coordinate's key is a fresh uniform key held by the challenger, in mode `sel`, and every other hidden coordinate keeps its table key and its mode, random mode included. -/
theorem link (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (decision : View n E X → ProbComp Bool) :
    Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (linkClient target modes setup codec route env serverKid bounds mode adversary decision) =
      (do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWith (selectedKey target key) (selectedModesM target sel modes) id setup codec route env
          serverKid bounds mode adversary
        decision (ctxView result)) := by
  simp only [PqxdhRecordLiftCtxPrivModes.sourceGame, map_bind]
  apply bind_congr
  intro key
  simp only [linkClient, simulateQ_bind, StateT.run_bind, map_bind, coinForward_program, Functor.map_map]
  have schedule := linked_schedule target modes sel key setup codec
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    (erasePrivate PqxdhRecordLiftProtocol.initialPrivate) AdaptiveCtxDynamicKnownKeys.initialSource
  have world := ctxInterpreterWith_schedule (selectedKey target key) (selectedModesM target sel modes) id setup codec
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    CtxPrivate.initial
  rw [linkProj_initial, ← world] at schedule
  have mapped := congrArg (fun work => work >>= fun result =>
    decision (viewOf result.1 result.2.1.produced)) schedule
  simp only [bind_map_left] at mapped
  refine Eq.trans ?_ (mapped.trans ?_)
  · simp only [id_map']
    rfl
  · rfl

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.coinForward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.coinForward_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.coinForward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.coinForward_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.simulateQ_hashForward' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.simulateQ_hashForward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.hashForward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.hashForward_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.hashForward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.hashForward_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.routeKeyed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.routeKeyed_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.known_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.known_link

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.linked_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivLink.link
