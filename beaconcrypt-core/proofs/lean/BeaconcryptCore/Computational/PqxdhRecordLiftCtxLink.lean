-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid

/-!
# Record-lift CTX link: one hybrid step as the one-key CTX challenger (items 4 and 5, stage S4, X1)

**Explicit-key worlds.** `ctxRunWith keyOf` is `PqxdhRecordLiftIdeal.ctxRun` with the key of each hidden coordinate given by `keyOf` as a function of the chain table; with the table key it is `ctxRun` itself (`ctxRunWith_tableKey`). `selectedKey target key` supplies the selected coordinate's key externally and keeps every other coordinate's table key; `selectedModes target real modes` puts the selected coordinate in real (`true`) or replay (`false`) mode. The counter-erased CTX world `bareCtxInterpreter` drops only the native and uniform analysis counters; every explicit-key world erases to it, service by service and for every state (`ctxInterpreterWith_erase`, `ctxInterpreterWith_schedule`).

**The reduction.** `reduction target modes` is the key-free private interpreter of one hybrid step against the ordinary one-key CTX challenger of `PqxdhRecordLiftCtxModes`. It keeps the counter-erased chain-world state (seeds, full chain table, effects, produced and pending frames); public coins and public BLAKE2b queries are forwarded through a reserved known-call slot (`coinForward`, `hashForward`), so the challenger's shared cache is the world's cache; the selected coordinate's hidden openings and seals go to the challenger (`routeKeyed`); every other hidden coordinate's openings and seals are known calls (`PqxdhRecordLiftCtxModes.KnownCall`) at an injective slot (`slotOf`), with the coordinate's table key, in real mode exactly when its mode is real; caller-known native records run with their commitment hashes forwarded (`PqxdhRecordLiftCtxProtocol.knownRom`). The reduction receives no key of the selected coordinate. `linked_step` and `linked_schedule` show that the reduction run against the challenger's source state realizes the counter-erased CTX world with the selected key supplied externally, for every state and without a reachability premise; the selected coordinate's CTX state is the challenger's and every other coordinate's is its known slot's (`keysOf`). `link` concludes: the challenger's real or replay game (`PqxdhRecordLiftCtxModes.sourceGame`) against the key-free client `linkClient` (the whole program under the reduction, then the decision on the permitted view) is the CTX world in which the selected coordinate's key is a fresh uniform key and the selected coordinate is in the challenger's mode. With the step's coordinate of the key-indexed hybrid family, the real game is the hybrid before the step and the replay game the hybrid after it, as far as modes go (`selectedModes_hybrid_real`, `selectedModes_hybrid_replay`); the hybrids never use random mode (`hybridModes_notRandom`).

**Scope.** The remaining step from `ctxRun` to the uniform external key of the selected coordinate (the lazy/eager law of its table key, which needs the availability invariant that every keyed request is at a coordinate already in the table) and the identification of the last hybrid with `PqxdhRecordLiftIdeal.idealAuth` are later S4 stages; see `doc/impl/record-lift-ctx-hybrid.md`. No assumption or contract is used, and every theorem carries an exact `#print axioms` guard allowing only `propext`, `Classical.choice` and `Quot.sound`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftCtxProtocol (Bare bareInterpreter bareSeeds erasePrivate)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The CTX world with an explicit key function -/

/-- The key of a hidden coordinate, as a function of the chain table. `PqxdhRecordLiftIdeal` reads the key projection of the coordinate's table entry (`tableKey`). -/
abbrev KeyOf (n : Nat) := PqxdhRecordLiftChainTable.Table (Slot n) → Label n → CtxKey

/-- The key projection of the coordinate's table entry, as in `PqxdhRecordLiftIdeal.keyed`. -/
noncomputable def tableKey : KeyOf n := fun table label => (materialAt table label).1

/-- `PqxdhRecordLiftIdeal.keyed` with an explicit key function. -/
noncomputable def keyedWith (keyOf : KeyOf n) (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp) := fun query state => do
  let result ← (PqxdhRecordLiftProtocol.sampled ((simulateQ AdaptiveCtxSharedHash.hashImpl
    ((keyImpl decode crypto (keyOf state.base.chain query.1) (modes query.1) query.2).run
      (state.keys query.1))).run state.base.primitive.2)).run state.base
  pure (result.1.1.1, ⟨{ result.2 with primitive := (result.2.primitive.1, result.1.2) },
    Function.update state.keys query.1 result.1.1.2⟩)

/-- `PqxdhRecordLiftIdeal.ctxInterpreter` with an explicit key function. -/
noncomputable def ctxInterpreterWith (keyOf : KeyOf n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ (keyedWith keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state
  | .sealing pending => fun state => do
      let result ← (simulateQ (keyedWith keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto) ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
          state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
  | query => onBase (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query)

/-- `PqxdhRecordLiftIdeal.ctxRun` with an explicit key function. -/
noncomputable def ctxRunWith (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) : ProbComp (Client n E X × CtxPrivate n) :=
  (simulateQ (ctxInterpreterWith keyOf modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      CtxPrivate.initial

/-- With the table key, the explicit-key world is the CTX world of `PqxdhRecordLiftIdeal`. -/
theorem ctxRunWith_tableKey (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ctxRunWith tableKey modes replace setup codec route env serverKid bounds mode adversary =
      ctxRun modes replace setup codec route env serverKid bounds mode adversary := by
  have same : ctxInterpreterWith (tableKey (n := n)) modes replace setup codec = ctxInterpreter modes replace setup codec := by
    funext query
    cases query <;> rfl
  rw [ctxRunWith, same, ctxRun]

/-- The key of the selected coordinate is supplied externally; every other coordinate keeps its table key. -/
noncomputable def selectedKey (target : Label n) (key : CtxKey) : KeyOf n := fun table label =>
  if label = target then key else (materialAt table label).1

/-- The selected coordinate's challenger mode (`true`: real, `false`: replay); every other coordinate keeps its mode. -/
def selectedModes (target : Label n) (real : Bool) (modes : Label n → KeyMode) (label : Label n) : KeyMode :=
  if label = target then (if real then .real else .replay) else modes label

/-! ### The counter-erased CTX world -/

/-- The counter-erased state of a CTX world: the bare chain-world state and every coordinate's CTX state. -/
abbrev BareCtx (n : Nat) := Bare n × (Label n → KeyEntry)

/-- Erase the native and uniform analysis counters of a CTX-world state. -/
def eraseCtx (state : CtxPrivate n) : BareCtx n := (ctxBare state, state.keys)

/-- A keyed request on the counter-erased state. -/
noncomputable def bareKeyed (keyOf : KeyOf n) (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (BareCtx n) ProbComp) := fun query state => do
  let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
    ((keyImpl decode crypto (keyOf state.1.chain query.1) (modes query.1) query.2).run (state.2 query.1))).run
      state.1.cache
  pure (result.1.1, ({ state.1 with cache := result.2 }, Function.update state.2 query.1 result.1.2))

/-- The counter-erased CTX interpreter: the bare chain world's services and counter-free keyed requests. -/
noncomputable def bareCtxInterpreter (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (BareCtx n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ (bareKeyed keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (hiddenOpening (bareSeeds state.1) state.1.chain pending)).run state
  | .sealing pending => fun state => do
      let result ← (simulateQ (bareKeyed keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto) ((hiddenSealing codec.frameWrite state.1.chain replace pending).run state.1.pending)).run
          state
      pure (result.1.1, ({ result.2.1 with pending := result.1.2 }, result.2.2))
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (bareInterpreter setup codec (fun _ => true) query).run state.1

/-- A keyed request erases to the counter-free keyed request. -/
theorem keyedWith_erase (keyOf : KeyOf n) (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id eraseCtx <$> (keyedWith keyOf modes decode crypto query).run state =
      (bareKeyed keyOf modes decode crypto query).run (eraseCtx state) := by
  have erased := congrArg (fun work => (fun result => (result.1.1.1,
      ({ result.2 with cache := result.1.2 }, Function.update state.keys query.1 result.1.1.2))) <$> work)
    (PqxdhRecordLiftCtxProtocol.sampled_bare ((simulateQ AdaptiveCtxSharedHash.hashImpl
      ((keyImpl decode crypto (keyOf state.base.chain query.1) (modes query.1) query.2).run
        (state.keys query.1))).run state.base.primitive.2) state.base)
  simp only [Functor.map_map, Prod.map_def, id_eq] at erased
  simp only [keyedWith, bareKeyed, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, eraseCtx]
  exact erased

/-- Every service other than a hidden opening or sealing erases to the bare chain world's service, with the CTX states unchanged. -/
theorem base_erase (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n)
    (notOpening : ∀ pending, query ≠ .opening pending) (notSealing : ∀ pending, query ≠ .sealing pending)
    (state : CtxPrivate n) :
    Prod.map id eraseCtx <$> (ctxInterpreterWith keyOf modes replace setup codec query).run state =
      (bareCtxInterpreter keyOf modes replace setup codec query).run (eraseCtx state) := by
  have world : (ctxInterpreterWith keyOf modes replace setup codec query).run state =
      (fun result => (result.1, { state with base := result.2 })) <$>
        (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query).run state.base := by
    cases query with
    | opening pending => exact absurd rfl (notOpening pending)
    | sealing pending => exact absurd rfl (notSealing pending)
    | _ => rfl
  have bare : (bareCtxInterpreter keyOf modes replace setup codec query).run (eraseCtx state) =
      (fun result => (result.1, (result.2, state.keys))) <$>
        (bareInterpreter setup codec (fun _ => true) query).run (erasePrivate state.base) := by
    cases query with
    | opening pending => exact absurd rfl (notOpening pending)
    | sealing pending => exact absurd rfl (notSealing pending)
    | _ => rfl
  rw [world, bare, ← PqxdhRecordLiftCtxProtocol.bare_query setup codec (fun _ => true) query state.base]
  simp only [Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- Every service of the explicit-key CTX world erases to the counter-erased CTX interpreter, for every state. -/
theorem ctxInterpreterWith_erase (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) :
    Prod.map id eraseCtx <$> (ctxInterpreterWith keyOf modes replace setup codec query).run state =
      (bareCtxInterpreter keyOf modes replace setup codec query).run (eraseCtx state) := by
  cases query with
  | opening pending =>
      exact map_run_simulateQ_eq_of_query_map_eq _ _ eraseCtx
        (keyedWith_erase keyOf modes _ _) _ state
  | sealing pending =>
      have inner := map_run_simulateQ_eq_of_query_map_eq _ _ eraseCtx
        (keyedWith_erase keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending) state
      change Prod.map id eraseCtx <$> (do
          let result ← (simulateQ (keyedWith keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead)
            setup.source.crypto) ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
              state.base.pending)).run state
          pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) = (do
        let result ← (simulateQ (bareKeyed keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto) ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
            state.base.pending)).run (eraseCtx state)
        pure (result.1.1, ({ result.2.1 with pending := result.1.2 }, result.2.2)))
      rw [← inner]
      simp only [map_bind, map_pure, bind_map_left, Prod.map_def, id_eq]
      rfl
  | allocate _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | coin _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | hash _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | charge _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | lookup _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | knownSend _ _ =>
      exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | knownReceive _ _ _ =>
      exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | publish _ => exact base_erase keyOf modes replace setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state

/-! ### The key-free reduction of one hybrid step -/

open PqxdhRecordLiftCtxModes (KnownCall)

/-- The known-call history slot of a hidden coordinate: an injective code shifted by one. Slot zero is reserved for forwarded public coins and hashes. -/
def slotOf (label : Label n) : Nat :=
  Nat.pair (Nat.pair label.slot.val (if label.direction then 1 else 0)) label.position + 1

theorem slotOf_ne_zero (label : Label n) : slotOf label ≠ 0 := Nat.succ_ne_zero _

theorem slotOf_injective : Function.Injective (slotOf (n := n)) := by
  intro left right same
  simp only [slotOf, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at same
  obtain ⟨⟨slots, directions⟩, positions⟩ := same
  rcases left with ⟨leftSlot, leftDirection, leftPosition⟩
  rcases right with ⟨rightSlot, rightDirection, rightPosition⟩
  simp only at slots directions positions
  have slotEq : leftSlot = rightSlot := Fin.ext slots
  have directionEq : leftDirection = rightDirection := by
    cases leftDirection <;> cases rightDirection <;> simp_all
  subst slotEq directionEq positions
  rfl

/-- A fixed public key for the reserved slot; forwarded coin and hash requests never read it. -/
def publicKey : CtxKey := List.Vector.replicate 32 0

/-- A public request forwarded through the reserved known slot in real mode. -/
def publicCall (decode : RawDecoder) (request : ReceiveSpec.Domain) : KnownCall :=
  ⟨⟨0, publicKey, decode, request⟩, true⟩

/-- Forward a uniform coin through the reserved known slot. -/
def coinForward (decode : RawDecoder) : QueryImpl unifSpec (OracleComp PqxdhRecordLiftCtxModes.Spec) :=
  fun query => PqxdhRecordLiftCtxModes.Spec.query (.inr (publicCall decode (.inl (.inl query))))

/-- Forward a public BLAKE2b query through the reserved known slot. -/
def hashForward (decode : RawDecoder) : QueryImpl CtxRO (OracleComp PqxdhRecordLiftCtxModes.Spec) :=
  fun query => PqxdhRecordLiftCtxModes.Spec.query (.inr (publicCall decode (.inl (.inr (.inl query)))))

/-- Route a keyed request: the selected coordinate to the challenger; every other coordinate to a known call at its own slot with its table key, in real mode exactly when its mode is real. -/
noncomputable def routeKeyed (target : Label n) (modes : Label n → KeyMode) (decode : RawDecoder)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) :
    QueryImpl (KeyedSpec n) (OracleComp PqxdhRecordLiftCtxModes.Spec) := fun query =>
  if query.1 = target then PqxdhRecordLiftCtxModes.Spec.query (.inl query.2)
  else PqxdhRecordLiftCtxModes.Spec.query
    (.inr ⟨⟨slotOf query.1, (materialAt table query.1).1, decode, query.2⟩, decide (modes query.1 = .real)⟩)

/-- The key-free reduction of one hybrid step. It holds the counter-erased chain-world state (its cache field is unused: the shared cache is the challenger's); public coins and hashes are forwarded through the reserved slot, the selected coordinate's records go to the challenger, and every other hidden coordinate's records are known calls with their table keys. No selected key is an argument. -/
noncomputable def reduction (target : Label n) (modes : Label n → KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (Bare n) (OracleComp PqxdhRecordLiftCtxModes.Spec))
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

/-- The CTX states of all hidden coordinates read from the challenger's source state: the selected coordinate's from the challenger, every other coordinate's from its known slot. -/
def keysOf (target : Label n) (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Label n → KeyEntry :=
  fun label => if label = target then state.selected else state.others (slotOf label)

/-- Updating the reserved slot changes no hidden coordinate's CTX state. -/
theorem keysOf_reserved (target : Label n) (state : AdaptiveCtxDynamicKnownKeys.SourceState) (entry : KeyEntry)
    (cache : CtxRO.QueryCache) :
    keysOf target { state with others := Function.update state.others 0 entry, cache := cache } = keysOf target state := by
  funext label
  unfold keysOf
  split
  · rfl
  · exact Function.update_of_ne (slotOf_ne_zero label) entry state.others

/-- A forwarded coin leaves the whole challenger source state unchanged. -/
theorem coinForward_step (real : Bool) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : unifSpec.Domain) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key) (coinForward decode' query)).run state =
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
theorem coinForward_program {Result : Type} (real : Bool) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (work : ProbComp Result) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key)
      (simulateQ (coinForward decode') work)).run state = (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure result => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, coinForward_step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result

/-- The reserved slot's history after a forwarded public hash. -/
def publicEntry (entry : KeyEntry) (query : CtxRO.Domain) : KeyEntry :=
  ({ entry.1 with publicInputs := query.2 :: entry.1.publicInputs }, entry.2)

/-- Simulating a forwarded public hash is one known call at the reserved slot. -/
theorem simulateQ_hashForward {σ : Type} (impl : QueryImpl PqxdhRecordLiftCtxModes.Spec (StateT σ ProbComp))
    (decode : RawDecoder) (query : CtxRO.Domain) :
    simulateQ impl (hashForward decode query) = impl (.inr (publicCall decode (.inl (.inr (.inl query))))) := by
  unfold hashForward
  exact simulateQ_spec_query impl _

/-- A forwarded public hash is the shared random oracle on the challenger's cache; only the reserved slot's history changes. -/
theorem hashForward_step (real : Bool) (decode decode' : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxRO.Domain) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key) (hashForward decode' query)).run state =
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
theorem hashForward_program {Result : Type} (target : Label n) (real : Bool) (decode decode' : RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxKey) (work : OracleComp CtxRO Result)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, result.2.cache, keysOf target result.2)) <$>
      (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key)
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

/-- A challenger step updates exactly the selected coordinate's CTX state. -/
theorem keysOf_selected (target : Label n) (state : AdaptiveCtxDynamicKnownKeys.SourceState) (entry : KeyEntry)
    (cache : CtxRO.QueryCache) :
    keysOf target { state with selected := entry, cache := cache } = Function.update (keysOf target state) target entry := by
  funext label
  by_cases same : label = target
  · subst same
    simp [keysOf]
  · simp [keysOf, same]

/-- A known call at a coordinate's slot updates exactly that coordinate's CTX state. -/
theorem keysOf_other (target label : Label n) (different : label ≠ target)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) (entry : KeyEntry) (cache : CtxRO.QueryCache) :
    keysOf target { state with others := Function.update state.others (slotOf label) entry, cache := cache } =
      Function.update (keysOf target state) label entry := by
  funext other
  by_cases same : other = label
  · subst same
    simp [keysOf, different]
  · have slots : slotOf other ≠ slotOf label := fun equal => same (slotOf_injective equal)
    simp only [keysOf, Function.update_apply, same, slots, ite_false]

/-- The challenger's mode endpoints are the real and replay one-key CTX states. -/
theorem keyImpl_bool (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (real : Bool) :
    keyImpl decode crypto key (if real then .real else .replay) = AdaptiveCtxSharedModes.localImpl real decode crypto key := by
  cases real <;> rfl

/-- A known call's real/replay flag reproduces every non-random mode. -/
theorem keyImpl_known (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (notRandom : mode ≠ .random) :
    keyImpl decode crypto key mode = AdaptiveCtxSharedModes.localImpl (decide (mode = .real)) decode crypto key := by
  cases mode
  · rfl
  · rfl
  · exact absurd rfl notRandom

/-- One routed keyed request under the challenger's source state is the counter-erased keyed request with the selected coordinate's key supplied externally and its mode set by the challenger. -/
theorem routeKeyed_step (target : Label n) (modes : Label n → KeyMode)
    (notRandom : ∀ label, label ≠ target → modes label ≠ .random) (real : Bool) (decode : RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxKey) (red : Bare n) (query : (KeyedSpec n).Domain)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id (fun after : AdaptiveCtxDynamicKnownKeys.SourceState =>
        (({ red with cache := after.cache } : Bare n), keysOf target after)) <$>
      (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key)
        (routeKeyed target modes decode red.chain query)).run state =
      (bareKeyed (selectedKey target key) (selectedModes target real modes) decode crypto query).run
        (({ red with cache := state.cache } : Bare n), keysOf target state) := by
  rcases query with ⟨label, request⟩
  by_cases same : label = target
  · subst same
    have routed : simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key)
        (routeKeyed label modes decode red.chain (label, request)) =
        PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key (.inl request) := by
      simp only [routeKeyed, ite_true]
      exact simulateQ_spec_query _ _
    have source : (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key (.inl request)).run state =
        (fun result => (result.1.1, { state with selected := result.1.2, cache := result.2 })) <$>
          (simulateQ AdaptiveCtxSharedHash.hashImpl
            ((AdaptiveCtxSharedModes.localImpl real decode crypto key request).run state.selected)).run state.cache := by
      simp only [PqxdhRecordLiftCtxModes.sourceImpl, StateT.run, bind_pure_comp]
    rw [routed, source, Functor.map_map]
    have entry : keysOf label state label = state.selected := by simp [keysOf]
    simp only [bareKeyed, selectedKey, selectedModes, ite_true, keyImpl_bool, StateT.run, bind_pure_comp, entry]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, keysOf_selected]
  · have routed : simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key)
        (routeKeyed target modes decode red.chain (label, request)) =
        PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key
          (.inr ⟨⟨slotOf label, (materialAt red.chain label).1, decode, request⟩, decide (modes label = .real)⟩) := by
      simp only [routeKeyed, same, ite_false]
      exact simulateQ_spec_query _ _
    have source : (PqxdhRecordLiftCtxModes.sourceImpl real decode crypto key
          (.inr ⟨⟨slotOf label, (materialAt red.chain label).1, decode, request⟩, decide (modes label = .real)⟩)).run
          state =
        (fun result => (result.1.1,
            { state with others := Function.update state.others (slotOf label) result.1.2, cache := result.2 })) <$>
          (simulateQ AdaptiveCtxSharedHash.hashImpl
            ((AdaptiveCtxSharedModes.localImpl (decide (modes label = .real)) decode crypto (materialAt red.chain label).1
              request).run (state.others (slotOf label)))).run state.cache := by
      simp only [PqxdhRecordLiftCtxModes.sourceImpl, StateT.run, bind_pure_comp]
    rw [routed, source, Functor.map_map]
    have entry : keysOf target state label = state.others (slotOf label) := by simp [keysOf, same]
    simp only [bareKeyed, selectedKey, selectedModes, same, ite_false, keyImpl_known _ _ _ _ (notRandom label same),
      StateT.run, bind_pure_comp, entry]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, keysOf_other target label same]

/-- Every caller-known native program with its public hashes forwarded through the reserved slot is the counter-erased native program on the challenger's cache, and leaves every hidden coordinate's CTX state unchanged. -/
theorem known_link {Result : Type} (target : Label n) (real : Bool) (decode decode' : RawDecoder)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (key : CtxKey) (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (red : Bare n)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, ({ red with cache := result.2.cache, pending := result.1.2 } : Bare n),
        keysOf target result.2)) <$>
      (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real decode setup.source.crypto key)
        (simulateQ (hashForward decode') ((simulateQ (PqxdhRecordLiftCtxProtocol.knownRom setup.source codec.frameWrite)
          work).run red.pending))).run state =
      (fun result => (result.1, ({ red with cache := result.2.1, pending := result.2.2 } : Bare n), keysOf target state)) <$>
        (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work).run
          (state.cache, red.pending) := by
  have forwarded := congrArg (fun program => (fun result : (Result × PqxdhRecordLiftLoggedAdapters.Frames) ×
      CtxRO.QueryCache × (Label n → KeyEntry) =>
        (result.1.1, ({ red with cache := result.2.1, pending := result.1.2 } : Bare n), result.2.2)) <$> program)
    (hashForward_program target real decode decode' setup.source.crypto key
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
noncomputable def linked (target : Label n) (modes : Label n → KeyMode) (real : Bool) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n)
      (StateT (Bare n × AdaptiveCtxDynamicKnownKeys.SourceState) ProbComp) :=
  ((PqxdhRecordLiftCtxModes.sourceImpl real (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    key).mapStateTBase (reduction target modes setup codec)).flattenStateT

/-- The counter-erased CTX state realized by the reduction state and the challenger's source state. -/
def linkProj (target : Label n) (state : Bare n × AdaptiveCtxDynamicKnownKeys.SourceState) : BareCtx n :=
  ({ state.1 with cache := state.2.cache }, keysOf target state.2)

theorem linked_run (target : Label n) (modes : Label n → KeyMode) (real : Bool) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (red : Bare n) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (linked target modes real key setup codec query).run (red, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key) ((reduction target modes setup codec query).run red)).run state := rfl

/-- Every service of the reduction, run against the challenger's source state, realizes the counter-erased CTX service with the selected coordinate's key supplied externally and its mode set by the challenger. No reachability premise is used. -/
theorem linked_step (target : Label n) (modes : Label n → KeyMode)
    (notRandom : ∀ label, label ≠ target → modes label ≠ .random) (real : Bool) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id (linkProj target) <$> (linked target modes real key setup codec query).run state =
      (bareCtxInterpreter (selectedKey target key) (selectedModes target real modes) id setup codec query).run
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
        (PqxdhRecordLiftCtxModes.sourceImpl real (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key ∘ₛ
          routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
        (bareKeyed (selectedKey target key) (selectedModes target real modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (fun after : AdaptiveCtxDynamicKnownKeys.SourceState => (({ red with cache := after.cache } : Bare n),
          keysOf target after))
        (fun request after => by
          simpa only [QueryImpl.compose] using routeKeyed_step target modes notRandom real
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
        (PqxdhRecordLiftCtxModes.sourceImpl real (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key ∘ₛ
          routeKeyed target modes (RawCtxUniversalDecoder.decoder codec.frameRead) red.chain)
        (bareKeyed (selectedKey target key) (selectedModes target real modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (fun after : AdaptiveCtxDynamicKnownKeys.SourceState => (({ red with cache := after.cache } : Bare n),
          keysOf target after))
        (fun request after => by
          simpa only [QueryImpl.compose] using routeKeyed_step target modes notRandom real
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
        let result ← (simulateQ (bareKeyed (selectedKey target key) (selectedModes target real modes)
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
            ((hiddenSealing codec.frameWrite red.chain id pending).run red.pending)).run
              (({ red with cache := source.cache } : Bare n), keysOf target source)
        pure (result.1.1, ({ result.2.1 with pending := result.1.2 }, result.2.2)))
      rw [← inner]
      simp only [bind_pure_comp, Functor.map_map]
      rfl
  | knownSend kernel context =>
      have fact := known_link target real (RawCtxUniversalDecoder.decoder codec.frameRead)
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
      have fact := known_link target real (RawCtxUniversalDecoder.decoder codec.frameRead)
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
theorem linked_schedule {Result : Type} (target : Label n) (modes : Label n → KeyMode)
    (notRandom : ∀ label, label ≠ target → modes label ≠ .random) (real : Bool) (key : CtxKey)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (red : Bare n)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, linkProj target (result.1.2, result.2))) <$>
      (simulateQ (PqxdhRecordLiftCtxModes.sourceImpl real (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key) ((simulateQ (reduction target modes setup codec) client).run red)).run state =
      (simulateQ (bareCtxInterpreter (selectedKey target key) (selectedModes target real modes) id setup codec)
        client).run (linkProj target (red, state)) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  exact map_run_simulateQ_eq_of_query_map_eq (linked target modes real key setup codec)
    (bareCtxInterpreter (selectedKey target key) (selectedModes target real modes) id setup codec) (linkProj target)
    (linked_step target modes notRandom real key setup codec) client (red, state)

/-- Every complete adaptive program of the explicit-key CTX world erases to the counter-erased CTX world. -/
theorem ctxInterpreterWith_schedule {Result : Type} (keyOf : KeyOf n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : CtxPrivate n) :
    Prod.map id eraseCtx <$> (simulateQ (ctxInterpreterWith keyOf modes replace setup codec) client).run state =
      (simulateQ (bareCtxInterpreter keyOf modes replace setup codec) client).run (eraseCtx state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ eraseCtx (ctxInterpreterWith_erase keyOf modes replace setup codec) client state

/-- The key-free reduction client of one hybrid step: the whole program under `reduction`, then the decision on the permitted view with its coins forwarded through the reserved slot. -/
noncomputable def linkClient (target : Label n) (modes : Label n → KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (decision : View n E X → ProbComp Bool) :
    OracleComp PqxdhRecordLiftCtxModes.Spec Bool := do
  let result ← (simulateQ (reduction target modes setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
  simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead)) (decision (viewOf result.1 result.2.produced))

/-- The reduction's initial state and the challenger's initial source state realize the CTX world's initial state. -/
theorem linkProj_initial (target : Label n) :
    linkProj target (erasePrivate PqxdhRecordLiftProtocol.initialPrivate, AdaptiveCtxDynamicKnownKeys.initialSource) =
      eraseCtx (CtxPrivate.initial : CtxPrivate n) := by
  simp only [linkProj, eraseCtx, ctxBare, CtxPrivate.initial, Prod.mk.injEq]
  constructor
  · rfl
  · funext label
    simp only [keysOf]
    split <;> rfl

/-- Link of one hybrid step (X1): the challenger's real (`real = true`) or replay (`real = false`) game against the key-free reduction client is the CTX world in which the selected coordinate's key is a fresh uniform key held by the challenger, in the challenger's mode, and every other hidden coordinate keeps its table key and its mode. -/
theorem link (target : Label n) (modes : Label n → KeyMode)
    (notRandom : ∀ label, label ≠ target → modes label ≠ .random) (real : Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (decision : View n E X → ProbComp Bool) :
    Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame real (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (linkClient target modes setup codec route env serverKid bounds mode adversary decision) =
      (do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWith (selectedKey target key) (selectedModes target real modes) id setup codec route env
          serverKid bounds mode adversary
        decision (ctxView result)) := by
  simp only [PqxdhRecordLiftCtxModes.sourceGame, map_bind]
  apply bind_congr
  intro key
  simp only [linkClient, simulateQ_bind, StateT.run_bind, map_bind, coinForward_program, Functor.map_map]
  have schedule := linked_schedule target modes notRandom real key setup codec
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    (erasePrivate PqxdhRecordLiftProtocol.initialPrivate) AdaptiveCtxDynamicKnownKeys.initialSource
  have world := ctxInterpreterWith_schedule (selectedKey target key) (selectedModes target real modes) id setup codec
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

/-! ### The step of the key-indexed hybrid family -/

/-- The key-indexed hybrids never use random mode. -/
theorem hybridModes_notRandom (positions cut : Nat) (label : Label n) : hybridModes positions cut label ≠ .random := by
  unfold hybridModes
  split <;> simp

/-- With the step's coordinate in real mode, the challenger's real game is the hybrid before the step. -/
theorem selectedModes_hybrid_real (positions : Nat) (step : Fin (positions * (n * 2))) :
    selectedModes (PqxdhRecordLiftChainOrder.entryAt step) true (hybridModes positions step.val) =
      hybridModes positions step.val := by
  funext label
  by_cases same : label = PqxdhRecordLiftChainOrder.entryAt step
  · subst same
    simp only [selectedModes, ite_true, (hybridModes_step positions step).1]
  · simp only [selectedModes, same, ite_false]

/-- With the step's coordinate in replay mode, the challenger's replay game is the hybrid after the step. -/
theorem selectedModes_hybrid_replay (positions : Nat) (step : Fin (positions * (n * 2))) :
    selectedModes (PqxdhRecordLiftChainOrder.entryAt step) false (hybridModes positions step.val) =
      hybridModes positions (step.val + 1) := by
  funext label
  by_cases same : label = PqxdhRecordLiftChainOrder.entryAt step
  · subst same
    simp only [selectedModes, ite_true, Bool.false_eq_true, ite_false, (hybridModes_step positions step).2]
  · simp only [selectedModes, same, ite_false, hybridModes_unchanged positions step label same]

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxRunWith_tableKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxRunWith_tableKey

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyedWith_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyedWith_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.base_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.base_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxInterpreterWith_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxInterpreterWith_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.slotOf_ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.slotOf_ne_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.slotOf_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.slotOf_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_reserved

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.coinForward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.coinForward_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.coinForward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.coinForward_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.simulateQ_hashForward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.simulateQ_hashForward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hashForward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hashForward_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hashForward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hashForward_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keysOf_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyImpl_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyImpl_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyImpl_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.keyImpl_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.routeKeyed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.routeKeyed_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.known_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.known_link

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linked_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxInterpreterWith_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.ctxInterpreterWith_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linkProj_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.linkProj_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.link

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hybridModes_notRandom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.hybridModes_notRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.selectedModes_hybrid_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.selectedModes_hybrid_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.selectedModes_hybrid_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink.selectedModes_hybrid_replay
