-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-! Source attempted-seal history and absence of private cache/nonces before a coordinate's first seal. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource
open CtxRomAuth AdaptiveCtxReceive LazyOracleDiscard
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec materialAt)
open PqxdhRecordFactsPrivateCacheFamily (erasedKeyed localLens keyedPointed_run)
open PqxdhRecordFactsPrivateCacheServices (MixedSpec)
open PqxdhRecordFactsPrivateCacheCompiler (BaseSpec base compile injectKey)
open PqxdhRecordLiftProtocol (Private ServiceSpec Service)
variable {n : Nat}

/-- Coordinates absent from the attempted-seal history still have no private suffix answers and no used nonce. -/
def Virgin (state : CtxPrivate n) (past : List (Label n)) : Prop :=
  ∀ label, label ∉ past → (state.keys label).2 = ∅ ∧ (state.keys label).1.usedNonces = []

private theorem apply_map {σ α β : Type} (f : α → β) (work : StateT σ ProbComp α)
    (state : σ) : (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun r => pure (f r.1, r.2)) = _
  simp only [bind_pure_comp]; rfl

/-- Explicit local form of the erased keyed step, retaining every other coordinate and the full base state. -/
theorem erasedKeyed_run (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    (erasedKeyed modes decode crypto query).run state =
      (fun result => (result.1, { state with
        base := { state.base with primitive := (state.base.primitive.1, result.2.2) }
        keys := Function.update state.keys query.1 result.2.1 })) <$>
        (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto
          (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
          (state.keys query.1, state.base.primitive.2) := by
  have pointed := keyedPointed_run modes decode crypto query state
  simp only [StateLens.lift, localLens, StateT.run, Functor.map_map] at pointed
  simp only [erasedKeyed, PqxdhRecordFactsPrivateCacheRandom.erased, StateT.run,
    apply_map, pointed, Functor.map_map]
  rfl

/-- Every supported erased keyed result comes from the exact local endpoint and changes only its selected entry and shared ROM. -/
theorem erasedKeyed_witness (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((erasedKeyed modes decode crypto query).run state)) :
    ∃ localState, (result.1, localState) ∈ support
      ((PqxdhRecordFactsPrivateCacheRandom.erased decode crypto
        (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
        (state.keys query.1, state.base.primitive.2)) ∧
      result.2.keys = Function.update state.keys query.1 localState.1 ∧
      result.2.base = { state.base with primitive := (state.base.primitive.1, localState.2) } := by
  simp only [erasedKeyed_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ⟨inner.2, reached, rfl, rfl⟩

/-- Coordinates other than the selected one retain their entire entry, including their private suffix dictionary and nonce list. -/
theorem erasedKeyed_other (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((erasedKeyed modes decode crypto query).run state))
    (label : Label n) (different : label ≠ query.1) : result.2.keys label = state.keys label := by
  obtain ⟨_, _, keys, _⟩ := erasedKeyed_witness modes decode crypto query state result supported
  rw [keys, Function.update_of_ne different]

/-- An erased raw step preserves the selected entry's nonce list and whole private cache, including rejected inputs. -/
theorem localRaw_retains (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (raw : Pqxdh.Bytes) (state : PqxdhRecordFactsPrivateCache.State)
    (result : Option Pqxdh.Bytes × PqxdhRecordFactsPrivateCache.State)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr raw)).run state)) :
    result.2.1.2 = state.1.2 ∧ result.2.1.1.usedNonces = state.1.1.usedNonces := by
  cases parsed : decode raw <;>
    simp only [PqxdhRecordFactsPrivateCacheRandom.erased,
      PqxdhRecordFactsPrivateCacheRandom.modePointed, StateT.run, apply_map,
      PqxdhRecordFactsPrivateCache.rawBase, parsed, map_pure, support_pure, Set.mem_singleton_iff,
      Prod.map, id_eq] at supported
  all_goals exact supported ▸ ⟨rfl, rfl⟩

/-- Recording a seal attempt permits changes only at its coordinate; every other virgin coordinate remains untouched. -/
theorem Virgin.seal {before after : CtxPrivate n} {past : List (Label n)} {selected : Label n}
    (good : Virgin before past) (others : ∀ label, label ≠ selected → after.keys label = before.keys label) :
    Virgin after (past ++ [selected]) := by
  intro label absent
  have fresh : label ∉ past ∧ label ≠ selected := by
    simpa only [List.mem_append, List.mem_singleton, not_or] using absent
  rw [others label fresh.2]
  exact good label fresh.1

/-- Every erased raw coordinate request preserves virgin entries at all coordinates. -/
theorem raw_virgin (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (selected : Label n) (raw : Pqxdh.Bytes) (state : CtxPrivate n) (past : List (Label n))
    (good : Virgin state past) (result : Option Pqxdh.Bytes × CtxPrivate n)
    (supported : result ∈ support ((erasedKeyed modes decode crypto (selected, .inr raw)).run state)) :
    Virgin result.2 past := by
  obtain ⟨localState, reached, keys, _⟩ := erasedKeyed_witness modes decode crypto (selected, .inr raw) state result supported
  have retained := localRaw_retains decode crypto (materialAt state.base.chain selected).1
    (modes selected) raw (state.keys selected, state.base.primitive.2) (result.1, localState) reached
  intro label absent
  by_cases same : label = selected
  · subst label
    simp only [keys, Function.update_self]
    exact ⟨retained.1.trans (good selected absent).1, retained.2.trans (good selected absent).2⟩
  · rw [keys, Function.update_of_ne same]
    exact good label absent

/-- Every supported sealing reply, including refusal, preserves virgin entries outside its now-recorded attempted coordinate. -/
theorem seal_virgin (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (selected : Label n) (input : CtxSealInput) (state : CtxPrivate n) (past : List (Label n))
    (good : Virgin state past) (result : Option CtxRomRecord × CtxPrivate n)
    (supported : result ∈ support ((erasedKeyed modes decode crypto (selected, .inl (.inr (.inr input)))).run state)) :
    Virgin result.2 (past ++ [selected]) :=
  good.seal (erasedKeyed_other modes decode crypto (selected, .inl (.inr (.inr input))) state result supported)

/-- Cache discard leaves every internal base service exactly unchanged. -/
theorem erased_base (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)) (q : (BaseSpec n).Domain) :
    PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl) (.inr q) =
      PqxdhRecordLiftIdeal.onBase (base impl q) := by
  simp only [PqxdhRecordFactsPrivateCacheServices.erased,
    PqxdhRecordFactsPrivateCacheServices.pointed, Functor.map_map]
  exact id_map _

/-- Arbitrary keyed continuations survive injection into the erased mixed interface literally. -/
theorem erased_inject (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)) {Result : Type}
    (client : OracleComp (KeyedSpec n) Result) :
    simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
      (simulateQ injectKey client) = simulateQ (erasedKeyed modes decode crypto) client := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  ext query
  simp only [QueryImpl.apply_compose, injectKey, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheServices.erased, PqxdhRecordFactsPrivateCacheServices.pointed,
    erasedKeyed]
  rfl

private theorem apply_bind {σ α β : Type} (work : StateT σ ProbComp α)
    (next : α → StateT σ ProbComp β) (state : σ) :
    (work >>= next) state = (work state >>= fun result => next result.1 result.2) := rfl

private theorem apply_pure {σ α : Type} (value : α) (state : σ) :
    (pure value : StateT σ ProbComp α) state = pure (value, state) := rfl

/-- The erased compiler runs exactly the original hidden opening through erased keyed requests. -/
theorem erased_opening (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
      (compile writer replace (.opening pending))).run state =
    (simulateQ (erasedKeyed modes decode crypto)
      (PqxdhRecordLiftIdeal.hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base)
        state.base.chain pending)).run state := by
  simp only [compile, simulateQ_bind, simulateQ_spec_query, erased_base, base,
    StateT.run, apply_bind, PqxdhRecordLiftIdeal.onBase, map_pure, pure_bind, erased_inject]

/-- The erased compiler retains the original hidden seal and exact writer-buffer reinstallation. -/
theorem erased_sealing (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
      (compile writer replace (.sealing pending))).run state =
    ((simulateQ (erasedKeyed modes decode crypto)
      ((PqxdhRecordLiftIdeal.hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state
      >>= fun result => pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) := by
  simp only [compile, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, erased_base, base,
    StateT.run, apply_bind, PqxdhRecordLiftIdeal.onBase, map_pure, pure_bind, erased_inject]
  rfl

/-- The original hidden-opening program changes no virgin cache or nonce list, regardless of parser, argument or opening result. -/
theorem hiddenOpening_virgin (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) (past : List (Label n))
    (good : Virgin state past)
    (result : CoreModels.core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (erasedKeyed modes decode crypto)
      (PqxdhRecordLiftIdeal.hiddenOpening seeds table pending)).run state)) :
    Virgin result.2 past := by
  unfold PqxdhRecordLiftIdeal.hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ good
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ good
    · split at supported
      · simp only [simulateQ_map, simulateQ_spec_query, StateT.run, apply_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact raw_virgin modes decode crypto _ _ state past good inner reached
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        exact supported ▸ good

/-- Hidden sealing can change only its attempted coordinate's cache and nonce list; writer failure does not discard the attempt. -/
theorem hiddenSealing_virgin (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Sealing n) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (state : CtxPrivate n) (past : List (Label n)) (good : Virgin state past)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftLoggedAdapters.Frames) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (erasedKeyed modes decode crypto)
      ((PqxdhRecordLiftIdeal.hiddenSealing writer table replace pending).run frames)).run state)) :
    Virgin result.2 (past ++ [pending.material]) := by
  simp only [PqxdhRecordLiftIdeal.hiddenSealing, StateT.run] at supported
  split at supported
  · simp only [simulateQ_bind, simulateQ_spec_query, apply_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, finished⟩ := supported
    have preserved := seal_virgin modes decode crypto pending.material _ state past good inner reached
    cases reply : inner.1 <;>
      simp only [reply, simulateQ_pure, apply_pure, support_pure, Set.mem_singleton_iff] at finished
    all_goals exact finished ▸ preserved
  · simp only [simulateQ_pure, apply_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ good.seal (fun _ _ => rfl)

/-- The complete service compiler preserves virgin coordinates, appending precisely the original source's attempted-seal coordinate. -/
theorem compiled_virgin (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (state : CtxPrivate n) (past : List (Label n)) (good : Virgin state past)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
      (compile writer replace query)).run state)) :
    Virgin result.2 (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query) := by
  cases query with
  | opening pending =>
      rw [erased_opening] at supported
      simpa only [PqxdhRecordLiftWorldProvenance.sealingCoordinates, List.append_nil] using
        hiddenOpening_virgin modes decode crypto _ _ pending state past good result supported
  | sealing pending =>
      rw [erased_sealing] at supported
      simp only [bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact hiddenSealing_virgin modes decode crypto writer replace _ pending _ state past good inner reached
  | _ =>
      simp only [compile, simulateQ_spec_query, erased_base, base, PqxdhRecordLiftIdeal.onBase,
        StateT.run, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      simpa only [PqxdhRecordLiftWorldProvenance.sealingCoordinates, List.append_nil, Virgin] using good

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Actual erased-world services preserve the source-history cache invariant, without any cryptographic premise. -/
theorem query_virgin (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : Service n) (state : CtxPrivate n) (past : List (Label n)) (good : Virgin state past)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state)) :
    Virgin result.2 (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query) :=
  compiled_virgin modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
    query state past good result supported

/-- The pre-query condition that turns a hidden seal's actual private lookup into a fresh uniform digest. -/
def FreshPoint (state : CtxPrivate n) : Service n → Prop
  | .sealing pending => (state.keys pending.material).2 = ∅ ∧ (state.keys pending.material).1.usedNonces = []
  | _ => True

/-- The source's previously proved pre-query attempted-history freshness supplies the exact empty-cache and unused-nonce condition. -/
theorem freshPoint (query : Service n) (state : CtxPrivate n) (past : List (Label n))
    (good : Virgin state past) (fresh : PqxdhRecordLiftProtocolHistory.Fresh (past, query)) :
    FreshPoint state query := by
  cases query <;> try trivial
  case sealing pending => exact good pending.material fresh

/-- Initialization has an empty private suffix cache and nonce list at every coordinate. -/
theorem initial_virgin : Virgin (PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))) [] := by
  intro label absent
  constructor <;> rfl

/-- A proof-side bad flag tests the pre-query state; the source service and all its replies remain literal. -/
noncomputable def checked (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n × Bool) ProbComp) := by
  classical
  exact fun query state => do
    let result ← (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state.1
    pure (result.1, (result.2, state.2 || decide (¬ FreshPoint state.1 query)))

/-- Erasing only the proof-side bad flag recovers the complete original erased execution and result, for any adaptive client. -/
theorem checked_project (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : CtxPrivate n × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (checked modes replace setup codec) client).run state =
      (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) client).run state.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst _ client state
  intro query before
  simp only [checked, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq]
  exact id_map _

/-- Under the source's all-reply freshness fact, no supported execution ever marks a nonempty or previously used hidden sealing coordinate. -/
theorem checked_safe (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : CtxPrivate n) (past : List (Label n))
    (good : Virgin state past)
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh)
    (result : Result × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (checked modes replace setup codec) client).run (state, false))) :
    result.2.2 = false := by
  induction client using OracleComp.inductionOn generalizing state past result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ rfl
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      have point := freshPoint query state past good fresh.1
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, apply_bind,
        checked, bind_pure_comp, bind_map_left, point, not_true_eq_false,
        decide_false, Bool.or_self, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, continued⟩ := supported
      exact ih inner.1 inner.2 _ (query_virgin modes replace setup codec query state past good inner reached)
        (fresh.2 inner.1) result continued

open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- The actual source run with only the private pre-query freshness flag added. -/
noncomputable def checkedRun {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ProbComp (PqxdhRecordLiftIdeal.Client n E X × (CtxPrivate n × Bool)) :=
  (simulateQ (checked modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial, false)

/-- Projecting the proof-side flag recovers the full actual erased world, including the same source control and all private state. -/
theorem checkedRun_project {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    Prod.map id Prod.fst <$> checkedRun modes replace setup codec route env serverKid bounds mode adversary =
      PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary :=
  checked_project modes replace setup codec _ _

/-- Every supported complete initialized source execution keeps the pre-query bad flag false. Thus every actual hidden sealing request sees an empty private suffix cache and unused nonce list before its reply. -/
theorem checkedRun_safe {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support (checkedRun modes replace setup codec route env serverKid bounds mode adversary)) :
    result.2.2 = false :=
  checked_safe modes replace setup codec _ _ [] initial_virgin
    (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)
    result supported

/-- A supported prefix of the literal service execution, ending before its next query is answered. No final completion or writer success is required. -/
inductive Reach {Result : Type}
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initial : OracleComp (ServiceSpec n) Result) (start : CtxPrivate n) (past0 : List (Label n)) :
    OracleComp (ServiceSpec n) Result → CtxPrivate n → List (Label n) → Prop where
  | initial : Reach service initial start past0 initial start past0
  | step {query : Service n} {next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) Result}
      {state : CtxPrivate n} {past : List (Label n)} {reply : (ServiceSpec n).Range query × CtxPrivate n}
      (before : Reach service initial start past0
        ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= next) state past)
      (supported : reply ∈ support ((service query).run state)) :
      Reach service initial start past0 (next reply.1) reply.2
        (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query)

/-- The exact source cache invariant holds at every supported prefix, including one whose next endpoint does not return. -/
theorem reach_virgin (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    {initial client : OracleComp (ServiceSpec n) Result} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (good : Virgin start past0)
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      initial start past0 client state past) : Virgin state past := by
  induction reached with
  | initial => exact good
  | step before supported ih => exact query_virgin modes replace setup codec _ _ _ ih _ supported

/-- Source all-reply pre-query freshness is preserved by every supported prefix, independently of the private endpoint's return distribution. -/
theorem reach_fresh {Result : Type}
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial client : OracleComp (ServiceSpec n) Result} {start state : CtxPrivate n}
    {past0 past : List (Label n)}
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated initial past0).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh)
    (reached : Reach service initial start past0 client state past) :
    (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy PqxdhRecordLiftProtocolHistory.Fresh := by
  induction reached with
  | initial => exact fresh
  | step before supported ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at ih
      exact ih.2 _

/-- At every supported prefix of the actual initialized source program, the next hidden seal's suffix cache and used-nonce list are empty before its endpoint replies. No cryptographic, writer-success or source-freshness premise is supplied. -/
theorem source_prefix_fresh {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    FreshPoint state query := by
  have good := reach_virgin modes replace setup codec initial_virgin reached
  have fresh := reach_fresh _
    (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)
    reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
  exact freshPoint query state past good fresh.1

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erasedKeyed_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.localRaw_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.localRaw_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.Virgin.seal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.Virgin.seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.raw_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.raw_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.seal_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.seal_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_inject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_inject

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.erased_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.hiddenOpening_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.hiddenOpening_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.hiddenSealing_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.hiddenSealing_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.compiled_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.compiled_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.query_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.query_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.freshPoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.freshPoint

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.initial_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.initial_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checked_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checked_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checked_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checked_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checkedRun_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checkedRun_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checkedRun_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.checkedRun_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.reach_virgin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.reach_virgin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.reach_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.reach_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.source_prefix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource.source_prefix_fresh
