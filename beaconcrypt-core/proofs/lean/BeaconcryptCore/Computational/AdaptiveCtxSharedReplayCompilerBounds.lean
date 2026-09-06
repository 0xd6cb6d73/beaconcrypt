import BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler
import BeaconcryptCore.Computational.AdaptiveSealKeyBounds
import BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds
import BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds

/-!
The key-free shared-cache compiler retains exact original indices and sealing plaintext in its complete weighted ledger. Source coin/work caps and arbitrary index/input-dependent seal prices derive ordinary selected seal/byte caps and all other-random ciphertext work. Every source and reduction key draw, shared/private digest, random body and tag remains charged through the entire adaptive continuation.

These statements account for the actual compiled independent-key experiment. Native evolving-key distribution, reveal/restore freshness and the common symbolic experiment remain separate. No primitive implementation is proved. All substantial statements, assumptions and exact costs are explained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds
open CtxRomAuth CtxSplitCache CtxNonceAeadIntCtxt AdaptiveCtxReceive CtxComputationalSecurity
open CtxNonceAeadIndDollarValidation
open AdaptiveCtxSharedHash (HashSpec hashImpl)
open AdaptiveCtxSharedReplaySeal
open AdaptiveCtxSharedReplayCompiler
open AdaptiveSealKeyBounds (WorkBound work_mono)

/-- Weighted costs add across every possible reply of the original computation. -/
theorem work_bind {ι First Result : Type} {spec : OracleSpec ι}
    (cost : spec.Domain → Nat) (first : OracleComp spec First)
    (next : First → OracleComp spec Result) (left right : Nat)
    (firstBound : WorkBound cost first left) (nextBound : ∀ value, WorkBound cost (next value) right) :
    WorkBound cost (first >>= next) (left + right) := by
  exact OracleComp.isQueryBound_bind Nat.add
    (fun query left right available allowed => by
      change cost query ≤ left + available ∧ cost query ≤ available + right
      constructor <;> omega)
    (fun query left right available allowed => by
      change left + (available - cost query) = left + available - cost query ∧
        available + right - cost query = (available - cost query) + right
      constructor <;> omega)
    firstBound nextBound

/-- Stateful compilation preserves an arbitrary weighted budget when each actual query implementation supplies that same cost. -/
theorem work_compile {ι κ Result LocalState : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (sourceCost : source.Domain → Nat) (targetCost : target.Domain → Nat)
    (impl : QueryImpl source (StateT LocalState (OracleComp target)))
    (client : OracleComp source Result) (budget : Nat) (bounded : WorkBound sourceCost client budget)
    (step : ∀ query state, WorkBound targetCost ((impl query).run state) (sourceCost query)) (state : LocalState) :
    WorkBound targetCost ((simulateQ impl client).run state) budget := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => sourceCost query)
    (fun first rest => work_bind _ _ _ _ _ first rest)
    (fun query _ state _ => step query state)
    (fun _query _available allowed => by dsimp; omega) state

/-- Pure query forwarding also transfers the complete weighted budget. -/
theorem work_forward {ι κ Result : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (sourceCost : source.Domain → Nat) (targetCost : target.Domain → Nat)
    (impl : QueryImpl source (OracleComp target)) (client : OracleComp source Result)
    (budget : Nat) (bounded : WorkBound sourceCost client budget)
    (step : ∀ query, WorkBound targetCost (impl query) (sourceCost query)) :
    WorkBound targetCost (simulateQ impl client) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    rw [WorkBound, isQueryBound_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query]
    have combined := work_bind targetCost (impl query) (fun reply => simulateQ impl (next reply))
      (sourceCost query) (budget - sourceCost query) (step query)
      (fun reply => ih reply _ (bounded.2 reply))
    simpa only [Nat.add_sub_of_le bounded.1] using combined

/-- A total query cap bounds any per-query price, without inspecting sampled values. -/
theorem work_of_total {ι Result : Type} {spec : OracleSpec ι}
    (cost : spec.Domain → Nat) (price : Nat) (prices : ∀ query, cost query ≤ price)
    (client : OracleComp spec Result) (budget : Nat) (bounded : client.IsTotalQueryBound budget) :
    WorkBound cost client (budget * price) := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    cases budget with
    | zero => simp at bounded
    | succ budget =>
      have combined := work_bind cost (spec.query query) next price (budget * price)
        (by simp [WorkBound, isQueryBound_query_iff, prices query])
        (fun reply => ih reply budget (by simpa using bounded.2 reply))
      simpa only [Nat.succ_mul, Nat.add_comm] using combined

def IndexedCost {count : Nat} (coinPrice : Nat)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat) :
    (AdaptiveSealKeyFamily.Spec count).Domain → Nat
  | ⟨_, .inl _⟩ => coinPrice
  | ⟨index, .inr input⟩ => sealPrice index input

def HashCost (coinPrice : Nat) : HashSpec.Domain → Nat
  | .inl _ => coinPrice
  | .inr _ => 64 * coinPrice

def LocalCost (coinPrice : Nat) (sealPrice : ModifiedNonceAeadSealSpec.Domain → Nat) : SealSpec.Domain → Nat
  | .inl hash => HashCost coinPrice hash
  | .inr input => sealPrice input

/-- Every forwarded coin retains its original owner index and exact finite range. -/
theorem coin_work {count : Nat} {Result : Type} (index : Fin count) (coinPrice : Nat)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (work : ProbComp Result) (budget : Nat) (bounded : work.IsTotalQueryBound budget) :
    WorkBound (IndexedCost coinPrice sealPrice) (simulateQ (coinForward index) work) (budget * coinPrice) := by
  exact work_forward (fun _ => coinPrice) _ _ _ _
    (work_of_total _ coinPrice (fun _ => le_refl _) work budget bounded)
    (fun query => by
      change (liftM ((AdaptiveSealKeyFamily.Spec count).query ⟨index, .inl query⟩) : OracleComp (AdaptiveSealKeyFamily.Spec count) _).IsQueryBound
        coinPrice (fun query available => IndexedCost coinPrice sealPrice query ≤ available)
        (fun query available => available - IndexedCost coinPrice sealPrice query)
      exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _))

/-- The backend charges each actual shared-cache miss, and forwards the exact seal input unchanged. -/
theorem backend_work {count : Nat} (index : Fin count) (coinPrice : Nat)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (query : SealSpec.Domain) (cache : CtxRO.QueryCache) :
    WorkBound (IndexedCost coinPrice sealPrice) ((backend index query).run cache)
      (LocalCost coinPrice (sealPrice index) query) := by
  cases query with
  | inl hash =>
    have bounded := coin_work index coinPrice sealPrice ((hashImpl hash).run cache) _
      (AdaptiveCtxSharedSourceBounds.hash_step_bound hash cache)
    cases hash <;> simpa only [backend, StateT.run, LocalCost, HashCost,
      AdaptiveCtxSharedHash.HashClass, Bool.false_eq_true, if_true, if_false, Nat.one_mul] using bounded
  | inr input =>
    simp only [backend, StateT.run, bind_pure_comp, WorkBound, isQueryBound_map_iff,
      isQueryBound_query_iff, IndexedCost, LocalCost, le_refl]

/-- Lifting explicit probabilistic work to the hash interface changes neither its actual coin cost nor its range. -/
theorem lifted_work {Result : Type} (coinPrice : Nat) (work : ProbComp Result)
    (budget : Nat) (bounded : work.IsTotalQueryBound budget) :
    WorkBound (HashCost coinPrice) (OracleComp.liftComp work HashSpec) (budget * coinPrice) := by
  unfold OracleComp.liftComp
  apply work_forward (fun _ => coinPrice) _ _ _ _
    (work_of_total _ coinPrice (fun _ => le_refl _) work budget bounded)
  intro query
  change (liftM (HashSpec.query (.inl query)) : OracleComp HashSpec _).IsQueryBound
    coinPrice (fun query available => HashCost coinPrice query ≤ available)
    (fun query available => available - HashCost coinPrice query)
  exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _)

/-- Each private dictionary lookup pays at most 64 actual coins; every hit and failure continuation remains present. -/
theorem private_work (coinPrice : Nat) (sealPrice : ModifiedNonceAeadSealSpec.Domain → Nat)
    (suffix : Pqxdh.Bytes) (entry : AdaptiveCtxSharedReplay.Local) :
    WorkBound (LocalCost coinPrice sealPrice)
      (simulateQ forwardHash (AdaptiveCtxSharedReplay.localPrivate suffix entry)) (64 * coinPrice) := by
  apply work_forward (HashCost coinPrice) _ _ _ _
  · simpa only [AdaptiveCtxSharedReplay.localPrivate, bind_pure_comp, WorkBound,
      isQueryBound_map_iff] using lifted_work coinPrice
      (AdaptiveCtxSharedReplay.privateLookup suffix entry.2) 64
      (AdaptiveCtxSharedReplayBounds.private_lookup_uniform suffix entry.2)
  · intro query
    change (liftM (SealSpec.query (.inl query)) : OracleComp SealSpec _).IsQueryBound
      (HashCost coinPrice query) (fun query available => LocalCost coinPrice sealPrice query ≤ available)
      (fun query available => available - LocalCost coinPrice sealPrice query)
    exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _)

def SourceCost (coinPrice : Nat) (sealPrice : ModifiedNonceAeadSealSpec.Domain → Nat) : ReceiveSpec.Domain → Nat
  | .inl (.inl _) => coinPrice
  | .inl (.inr (.inl _)) => 64 * coinPrice
  | .inl (.inr (.inr input)) => sealPrice (CtxSealInput.toModifiedNonceAeadSealInput input) + 64 * coinPrice
  | .inr _ => 64 * coinPrice

/-- Each original sealing attempt submits its exact ordinary input at most once, followed by the actual private commitment work. -/
theorem sealing_work (coinPrice : Nat) (sealPrice : ModifiedNonceAeadSealSpec.Domain → Nat)
    (input : CtxSealInput) (entry : AdaptiveCtxSharedReplay.Local) :
    WorkBound (LocalCost coinPrice sealPrice) (compiledSeal input entry)
      (sealPrice (CtxSealInput.toModifiedNonceAeadSealInput input) + 64 * coinPrice) := by
  unfold compiledSeal
  split
  · trivial
  · apply work_bind (LocalCost coinPrice sealPrice) _ _ _ _
    · exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _)
    · intro reply
      cases reply with
      | none => trivial
      | some base =>
        simpa only [bind_pure_comp, WorkBound, isQueryBound_map_iff] using
          private_work coinPrice sealPrice (CtxSplitCache.outerSuffix input.nonce input.context base.tag) entry

/-- The local compiler retains all source attempts and charges their complete optional continuations. -/
theorem local_work (decode : RawDecoder) (coinPrice : Nat)
    (sealPrice : ModifiedNonceAeadSealSpec.Domain → Nat)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedReplay.Local) :
    WorkBound (LocalCost coinPrice sealPrice) ((compiledImpl decode query).run entry)
      (SourceCost coinPrice sealPrice query) := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [compiledImpl, StateT.run, bind_pure_comp, WorkBound, isQueryBound_map_iff, SourceCost]
    exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _)
  · simp only [compiledImpl, StateT.run, bind_pure_comp, WorkBound, isQueryBound_map_iff, SourceCost]
    exact (isQueryBound_query_iff _ _ _ _).mpr (le_refl _)
  · exact sealing_work coinPrice sealPrice input entry
  · simp only [compiledImpl, StateT.run, AdaptiveCtxSharedReplay.localRaw, SourceCost]
    split
    · trivial
    · simpa only [bind_pure_comp, simulateQ_map, WorkBound, isQueryBound_map_iff] using
        private_work coinPrice sealPrice _ _

/-- Index-specific seal prices preserve the exact originating index and plaintext under the shared backend. -/
def FamilySourceCost {count : Nat} (coinPrice : Nat)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat) : (SourceSpec count).Domain → Nat :=
  fun query => SourceCost coinPrice (sealPrice query.1) query.2

theorem compiler_work_step {count : Nat} (decode : Fin count → RawDecoder)
    (coinPrice : Nat) (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (query : (SourceSpec count).Domain) (state : State count) :
    WorkBound (IndexedCost coinPrice sealPrice) ((compilerImpl decode query).run state)
      (FamilySourceCost coinPrice sealPrice query) := by
  simpa only [compilerImpl, StateT.run, bind_pure_comp, WorkBound, isQueryBound_map_iff,
    FamilySourceCost] using work_compile (LocalCost coinPrice (sealPrice query.1))
      (IndexedCost coinPrice sealPrice) (backend query.1)
      ((compiledImpl (decode query.1) query.2).run (state.1 query.1)) _
      (local_work (decode query.1) coinPrice (sealPrice query.1) query.2 (state.1 query.1))
      (backend_work query.1 coinPrice sealPrice) state.2

/-- The full compiler carries its weighted budget through arbitrary adaptive replies and complete shared state. -/
theorem compiler_work {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (coinPrice : Nat) (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (client : OracleComp (SourceSpec count) Result) (budget : Nat)
    (bounded : WorkBound (FamilySourceCost coinPrice sealPrice) client budget) (state : State count) :
    WorkBound (IndexedCost coinPrice sealPrice) ((simulateQ (compilerImpl decode) client).run state) budget :=
  work_compile _ _ _ client budget bounded (compiler_work_step decode coinPrice sealPrice) state

/-- The actual ordinary privacy client inherits the same syntactic bound before any primitive interpretation. -/
theorem compiled_work {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (coinPrice : Nat) (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (client : OracleComp (SourceSpec count) Result) (budget : Nat)
    (bounded : WorkBound (FamilySourceCost coinPrice sealPrice) client budget) :
    WorkBound (IndexedCost coinPrice sealPrice) (compiledClient decode client) budget := by
  simpa only [compiledClient, retainedClient, WorkBound, isQueryBound_map_iff] using
    compiler_work decode coinPrice sealPrice client budget bounded (initialState count)

/-- An indicator-weighted budget is precisely the existing selective query cap. -/
theorem work_indicator {ι Result : Type} {spec : OracleSpec ι} (predicate : spec.Domain → Prop)
    [DecidablePred predicate] (client : OracleComp spec Result) (budget : Nat) :
    WorkBound (fun query => if predicate query then 1 else 0) client budget ↔
      client.IsQueryBoundP predicate budget := by
  apply isQueryBound_congr
  · intro query available
    by_cases selected : predicate query <;> simp [selected, Nat.succ_le_iff]
  · intro query available
    by_cases selected : predicate query <;> simp [selected]

/-- Multiplication changes only the accounting unit, and preserves every continuation. -/
theorem work_scale {ι Result : Type} {spec : OracleSpec ι} (cost : spec.Domain → Nat)
    (factor : Nat) (client : OracleComp spec Result) (budget : Nat) (bounded : WorkBound cost client budget) :
    WorkBound (fun query => factor * cost query) client (factor * budget) := by
  exact bounded.proj (fun available => factor * available)
    (fun query available allowed => Nat.mul_le_mul_left factor allowed)
    (fun query available _allowed => Nat.mul_sub_left_distrib factor available (cost query))

/-- Independently supplied caps combine on the same adaptive run and every possible reply. -/
theorem work_add {ι Result : Type} {spec : OracleSpec ι} (leftCost rightCost : spec.Domain → Nat)
    (client : OracleComp spec Result) (left right : Nat)
    (leftBound : WorkBound leftCost client left) (rightBound : WorkBound rightCost client right) :
    WorkBound (fun query => leftCost query + rightCost query) client (left + right) := by
  induction client using OracleComp.inductionOn generalizing left right with
  | pure value => trivial
  | query_bind query next ih =>
    rw [WorkBound, isQueryBound_query_bind_iff] at leftBound rightBound ⊢
    refine ⟨by omega, fun reply => ?_⟩
    have rest := ih reply _ _ (leftBound.2 reply) (rightBound.2 reply)
    rw [show left + right - (leftCost query + rightCost query) =
      left - leftCost query + (right - rightCost query) by omega]
    exact rest

open AdaptiveCtxQueryBounds (SourceUniform SourceWork SourceHash SourceSeal)

def SourceSealCost {count : Nat}
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat) : (SourceSpec count).Domain → Nat
  | ⟨index, .inl (.inr (.inr input))⟩ => sealPrice index (CtxSealInput.toModifiedNonceAeadSealInput input)
  | _ => 0

/-- The source bill retains the exact original seal price, separately from caller and hash/dictionary coins. -/
theorem source_aggregate {count : Nat} {Result : Type} (coinPrice : Nat)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (client : OracleComp (SourceSpec count) Result) (qUniform qWork qSealCost : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (sealBound : WorkBound (SourceSealCost sealPrice) client qSealCost) :
    WorkBound (FamilySourceCost coinPrice sealPrice) client
      (coinPrice * qUniform + (64 * coinPrice) * qWork + qSealCost) := by
  have uniform := work_scale _ coinPrice client qUniform ((work_indicator _ client qUniform).mpr uniformBound)
  have work := work_scale _ (64 * coinPrice) client qWork ((work_indicator _ client qWork).mpr workBound)
  have complete := work_add _ _ client _ _ (work_add _ _ client _ _ uniform work) sealBound
  have prices : FamilySourceCost coinPrice sealPrice = (fun query =>
      coinPrice * (if SourceUniform query.2 then 1 else 0) +
      (64 * coinPrice) * (if SourceWork query.2 then 1 else 0) + SourceSealCost sealPrice query) := by
    funext query
    rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;>
      simp [FamilySourceCost, SourceCost, SourceUniform, SourceWork, SourceSealCost, Nat.add_comm]
  rw [prices]
  exact complete

/-- Every actual weighted primitive client is bounded by the original source's independent all-reply caps. -/
theorem compiled_aggregate {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (coinPrice : Nat) (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (client : OracleComp (SourceSpec count) Result) (qUniform qWork qSealCost : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (sealBound : WorkBound (SourceSealCost sealPrice) client qSealCost) :
    WorkBound (IndexedCost coinPrice sealPrice) (compiledClient decode client)
      (coinPrice * qUniform + (64 * coinPrice) * qWork + qSealCost) :=
  compiled_work decode coinPrice sealPrice client _
    (source_aggregate coinPrice sealPrice client qUniform qWork qSealCost uniformBound workBound sealBound)

/-- Coin-free compiler prices preserve any exact index/input-dependent source sealing budget. -/
theorem compiled_seal_cost {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (sealPrice : Fin count → ModifiedNonceAeadSealSpec.Domain → Nat)
    (client : OracleComp (SourceSpec count) Result) (budget : Nat)
    (bounded : WorkBound (SourceSealCost sealPrice) client budget) :
    WorkBound (IndexedCost 0 sealPrice) (compiledClient decode client) budget := by
  apply compiled_work decode 0 sealPrice client budget
  have prices : FamilySourceCost 0 sealPrice = SourceSealCost sealPrice := by
    funext query
    rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;>
      simp [FamilySourceCost, SourceCost, SourceSealCost]
  simpa only [prices] using bounded

/-- The compiler's own uniform requests pay only actual caller and public/private dictionary sampling. -/
theorem compiled_uniform {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (client : OracleComp (SourceSpec count) Result) (qUniform qWork : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork) :
    (compiledClient decode client).IsQueryBoundP
      (fun query => IsModifiedNonceAeadUniformQuery query.2) (qUniform + 64 * qWork) := by
  have noSealCost : WorkBound (SourceSealCost (fun _ _ => 0)) client 0 := by
    have bounded := (work_indicator (fun _ => False) client 0).mpr (isQueryBoundP_false client 0)
    have prices : SourceSealCost (count := count) (fun _ _ => 0) = fun _ => 0 := by
      funext query
      rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;> rfl
    simpa only [prices, if_false] using bounded
  have bounded := compiled_aggregate decode 1 (fun _ _ => 0) client qUniform qWork 0 uniformBound workBound noSealCost
  have prices : IndexedCost (count := count) 1 (fun _ _ => 0) =
      fun query => if IsModifiedNonceAeadUniformQuery query.2 then 1 else 0 := by
    funext query
    rcases query with ⟨index, coin | input⟩ <;> rfl
  apply (work_indicator _ _ _).mp
  simpa only [prices, Nat.one_mul, Nat.mul_one, Nat.add_zero] using bounded

def SourceSeals {count : Nat} (selected : Fin count → ModifiedNonceAeadSealSpec.Domain → Prop) :
    (SourceSpec count).Domain → Prop
  | ⟨index, .inl (.inr (.inr input))⟩ => selected index (CtxSealInput.toModifiedNonceAeadSealInput input)
  | _ => False

def IndexedSeals {count : Nat} (selected : Fin count → ModifiedNonceAeadSealSpec.Domain → Prop) :
    (AdaptiveSealKeyFamily.Spec count).Domain → Prop
  | ⟨index, .inr input⟩ => selected index input
  | _ => False

instance {count : Nat} (selected : Fin count → ModifiedNonceAeadSealSpec.Domain → Prop)
    [∀ index, DecidablePred (selected index)] : DecidablePred (SourceSeals selected) :=
  fun query => by rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;> unfold SourceSeals <;> infer_instance

instance {count : Nat} (selected : Fin count → ModifiedNonceAeadSealSpec.Domain → Prop)
    [∀ index, DecidablePred (selected index)] : DecidablePred (IndexedSeals selected) :=
  fun query => by rcases query with ⟨index, coin | input⟩ <;> unfold IndexedSeals <;> infer_instance

/-- Any predicate on the original key index and complete sealing input has the same source attempt cap. -/
theorem compiled_seals {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (selected : Fin count → ModifiedNonceAeadSealSpec.Domain → Prop) [∀ index, DecidablePred (selected index)]
    (client : OracleComp (SourceSpec count) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (SourceSeals selected) budget) :
    (compiledClient decode client).IsQueryBoundP (IndexedSeals selected) budget := by
  have original := (work_indicator _ client budget).mpr bounded
  have sourcePrice : (fun query => if SourceSeals selected query then 1 else 0) =
      SourceSealCost (fun index input => if selected index input then 1 else 0) := by
    funext query
    rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;> rfl
  rw [sourcePrice] at original
  have compiled := compiled_seal_cost decode _ client budget original
  have targetPrice : IndexedCost 0 (fun index input => if selected index input then 1 else 0) =
      (fun query => if IndexedSeals selected query then 1 else 0) := by
    funext query
    rcases query with ⟨index, coin | input⟩ <;> rfl
  apply (work_indicator _ _ _).mp
  simpa only [targetPrice] using compiled

/-- Every forwarded seal retains exactly the original chosen plaintext bytes. -/
theorem compiled_bytes {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (client : OracleComp (SourceSpec count) Result) (budget : Nat)
    (bounded : WorkBound (SourceSealCost (fun _ input => input.plaintext.length)) client budget) :
    WorkBound (fun query => NonceAeadRandomQueryBounds.plaintextCost query.2) (compiledClient decode client) budget := by
  have compiled := compiled_seal_cost decode (fun _ input => input.plaintext.length) client budget bounded
  have prices : IndexedCost (count := count) 0 (fun _ input => input.plaintext.length) =
      (fun query => NonceAeadRandomQueryBounds.plaintextCost query.2) := by
    funext query
    rcases query with ⟨index, coin | input⟩ <;> rfl
  simpa only [prices] using compiled

/-- Original caller/hash/seal/raw budgets give the actual compiler coin, seal and chosen-plaintext ledger. -/
theorem compiled_global_caps {count : Nat} {Result : Type} (decode : Fin (count + 1) → RawDecoder)
    (client : OracleComp (SourceSpec (count + 1)) Result) (qUniform qHash qSeal qRaw qBytes : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (hashBound : client.IsQueryBoundP (fun query => SourceHash query.2) qHash)
    (sealBound : client.IsQueryBoundP (fun query => SourceSeal query.2) qSeal)
    (rawBound : client.IsQueryBoundP (fun query => IsRawQuery query.2) qRaw)
    (bytesBound : WorkBound (SourceSealCost (fun _ input => input.plaintext.length)) client qBytes) :
    (compiledClient decode client).IsQueryBoundP (fun query => IsModifiedNonceAeadUniformQuery query.2)
        (qUniform + 64 * (qHash + qSeal + qRaw)) ∧
      (compiledClient decode client).IsQueryBoundP (fun query => IsModifiedNonceAeadSealQuery query.2) qSeal ∧
      WorkBound (fun query => NonceAeadRandomQueryBounds.plaintextCost query.2) (compiledClient decode client) qBytes := by
  refine ⟨compiled_uniform decode client qUniform _ uniformBound
    (AdaptiveCtxSharedSourceBounds.source_work_bound client qHash qSeal qRaw hashBound sealBound rawBound), ?_,
    compiled_bytes decode client qBytes bytesBound⟩
  have sourcePredicate : SourceSeals (count := count + 1) (fun _ _ => True) =
      fun query => SourceSeal query.2 := by
    funext query
    rcases query with ⟨index, (coin | (hash | input)) | raw⟩ <;> rfl
  have targetPredicate : IndexedSeals (count := count + 1) (fun _ _ => True) =
      fun query => IsModifiedNonceAeadSealQuery query.2 := by
    funext query
    rcases query with ⟨index, coin | input⟩ <;> rfl
  have compiled := compiled_seals decode (fun _ _ => True) client qSeal (by simpa only [sourcePredicate] using sealBound)
  simpa only [targetPredicate] using compiled

/-- Any ordinary family cost with a fixed coin price retains its exact per-index source sealing price. -/
theorem compiled_cost {count : Nat} {Result : Type} (decode : Fin count → RawDecoder)
    (cost : (AdaptiveSealKeyFamily.Spec count).Domain → Nat) (coinPrice : Nat)
    (coins : ∀ index coin, cost ⟨index, .inl coin⟩ = coinPrice)
    (client : OracleComp (SourceSpec count) Result) (qUniform qWork qSealCost : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (sealBound : WorkBound (SourceSealCost (fun index input => cost ⟨index, .inr input⟩)) client qSealCost) :
    WorkBound cost (compiledClient decode client) (coinPrice * qUniform + (64 * coinPrice) * qWork + qSealCost) := by
  have prices : cost = IndexedCost coinPrice (fun index input => cost ⟨index, .inr input⟩) := by
    funext query
    rcases query with ⟨index, coin | input⟩
    · exact coins index coin
    · rfl
  rw [prices]
  exact compiled_aggregate decode coinPrice _ client qUniform qWork qSealCost uniformBound workBound sealBound

open AdaptiveSealKeyBounds (SelectionClass TargetClass SelectedCost SplitUniformCost SplitPlaintextCost)

/-- Selected privacy reductions retain source target-attempt/byte caps and every actual other-mode random body/tag byte. -/
theorem reduction_source_bounds {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec (count + 1)) Bool) (qUniform qWork qOther qSeal qBytes : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (otherBound : WorkBound (SourceSealCost (fun index input =>
      SelectedCost target (SplitUniformCost real) ⟨index, .inr input⟩)) client qOther)
    (sealBound : client.IsQueryBoundP (SourceSeals (fun index input =>
      SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery) ⟨index, .inr input⟩)) qSeal)
    (bytesBound : WorkBound (SourceSealCost (fun index input =>
      SelectedCost target SplitPlaintextCost ⟨index, .inr input⟩)) client qBytes) :
    (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client)).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery qSeal ∧
      (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client)).main.IsQueryBoundP
        IsModifiedNonceAeadUniformQuery (count * 32 + (qUniform + 64 * qWork + qOther)) ∧
      NonceAeadRandomQueryBounds.PlaintextBound
        (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client)).main qBytes := by
  apply AdaptiveSealKeyBounds.reduction_bounds target real c (compiledClient decode client)
    qSeal (qUniform + 64 * qWork + qOther) qBytes
  · have bounded := compiled_seals decode _ client qSeal sealBound
    have predicates : IndexedSeals (fun index input =>
        SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery) ⟨index, .inr input⟩) =
        SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery) := by
      funext query
      rcases query with ⟨index, coin | input⟩
      · cases chosen : finSuccEquiv' target index <;>
          simp [IndexedSeals, SelectionClass, chosen, TargetClass, IsModifiedNonceAeadSealQuery]
      · rfl
    simpa only [predicates] using bounded
  · have bounded := compiled_cost decode (SelectedCost target (SplitUniformCost real)) 1
      (by
        intro index coin
        cases chosen : finSuccEquiv' target index <;>
          simp [SelectedCost, chosen, SplitUniformCost, AdaptiveSealKeyBounds.localUniformCost])
      client qUniform qWork qOther uniformBound workBound otherBound
    simpa only [Nat.one_mul, Nat.mul_one] using bounded
  · have bounded := compiled_seal_cost decode _ client qBytes bytesBound
    have prices : IndexedCost 0 (fun index input => SelectedCost target SplitPlaintextCost ⟨index, .inr input⟩) =
        SelectedCost target SplitPlaintextCost := by
      funext query
      rcases query with ⟨index, coin | input⟩
      · cases chosen : finSuccEquiv' target index <;>
          simp [IndexedCost, SelectedCost, chosen, SplitPlaintextCost, NonceAeadRandomQueryBounds.plaintextCost]
      · rfl
    simpa only [prices] using bounded

/-- The complete ordinary real/random challengers include their actual key or body/tag sampling, with no resource transfer through evaluated equality. -/
theorem experiment_source_bounds {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec (count + 1)) Bool) (qUniform qWork qOther qSeal qBytes : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (otherBound : WorkBound (SourceSealCost (fun index input =>
      SelectedCost target (SplitUniformCost real) ⟨index, .inr input⟩)) client qOther)
    (sealBound : client.IsQueryBoundP (SourceSeals (fun index input =>
      SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery) ⟨index, .inr input⟩)) qSeal)
    (bytesBound : WorkBound (SourceSealCost (fun index input =>
      SelectedCost target SplitPlaintextCost ⟨index, .inr input⟩)) client qBytes) :
    (modifiedNonceAeadINDDollarRealExp c
      (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client))).IsTotalQueryBound
        (32 + (count * 32 + (qUniform + 64 * qWork + qOther))) ∧
      (modifiedNonceAeadINDDollarRandomExp
        (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client))).IsTotalQueryBound
        (count * 32 + (qUniform + 64 * qWork + qOther) + qBytes + 16 * qSeal) := by
  have bounds := reduction_source_bounds target real decode c client qUniform qWork qOther qSeal qBytes
    uniformBound workBound otherBound sealBound bytesBound
  constructor
  · unfold modifiedNonceAeadINDDollarRealExp
    apply isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 32)
    intro key
    simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound c key
        (AdaptiveSealMultiKeyPrivacy.reduction target real c (compiledClient decode client)).main _ bounds.2.1
  · exact NonceAeadRandomQueryBounds.randomExperiment_uniform_bound _ qBytes qSeal
      (count * 32 + (qUniform + 64 * qWork + qOther)) bounds.2.2 bounds.1 bounds.2.1

/-- The actual full family experiment pays for every sampled key, even unused random-mode keys, and every priced compiler operation. -/
theorem source_experiment_uniform {count : Nat} {Result : Type} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Result) (qUniform qWork qRandomSeal : Nat)
    (uniformBound : client.IsQueryBoundP (fun query => SourceUniform query.2) qUniform)
    (workBound : client.IsQueryBoundP (fun query => SourceWork query.2) qWork)
    (sealBound : WorkBound (SourceSealCost (fun index input =>
      AdaptiveSealKeyBounds.localUniformCost (real index) (.inr input))) client qRandomSeal) :
    (AdaptiveSealKeySelection.sourceGame real c (retainedClient decode client)).IsTotalQueryBound
      (count * 32 + (qUniform + 64 * qWork + qRandomSeal)) := by
  have bounded := compiled_cost decode (AdaptiveSealKeyBounds.FamilyCost real) 1
    (by intro index coin; rfl) client qUniform qWork qRandomSeal uniformBound workBound sealBound
  apply AdaptiveSealKeyBounds.source_uniform_bound real c (retainedClient decode client)
    (qUniform + 64 * qWork + qRandomSeal)
  simpa only [compiledClient, WorkBound, isQueryBound_map_iff, Nat.one_mul, Nat.mul_one] using bounded

end BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_bind

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_compile' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_compile

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_forward' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_forward

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_of_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_of_total

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.coin_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.coin_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.backend_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.backend_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.lifted_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.lifted_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.private_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.private_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.sealing_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.sealing_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.local_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.local_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiler_work_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiler_work_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiler_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiler_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_indicator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_indicator

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_scale' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_scale

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.work_add

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.source_aggregate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.source_aggregate

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_aggregate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_aggregate

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_seal_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_seal_cost

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_seals

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_bytes

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_global_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_global_caps

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.compiled_cost

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.reduction_source_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.reduction_source_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.experiment_source_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.experiment_source_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.source_experiment_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompilerBounds.source_experiment_uniform
