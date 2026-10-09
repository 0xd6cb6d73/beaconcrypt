-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal

/-! Exact dictionary changes at callbacks of the actual erased source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsPrivateCacheFamily (erasedKeyed)
open PqxdhRecordFactsPrivateCacheSource
open PqxdhRecordFactsPrivateCacheCompiler (base compile)
variable {n : Nat}

private theorem apply_map {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]; rfl

/-- Removing a discarded raw suffix completion retains the exact local seal dictionary. -/
theorem localRaw_seals (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (raw : Pqxdh.Bytes) (state : PqxdhRecordFactsPrivateCache.State)
    (result : Option Pqxdh.Bytes × PqxdhRecordFactsPrivateCache.State)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr raw)).run state)) :
    result.2.1.1.successfulSeals = state.1.1.successfulSeals := by
  cases parsed : decode raw <;>
    simp only [PqxdhRecordFactsPrivateCacheRandom.erased,
      PqxdhRecordFactsPrivateCacheRandom.modePointed, StateT.run, apply_map,
      PqxdhRecordFactsPrivateCache.rawBase, parsed, map_pure, support_pure, Set.mem_singleton_iff,
      Prod.map, id_eq] at supported
  all_goals exact supported ▸ rfl

/-- Every erased keyed raw reply keeps every coordinate's full seal dictionary. -/
theorem keyedRaw_seals (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (selected : Label n) (raw : Pqxdh.Bytes) (state : CtxPrivate n)
    (result : Option Pqxdh.Bytes × CtxPrivate n)
    (supported : result ∈ support ((erasedKeyed modes decode crypto (selected, .inr raw)).run state)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (state.keys label).1.successfulSeals := by
  obtain ⟨localState, reached, keys, baseKept⟩ := erasedKeyed_witness modes decode crypto (selected, .inr raw) state result supported
  intro label
  by_cases same : label = selected
  · subst label
    simp only [keys, Function.update_self]
    exact localRaw_seals decode crypto (materialAt state.base.chain selected).1 (modes selected)
      raw (state.keys selected, state.base.primitive.2) (result.1, localState) reached
  · rw [keys, Function.update_of_ne same]

/-- The literal hidden opening preserves all seal dictionaries through parser, getter, validation and optional plaintext branches. -/
theorem hiddenOpening_seals (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (erasedKeyed modes decode crypto)
      (hiddenOpening seeds table pending)).run state)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (state.keys label).1.successfulSeals := by
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ fun _ => rfl
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ fun _ => rfl
    · split at supported
      · simp only [simulateQ_map, simulateQ_spec_query, StateT.run, apply_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact keyedRaw_seals modes decode crypto _ _ state inner reached
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        exact supported ▸ fun _ => rfl

/-- Every non-sealing source service preserves all seal dictionaries, while its complete base work still executes. -/
theorem service_nonSeal (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (notSealing : ∀ pending, query ≠ .sealing pending) (state : CtxPrivate n)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter modes decode crypto
      impl writer replace query).run state)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (state.keys label).1.successfulSeals := by
  change result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
    (compile writer replace query)).run state) at supported
  cases query
  case opening pending =>
    rw [erased_opening] at supported
    exact hiddenOpening_seals modes decode crypto _ _ pending state result supported
  case sealing pending => exact False.elim (notSealing pending rfl)
  all_goals
    simp only [compile, simulateQ_spec_query, erased_base, base, onBase, StateT.run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact fun _ => rfl

private theorem apply_bind {S A B : Type} (work : StateT S ProbComp A)
    (next : A → StateT S ProbComp B) (state : S) :
    (work >>= next) state = (work state >>= fun result => next result.1 result.2) := rfl

private theorem apply_pure {S A : Type} (value : A) (state : S) :
    (pure value : StateT S ProbComp A) state = pure (value, state) := rfl

/-- A hidden sealing callback changes no other material coordinate, including when its writer fails. -/
theorem hiddenSealing_other (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Sealing n) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (state : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftLoggedAdapters.Frames) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (erasedKeyed modes decode crypto)
      ((hiddenSealing writer table replace pending).run frames)).run state))
    (label : Label n) (different : label ≠ pending.material) : result.2.keys label = state.keys label := by
  simp only [hiddenSealing, StateT.run] at supported
  split at supported
  · simp only [simulateQ_bind, simulateQ_spec_query, apply_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, finished⟩ := supported
    have retained := erasedKeyed_other modes decode crypto _ state inner reached label different
    cases reply : inner.1 <;>
      simp only [reply, simulateQ_pure, apply_pure, support_pure, Set.mem_singleton_iff] at finished
    all_goals exact finished ▸ retained
  · simp only [simulateQ_pure, apply_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ rfl

/-- Complete sealing-service buffer reinstallation retains every other coordinate's full local state. -/
theorem service_sealing_other (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter modes decode crypto
      impl writer replace (.sealing pending)).run state))
    (label : Label n) (different : label ≠ pending.material) : result.2.keys label = state.keys label := by
  change result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto (base impl))
    (compile writer replace (.sealing pending))).run state) at supported
  rw [erased_sealing] at supported
  simp only [bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact hiddenSealing_other modes decode crypto writer replace _ pending _ state inner reached label different

/-- A newly present seal entry can only come from the literal sealing callback at that exact material coordinate. -/
theorem insertion_sealing (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (state : CtxPrivate n) (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter modes decode crypto
      impl writer replace query).run state)) (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry ∉ (state.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.keys label).1.successfulSeals) :
    ∃ pending, query = .sealing pending ∧ pending.material = label := by
  by_cases sealed : ∃ pending, query = .sealing pending
  · obtain ⟨pending, rfl⟩ := sealed
    refine ⟨pending, rfl, ?_⟩
    by_contra different
    have retained := service_sealing_other modes decode crypto impl writer replace pending state result supported
      label (Ne.symm different)
    exact absent (by simpa only [retained] using present)
  · have retained := service_nonSeal modes decode crypto impl writer replace query
      (fun pending same => sealed ⟨pending, same⟩) state result supported label
    exact False.elim (absent (retained ▸ present))

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.localRaw_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.localRaw_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.keyedRaw_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.keyedRaw_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.hiddenOpening_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.hiddenOpening_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.service_nonSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.service_nonSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.hiddenSealing_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.hiddenSealing_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.service_sealing_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.service_sealing_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.insertion_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices.insertion_sealing
