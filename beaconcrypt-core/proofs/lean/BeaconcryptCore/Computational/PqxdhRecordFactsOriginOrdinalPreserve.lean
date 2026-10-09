-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices

/-! Exact selected dictionary preservation after the last selected source seal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsPrivateCacheFamily (erasedKeyed localLens)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing)
variable {n : Nat}

/-- Support-wise invariance through any adaptive program with zero forbidden callbacks. -/
theorem program_preserves {ι : Type} {spec : OracleSpec ι} {S X V : Type}
    (service : QueryImpl spec (StateT S ProbComp)) (blocked : spec.Domain → Prop)
    [DecidablePred blocked] (observe : S → V)
    (step : ∀ query, ¬blocked query → ∀ state result,
      result ∈ support ((service query).run state) → observe result.2 = observe state)
    (work : OracleComp spec X) (noBlocked : work.IsQueryBoundP blocked 0)
    (state : S) (result : X × S)
    (supported : result ∈ support ((simulateQ service work).run state)) :
    observe result.2 = observe state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ rfl
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noBlocked
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, finished⟩ := supported
    exact (ih inner.1 (noBlocked.2 inner.1) inner.2 finished).trans
      (step query noBlocked.1 state inner reached)

/-- Every actual erased service other than a selected seal preserves that dictionary exactly. -/
theorem erased_service (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (noSeal : ¬IsTargetSealing target query) (state : CtxPrivate n)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter
      modes decode crypto base writer replace query).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals := by
  by_cases sealed : ∃ pending, query = .sealing pending
  · obtain ⟨pending, rfl⟩ := sealed
    exact congrArg (fun entry => entry.1.successfulSeals)
      (PqxdhRecordFactsOriginOrdinalServices.service_sealing_other modes decode crypto base writer replace
        pending state result supported target (Ne.symm noSeal))
  · exact PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes decode crypto base writer replace
      query (fun pending same => sealed ⟨pending, same⟩) state result supported target

/-- The literal muted raw endpoint keeps the selected dictionary while changing only its optional replay answer and actual raw instrumentation. -/
theorem muted_raw (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhRecordFactsPrivateCache.State)
    (result : Option Pqxdh.Bytes × PqxdhRecordFactsPrivateCache.State)
    (supported : result ∈ support ((PqxdhRecordFactsOriginMute.raw decode raw).run state)) :
    result.2.1.1.successfulSeals = state.1.1.successfulSeals := by
  cases parsed : decode raw <;>
    simp only [PqxdhRecordFactsOriginMute.raw, PqxdhRecordFactsPrivateCache.rawBase,
      parsed, StateT.run, map_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals exact supported ▸ rfl

/-- A muted keyed raw request retains the selected dictionary for either queried coordinate. -/
theorem muted_keyed_raw (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (selected : Label n) (raw : Pqxdh.Bytes)
    (state : CtxPrivate n) (result : Option Pqxdh.Bytes × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto
      (selected, .inr raw)).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals := by
  by_cases same : selected = target
  · subst selected
    simp only [PqxdhRecordFactsOriginMuteFamily.keyed, StateT.run, ite_true,
      LazyOracleDiscard.StateLens.lift, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    simpa only [localLens, Function.update_self] using
      muted_raw decode raw ((localLens target).get state) inner reached
  · simp only [PqxdhRecordFactsOriginMuteFamily.keyed, StateT.run, same, ite_false] at supported
    exact PqxdhRecordFactsOriginOrdinalServices.keyedRaw_seals modes decode crypto selected raw state result supported target

private theorem apply_map {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]; rfl

/-- Literal muted hidden opening retains the selected dictionary across every parser and optional plaintext branch. -/
theorem muted_opening (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto)
      (hiddenOpening seeds table pending)).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals := by
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ rfl
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ rfl
    · split at supported
      · simp only [simulateQ_map, simulateQ_spec_query, StateT.run, apply_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact muted_keyed_raw target modes decode crypto _ _ state inner reached
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        exact supported ▸ rfl

/-- A muted seal on another coordinate is exactly the original erased hidden service. -/
theorem muted_sealing_eq (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Sealing n) (different : pending.material ≠ target)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    simulateQ (PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto)
      ((hiddenSealing writer table replace pending).run frames) =
      simulateQ (erasedKeyed modes decode crypto)
        ((hiddenSealing writer table replace pending).run frames) := by
  simp only [hiddenSealing, StateT.run]
  split
  · simp only [simulateQ_bind, simulateQ_spec_query]
    have keyedSame (input : CtxSealInput) : PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto
        (pending.material, .inl (.inr (.inr input))) =
        erasedKeyed modes decode crypto (pending.material, .inl (.inr (.inr input))) := by
      funext state
      change (if pending.material = target then _ else _) = _
      simp only [different, ite_false, StateT.run]
    rw [keyedSame]
    apply bind_congr
    intro reply
    cases reply <;> rfl
  · rfl

/-- Every muted source service other than a selected seal preserves the exact selected dictionary. -/
theorem muted_service (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (noSeal : ¬IsTargetSealing target query) (state : CtxPrivate n)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsOriginMuteServices.interpreter target
      modes decode crypto base writer replace query).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals := by
  cases query
  case opening pending =>
    change result ∈ support ((simulateQ (PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto)
      (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state) at supported
    exact muted_opening target modes decode crypto _ _ pending state result supported
  case sealing pending =>
    simp only [PqxdhRecordFactsOriginMuteServices.interpreter, StateT.run,
      bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    change inner ∈ support ((simulateQ (PqxdhRecordFactsOriginMuteFamily.keyed target modes decode crypto)
      ((hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state) at reached
    rw [muted_sealing_eq target modes decode crypto writer replace _ pending noSeal] at reached
    exact congrArg (fun entry => entry.1.successfulSeals)
      (PqxdhRecordFactsOriginOrdinalServices.hiddenSealing_other modes decode crypto writer replace
        _ pending _ state inner reached target (Ne.symm noSeal))
  all_goals
    simp only [PqxdhRecordFactsOriginMuteServices.interpreter, onBase, StateT.run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    rfl

/-- Every supported adaptive erased continuation with no later selected seal retains the exact starting selected dictionary. -/
theorem erased_program {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter
      modes decode crypto base writer replace) work).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals :=
  program_preserves _ (IsTargetSealing target) (fun state => (state.keys target).1.successfulSeals)
    (erased_service target modes decode crypto base writer replace) work noSeal state result supported

/-- Every supported adaptive muted continuation with no later selected seal retains the exact starting selected dictionary. -/
theorem muted_program {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsOriginMuteServices.interpreter target
      modes decode crypto base writer replace) work).run state)) :
    (result.2.keys target).1.successfulSeals = (state.keys target).1.successfulSeals :=
  program_preserves _ (IsTargetSealing target) (fun state => (state.keys target).1.successfulSeals)
    (muted_service target modes decode crypto base writer replace) work noSeal state result supported

/-- The same service invariant holds at every supported adaptive source prefix, without requiring a later completion. -/
theorem reach_preserves {X V : Type}
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (blocked : Service n → Prop) [DecidablePred blocked] (observe : CtxPrivate n → V)
    (step : ∀ query, ¬blocked query → ∀ state result,
      result ∈ support ((service query).run state) → observe result.2 = observe state)
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (noBlocked : initial.IsQueryBoundP blocked 0)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach service initial start past0 work state past) :
    work.IsQueryBoundP blocked 0 ∧ observe state = observe start := by
  induction reached with
  | initial => exact ⟨noBlocked, rfl⟩
  | @step query next before history reply prior supported ih =>
    obtain ⟨bound, kept⟩ := ih
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at bound
    exact ⟨bound.2 reply.1, (step query bound.1 before reply supported).trans kept⟩

/-- A supported prefix of the actual erased continuation retains its exact selected dictionary and residual zero-seal bound. -/
theorem erased_reach {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (noSeal : initial.IsQueryBoundP (IsTargetSealing target) 0)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach
      (PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter modes decode crypto base writer replace)
      initial start past0 work state past) :
    work.IsQueryBoundP (IsTargetSealing target) 0 ∧
      (state.keys target).1.successfulSeals = (start.keys target).1.successfulSeals :=
  reach_preserves _ (IsTargetSealing target) (fun state => (state.keys target).1.successfulSeals)
    (erased_service target modes decode crypto base writer replace) initial start past0 noSeal work state past reached

/-- A supported prefix of the muted continuation retains its exact selected dictionary and residual zero-seal bound. -/
theorem muted_reach {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (noSeal : initial.IsQueryBoundP (IsTargetSealing target) 0)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach
      (PqxdhRecordFactsOriginMuteServices.interpreter target modes decode crypto base writer replace)
      initial start past0 work state past) :
    work.IsQueryBoundP (IsTargetSealing target) 0 ∧
      (state.keys target).1.successfulSeals = (start.keys target).1.successfulSeals :=
  reach_preserves _ (IsTargetSealing target) (fun state => (state.keys target).1.successfulSeals)
    (muted_service target modes decode crypto base writer replace) initial start past0 noSeal work state past reached

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.program_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.program_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_keyed_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_keyed_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_sealing_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_sealing_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.reach_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.reach_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.erased_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve.muted_reach
