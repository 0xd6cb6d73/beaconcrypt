import BeaconcryptCore.Computational.RawCtxSourceSharedRom
import BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried

/-!
The actual ordered private-table interpreter is compiled before the selected cut using its original full-output draw, exact cache lookup, cursor transition, real public HKDF and one forwarded commitment ROM. No selected message key is needed by this compiler. The private retained table and the ROM cache remain distinct, and both complete states survive execution.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveSharedRom
open CtxRomAuth AdaptiveCtxSharedHash PqxdhJointKdfGame RawCtxSelectiveChainGame

noncomputable def coins : QueryImpl unifSpec (OracleComp HashSpec) := fun query => HashSpec.query (.inl query)

/-- Every private-prefix draw forwards its original finite uniform request and preserves the entire hash cache. -/
theorem coins_complete {Result : Type} (work : ProbComp Result) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (simulateQ coins work)).run cache = (fun result => (result, cache)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, coins, StateT.run_bind]
    change (do
      let result ← (hashImpl (.inl query)).run cache
      (simulateQ hashImpl (simulateQ coins (next result.1))).run result.2) = _
    rw [AdaptiveCtxSharedModes.hash_uniform_step]
    change (((fun answer : Fin (query + 1) => (answer, cache)) <$>
      (unifSpec.query query : ProbComp (Fin (query + 1)))) >>= fun result =>
      (simulateQ hashImpl (simulateQ coins (next result.1))).run result.2) = _
    rw [bind_map_left]
    simpa only [map_bind] using (bind_congr fun answer => ih answer)

abbrev Local (A : Type) := A × Store

def attach {A : Type} (state : Local A) (cache : CtxRO.QueryCache) : RawCtxPendingSelectiveFamily.State A :=
  ((state.1, cache), state.2)

noncomputable def handler {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat) :
    QueryImpl RawCtxSelectiveKdfFamily.FamilySpec (StateT (Local A) (OracleComp HashSpec))
  | .inl query => fun state => do
      let reply ← RawCtxSourceSharedRom.backend source writer query
      pure (reply, state)
  | .inr request => fun state => do
      let result ← simulateQ coins (privateStep source stage request state.2)
      pure (result.1, (state.1, result.2))

/-- One actual selective callback retains its complete private table, cursor and ROM cache, including hit and collision branches. -/
theorem step {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (query : RawCtxSelectiveKdfFamily.FamilySpec.Domain)
    (state : Local A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((handler source writer stage query).run state)).run cache =
      (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer) query).run (attach state cache) := by
  cases query with
  | inl query =>
    change (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((fun answer => (answer, state)) <$> RawCtxSourceSharedRom.backend source writer query)).run cache = _
    simp only [simulateQ_map, StateT.run_map]
    change _ = (fun answer => (answer.1, (answer.2, state.2))) <$>
      (RawCtxProtocolBackend.backend source writer query).run (state.1, cache)
    rw [RawCtxSourceSharedRom.backend_step]
    simp only [Functor.map_map, attach]
  | inr request =>
    change (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((fun answer => (answer.1, (state.1, answer.2))) <$>
        simulateQ coins (privateStep source stage request state.2))).run cache = _
    rw [simulateQ_map, StateT.run_map, coins_complete]
    simp only [RawCtxSelectiveChainGame.handler, StateT.run, bind_pure_comp, Functor.map_map, attach]
    rfl

/-- The complete adaptive staged program executes the exact source table and cursor while all earlier commitment work is forwarded into the retained ROM. -/
theorem program {A Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (client : OracleComp RawCtxSelectiveKdfFamily.FamilySpec Result)
    (state : Local A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((simulateQ (handler source writer stage) client).run state)).run cache =
      (simulateQ (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer)) client).run
        (attach state cache) := by
  have perQuery : ∀ query before,
      Prod.map id (fun combined : Local A × CtxRO.QueryCache => attach combined.1 combined.2) <$>
        (((hashImpl.mapStateTBase (handler source writer stage)).flattenStateT query).run before) =
        (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer) query).run
          (attach before.1 before.2) := by
    intro query before
    simpa only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq] using
      step source writer stage query before.1 before.2
  have whole := map_run_simulateQ_eq_of_query_map_eq
    ((hashImpl.mapStateTBase (handler source writer stage)).flattenStateT)
    (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer))
    (fun combined : Local A × CtxRO.QueryCache => attach combined.1 combined.2) perQuery client (state, cache)
  have unpacked := congrArg (fun work => (fun result => (result.1.1, attach result.1.2 result.2)) <$> work)
    (simulateQ_mapStateTBase_run_eq_map_flattenStateT hashImpl (handler source writer stage) client state cache)
  simp only [Functor.map_map, Prod.map_def, id_eq] at unpacked whole
  exact unpacked.trans whole

noncomputable def pendingCode {S B : Nat} :
    QueryImpl (RawCtxPendingSelectiveFamily.Spec S B) (OracleComp RawCtxServerServices.BackendSpec) :=
  RawCtxPendingFamilyNative.handler (QueryImpl.id' RawCtxServerServices.BackendSpec)

/-- The actual pending source callback is a literal native backend program, including optional reveal replies and both record directions. -/
theorem pending_natural {S B : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) :
    simulateQ backend (pendingCode query) = RawCtxPendingFamilyNative.handler backend query := by
  rcases query with ((receiving | opening) | ((sending | sealing) | query)) | query
  all_goals simp [pendingCode, RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
    RawCtxPendingNativeCalls.pending, RawCtxPendingNativeCalls.original, RawCtxPendingOwnerQueries.erase,
    RawCtxPendingNativeCalls.receive, RawCtxPendingNativeCalls.send, QueryImpl.compose,
    RawCtxGenericFamilyRead.nativeReader, QueryImpl.simulateQ_compose]

noncomputable def pending {A : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat) :
    QueryImpl (RawCtxPendingSelectiveFamily.Spec S B) (StateT (Local A) (OracleComp HashSpec)) :=
  (handler source writer stage ∘ₛ RawCtxSelectiveKdfFamily.compiler) ∘ₛ pendingCode

/-- The literal source pending callback uses the same compiled stage and full ROM cache; no equality premise on completed source outcomes is supplied. -/
theorem pending_step {A : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat) (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain)
    (state : Local A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((pending source writer stage query).run state)).run cache =
      (RawCtxPendingSelectiveFamily.handler source writer stage query).run (attach state cache) := by
  simp only [pending, QueryImpl.compose, QueryImpl.simulateQ_compose]
  rw [program]
  change (simulateQ (RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend source writer))
    (simulateQ RawCtxSelectiveKdfFamily.compiler (pendingCode query))).run (attach state cache) = _
  rw [← QueryImpl.simulateQ_compose, pending_natural]
  rfl

/-- The entire actual enriched role/reveal prefix preserves all original pending native payloads, replies, private table, selected cursor and shared ROM. -/
theorem pending_program {A Result : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : Local A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, attach result.1.2 result.2)) <$>
      (simulateQ hashImpl ((simulateQ (pending source writer stage) client).run state)).run cache =
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run (attach state cache) := by
  simp only [pending, QueryImpl.simulateQ_compose]
  rw [program]
  simp only [← QueryImpl.simulateQ_compose]
  have callbacks : RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) ∘ₛ
      (RawCtxSelectiveKdfFamily.compiler ∘ₛ pendingCode) = RawCtxPendingSelectiveFamily.handler (serverCount := S) (beaconCount := B) source writer stage := by
    funext query
    simp only [QueryImpl.compose, ← QueryImpl.simulateQ_compose]
    exact pending_natural _ query
  rw [callbacks]

/-- Explicit prefix coins make no hash query. -/
theorem coins_no_hash {Result : Type} (work : ProbComp Result) :
    (simulateQ coins work).IsQueryBoundP (HashClass true) 0 := by
  apply RawCtxSourceOpen.simulate_bound coins (fun _ => False) (HashClass true) work 0 (isQueryBoundP_false work 0)
  intro query
  change (HashSpec.query (.inl query) : OracleComp HashSpec _).IsQueryBoundP (HashClass true) 0
  exact (isQueryBoundP_query_iff (spec := HashSpec) (p := HashClass true) (.inl query) 0).2 (by simp [HashClass])

/-- Every original uniform draw remains exactly one forwarded uniform request, with no hidden random work. -/
theorem coins_bound {Result : Type} (work : ProbComp Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (simulateQ coins work).IsQueryBoundP (HashClass false) bound := by
  apply RawCtxSourceOpen.simulate_bound coins (fun _ => True) (HashClass false) work bound
    ((isQueryBoundP_true_iff work bound).2 bounded)
  intro query
  change (HashSpec.query (.inl query) : OracleComp HashSpec _).IsQueryBoundP (HashClass false) 1
  exact (isQueryBoundP_query_iff (spec := HashSpec) (p := HashClass false) (.inl query) 1).2 (by simp [HashClass])

/-- A private staged lookup uses no hash and at most the actual76-byte full-output draw. Hits and unselected misses keep their existing cheaper branches. -/
theorem private_bills (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : PqxdhJointKdf.JointKdfAddress) (store : Store) :
    (simulateQ coins (privateStep source stage request store)).IsQueryBoundP (HashClass true) 0 ∧
    (simulateQ coins (privateStep source stage request store)).IsQueryBoundP (HashClass false) 76 :=
  ⟨coins_no_hash _, coins_bound _ 76 (private_uniform source stage request store)⟩

end BeaconcryptCore.Computational.RawCtxSelectiveSharedRom


/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_natural

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.pending_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_no_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_no_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.coins_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.private_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSharedRom.private_bills
