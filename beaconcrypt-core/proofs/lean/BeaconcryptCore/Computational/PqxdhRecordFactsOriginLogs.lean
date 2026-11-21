-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol

/-! Removing only write-only source frame logs retains the full operational result and all primitive state. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs
open PqxdhRecordLiftProtocol PqxdhRecordLiftLoggedAdapters
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Blank only the two write-only frame logs, retaining every operational private field and counter. -/
def clearPrivate (state : Private n) : Private n :=
  { state with produced := [], pending := [] }

/-- The corresponding projection retains all coordinate dictionaries and caches. -/
def clearCtx (state : PqxdhRecordLiftIdeal.CtxPrivate n) : PqxdhRecordLiftIdeal.CtxPrivate n :=
  { state with base := clearPrivate state.base }

/-- Forgetting the writer log preserves each actual native primitive call, reply and complete primitive state. -/
theorem logged_program_forget {PrimitiveState Result : Type} (native : Native PrimitiveState)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (primitive : PrimitiveState) (frames : Frames) :
    Prod.map id Prod.fst <$> (simulateQ (loggedNative native) client).run (primitive, frames) =
      (simulateQ native client).run primitive := by
  rw [program_logged, Functor.map_map]
  have same := congrArg (fun work => (simulateQ native work).run primitive)
    (PqxdhDeploymentNative.logged_forget client frames)
  simpa only [simulateQ_map, StateT.run_map, Prod.map, id_eq, swapResult] using same

/-- A complete native record continuation depends on neither source log, retaining all actual primitive effects. -/
theorem withNative_logs {Result : Type} (native : Native PqxdhRecordLiftWorld.Primitive)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : Private n) :
    Prod.map id clearPrivate <$>
      (withRecord (primitiveWork (simulateQ (loggedNative native) client))).run state =
      (fun reply => (reply.1, { clearPrivate state with primitive := reply.2 })) <$>
        (simulateQ native client).run state.primitive := by
  have same := congrArg (fun work => (fun reply =>
    (reply.1, { clearPrivate state with primitive := reply.2 })) <$> work)
    (logged_program_forget native client state.primitive state.pending)
  simpa only [withRecord, primitiveWork, recordState, putRecord, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, clearPrivate] using same

/-- Resetting only the input source logs has no effect after the same output projection. -/
theorem withNative_clear {Result : Type} (native : Native PqxdhRecordLiftWorld.Primitive)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : Private n) :
    Prod.map id clearPrivate <$>
      (withRecord (primitiveWork (simulateQ (loggedNative native) client))).run state =
      Prod.map id clearPrivate <$>
        (withRecord (primitiveWork (simulateQ (loggedNative native) client))).run (clearPrivate state) := by
  rw [withNative_logs, withNative_logs]
  rfl

/-- Actual counterless base services retain the same reply and every operational field when only source logs are blanked. -/
theorem interpreter_clear (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : (ServiceSpec n).Domain)
    (notOpening : ∀ pending, query ≠ .opening pending)
    (notSealing : ∀ pending, query ≠ .sealing pending) (state : Private n) :
    Prod.map id clearPrivate <$>
      (PqxdhRecordFactsCounterProtocol.interpreter ideal setup codec query).run state =
      Prod.map id clearPrivate <$>
        (PqxdhRecordFactsCounterProtocol.interpreter ideal setup codec query).run (clearPrivate state) := by
  cases query
  case knownSend kernel context =>
    simp only [PqxdhRecordFactsCounterProtocol.interpreter,
      PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose]
    exact withNative_clear _ _ _
  case knownReceive kernel target context =>
    simpa only [PqxdhRecordFactsCounterProtocol.interpreter,
      PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose] using
      (withNative_clear (PqxdhRecordFactsCounter.primitives setup codec)
        (simulateQ RawCtxMixedOwner.receiveAdapter
          (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))) state)
  case lookup coordinate =>
    simp only [PqxdhRecordFactsCounterProtocol.interpreter, withRecord,
      PqxdhRecordFactsCounter.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
      recordState, putRecord, StateT.run, bind_pure_comp,
      Functor.map_map, Prod.map, id_eq, clearPrivate]
    simp only [Functor.map, StateT.map, PqxdhRecordLiftLoggedAdapters.liftLookup, bind_pure_comp]
    simp only [PFunctor.FreeM.map_eq_map, Functor.map_map]
    rfl
  case opening pending => exact False.elim (notOpening pending rfl)
  case sealing pending => exact False.elim (notSealing pending rfl)
  all_goals simp only [PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordFactsCounterProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
    map_pure, Prod.map, id_eq, clearPrivate, publish]

/-- Blanking the two source logs is idempotent. -/
theorem clearPrivate_idempotent (state : Private n) : clearPrivate (clearPrivate state) = clearPrivate state := rfl

/-- The whole-coordinate projection is idempotent and never edits a coordinate dictionary. -/
theorem clearCtx_idempotent (state : PqxdhRecordLiftIdeal.CtxPrivate n) :
    clearCtx (clearCtx state) = clearCtx state := rfl

/-- Native/effect/uniform counters, shared cache, both seeds, evolving table and every key state remain exact. -/
theorem clearCtx_retained (state : PqxdhRecordLiftIdeal.CtxPrivate n) :
    (clearCtx state).base.primitive = state.base.primitive ∧
      (clearCtx state).base.seeds = state.base.seeds ∧
      (clearCtx state).base.chain = state.base.chain ∧ (clearCtx state).keys = state.keys :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Log projection commutes with any explicit coordinate-state update, including a selected dictionary/cache projection. -/
theorem clearCtx_keys (state : PqxdhRecordLiftIdeal.CtxPrivate n)
    (keys : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyEntry) :
    clearCtx { state with keys := keys } = { clearCtx state with keys := keys } := rfl

/-- The base-service log law frames every coordinate state unchanged. -/
theorem onBase_clear {Result : Type} (work : StateT (Private n) ProbComp Result)
    (law : ∀ base, Prod.map id clearPrivate <$> work.run base =
      Prod.map id clearPrivate <$> work.run (clearPrivate base))
    (state : PqxdhRecordLiftIdeal.CtxPrivate n) :
    Prod.map id clearCtx <$> (PqxdhRecordLiftIdeal.onBase work).run state =
      Prod.map id clearCtx <$> (PqxdhRecordLiftIdeal.onBase work).run (clearCtx state) := by
  have same := congrArg (fun computation => (fun reply =>
    (reply.1, { state with base := reply.2 })) <$> computation) (law state.base)
  simpa only [PqxdhRecordLiftIdeal.onBase, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, clearCtx] using same

/-- The actual counterless CTX base endpoint has the same reply and full projected poststate for every ambient source service. -/
theorem base_clear (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : (ServiceSpec n).Domain)
    (notOpening : ∀ pending, query ≠ .opening pending)
    (notSealing : ∀ pending, query ≠ .sealing pending)
    (state : PqxdhRecordLiftIdeal.CtxPrivate n) :
    Prod.map id clearCtx <$> (PqxdhRecordLiftIdeal.onBase
      (PqxdhRecordFactsCounterProtocol.interpreter ideal setup codec query)).run state =
      Prod.map id clearCtx <$> (PqxdhRecordLiftIdeal.onBase
        (PqxdhRecordFactsCounterProtocol.interpreter ideal setup codec query)).run (clearCtx state) :=
  onBase_clear _ (interpreter_clear ideal setup codec query notOpening notSealing) state

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.logged_program_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.logged_program_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.withNative_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.withNative_logs

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.withNative_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.withNative_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.interpreter_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.interpreter_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearPrivate_idempotent' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearPrivate_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_idempotent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_retained' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_keys' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.clearCtx_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.onBase_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.onBase_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.base_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs.base_clear
