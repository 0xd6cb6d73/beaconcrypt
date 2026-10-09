-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCounter

/-! Whole protocol service projection of uniform instrumentation, preserving native costs and every operational reply. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol
open PqxdhRecordFactsCounter PqxdhRecordLiftProtocol
open PqxdhRecordLiftWorld (Primitive)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Uninstrumented sampling leaves all private fields in place. -/
def sampled {Result : Type} (work : ProbComp Result) : StateT (Private n) ProbComp Result :=
  fun state => (fun result => (result, state)) <$> work

/-- The same source service interpreter with the uniform-counting wrappers removed. -/
noncomputable def interpreter (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)
  | .allocate slot => fun secret => do
      let result ← (sampled ((PqxdhRecordLiftLazyTable.impl slot).run secret.seeds)).run secret
      pure ((), { result.2 with seeds := result.1.2 })
  | .coin coin => sampled (unifSpec.query coin : ProbComp _)
  | .hash bytes => fun secret => do
      let result ← (sampled ((CtxRomAuth.ctxRandomOracle ((), bytes)).run secret.primitive.2)).run secret
      pure (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })
  | .charge kind => fun secret => pure ((), { secret with primitive :=
      ({ secret.primitive.1 with effects := Function.update secret.primitive.1.effects kind (secret.primitive.1.effects kind + 1) }, secret.primitive.2) })
  | .lookup coordinate => fun secret =>
      (withRecord (PqxdhRecordFactsCounter.localInterpreter ideal setup codec (cachedSeeds secret) (.inl coordinate))).run secret
  | .opening pending => fun secret =>
      (withRecord (PqxdhRecordFactsCounter.localInterpreter ideal setup codec (cachedSeeds secret) (.inr (.inl pending)))).run secret
  | .sealing pending => fun secret =>
      (withRecord (PqxdhRecordFactsCounter.localInterpreter ideal setup codec (cachedSeeds secret) (.inr (.inr pending)))).run secret
  | .knownSend kernel context => withRecord (primitiveWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec)))
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))))
  | .knownReceive kernel target context => withRecord (primitiveWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec)))
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))))
  | .publish tag => fun secret => pure ((), publish tag secret)

/-- Framing a projected native program with the untouched chain table preserves its entire reply and writer log. -/
theorem primitiveWork_project {Result : Type}
    (before after : StateT (Primitive × PqxdhRecordLiftLoggedAdapters.Frames) ProbComp Result)
    (project : ∀ state, Prod.map id zeroLogged <$> before.run state = after.run (zeroLogged state))
    (state : RecordState n) :
    Prod.map id zeroRecord <$> (primitiveWork before).run state =
      (primitiveWork after).run (zeroRecord state) := by
  have same := congrArg (fun work => (fun reply => (reply.1, (state.1, reply.2))) <$> work) (project state.2)
  simpa only [primitiveWork, StateT.run, bind_pure_comp, Functor.map_map,
    zeroRecord, Prod.map, id_eq] using same

/-- Actual source services have identical replies and operational poststate after projecting only uniform instrumentation. -/
theorem interpreter_project (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (ServiceSpec n).Domain) (state : Private n) :
    Prod.map id zeroPrivate <$>
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal)
        setup codec query).run state =
      (interpreter ideal setup codec query).run (zeroPrivate state) := by
  cases query with
  | hash bytes =>
      have same := congrArg (fun work => (fun reply => (reply.1.1,
        { reply.2 with primitive := (reply.2.primitive.1, reply.1.2) })) <$> work)
        (sampled_project ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2) state)
      simp only [PqxdhRecordLiftProtocol.interpreter, interpreter, sampled,
        StateT.run, bind_pure_comp, Functor.map_map, zeroPrivate, zeroPrimitive,
        Prod.map, id_eq] at same ⊢
      convert same using 1
  | allocate slot =>
      have same := congrArg (fun work => (fun reply => ((), { reply.2 with seeds := reply.1.2 })) <$> work)
        (sampled_project ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) state)
      simpa only [PqxdhRecordLiftProtocol.interpreter, interpreter, sampled,
        StateT.run, bind_pure_comp, Functor.map_map, zeroPrivate,
        Prod.map, id_eq] using same
  | coin coin => exact sampled_project (unifSpec.query coin : ProbComp _) state
  | charge kind => simp [PqxdhRecordLiftProtocol.interpreter, interpreter, zeroPrivate, zeroPrimitive, StateT.run]
  | lookup coordinate =>
      exact withRecord_project _ _ (local_project ideal setup codec (cachedSeeds state) (.inl coordinate)) state
  | opening pending =>
      exact withRecord_project _ _ (local_project ideal setup codec (cachedSeeds state) (.inr (.inl pending))) state
  | sealing pending =>
      exact withRecord_project _ _ (local_project ideal setup codec (cachedSeeds state) (.inr (.inr pending))) state
  | knownSend kernel context =>
      exact withRecord_project _ _ (primitiveWork_project _ _
        (send_program_project setup codec (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send kernel context)))) state
  | knownReceive kernel target context =>
      exact withRecord_project _ _ (primitiveWork_project _ _
        (receive_program_project setup codec (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive kernel target context)))) state
  | publish tag => simp [PqxdhRecordLiftProtocol.interpreter, interpreter, publish, zeroPrivate, StateT.run]

/-- The equality holds through every adaptive source-service continuation and retains its entire returned result. -/
theorem program_project (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : Private n) :
    Prod.map id zeroPrivate <$>
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal)
        setup codec) client).run state =
      (simulateQ (interpreter ideal setup codec) client).run (zeroPrivate state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ zeroPrivate
    (interpreter_project ideal setup codec) client state

end BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.primitiveWork_project' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.primitiveWork_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.interpreter_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.interpreter_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol.program_project
