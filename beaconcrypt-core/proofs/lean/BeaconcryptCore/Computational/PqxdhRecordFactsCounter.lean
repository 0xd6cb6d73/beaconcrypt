-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-! Exact removal of the uniform-draw counter from record computations. Native/effect counts, caches, private material and replies remain retained. This module proves no equality of source costs. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsCounter
open PqxdhRecordLiftWorld
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Zero only the uniform-draw instrumentation, retaining both other count families and the shared ROM. -/
def zeroPrimitive (state : Primitive) : Primitive :=
  ({ state.1 with uniform := 0 }, state.2)

/-- The corresponding projection on the entire protocol-private state. -/
def zeroPrivate (state : PqxdhRecordLiftProtocol.Private n) : PqxdhRecordLiftProtocol.Private n :=
  { state with primitive := zeroPrimitive state.primitive }

/-- The corresponding projection leaves every CTX coordinate dictionary intact. -/
def zeroCtx (state : PqxdhRecordLiftIdeal.CtxPrivate n) : PqxdhRecordLiftIdeal.CtxPrivate n :=
  { state with base := zeroPrivate state.base }

/-- Native primitive interpretation without uniform instrumentation, retaining the actual native call charge and shared ROM poststate. -/
noncomputable def primitives (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive ProbComp) := fun query state => do
  let result ← (PqxdhDeploymentNative.primitives setup codec query).run ((), state.2)
  let kind := RawCtxMixedOwner.callKind query
  pure (result.1, ({ state.1 with
    native := Function.update state.1.native kind (state.1.native kind + 1) }, result.2.2))

/-- Removing the actual sampler counter commutes with an entire native primitive execution, including its retained native bill. -/
theorem primitives_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive) :
    Prod.map id zeroPrimitive <$> (PqxdhRecordLiftWorld.primitives setup codec query).run state =
      (primitives setup codec query).run (zeroPrimitive state) := by
  have same := congrArg (fun work =>
    (fun result : RawCtxMixedOwner.NativeSpec.Range query × (Unit × CtxRomAuth.CtxRO.QueryCache) =>
      (result.1, ({ state.1 with
      uniform := 0
      native := Function.update state.1.native (RawCtxMixedOwner.callKind query)
        (state.1.native (RawCtxMixedOwner.callKind query) + 1) }, result.2.2))) <$> work)
    (countCoin_forget ((PqxdhDeploymentNative.primitives setup codec query).run ((), state.2)) state.1.uniform)
  simpa only [PqxdhRecordLiftWorld.primitives, primitives, StateT.run, bind_pure_comp,
    Functor.map_map, zeroPrimitive, Prod.map, id_eq] using same

/-- Full adaptive primitive programs preserve the same reply and every field except the uniform counter. -/
theorem primitive_program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {Result : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : Primitive) :
    Prod.map id zeroPrimitive <$> (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) client).run state =
      (simulateQ (primitives setup codec) client).run (zeroPrimitive state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ zeroPrimitive (primitives_project setup codec) client state

/-- Removing uniform instrumentation from the actual private sampler preserves its whole value and every other private field. -/
theorem sampled_project {Result : Type} (work : ProbComp Result) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id zeroPrivate <$> (PqxdhRecordLiftProtocol.sampled work).run state =
      (fun result => (result, zeroPrivate state)) <$> work := by
  have same := congrArg (fun computation => (fun result => (result, zeroPrivate state)) <$> computation)
    (countCoin_forget work state.primitive.1.uniform)
  simpa only [PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
    zeroPrivate, zeroPrimitive, Prod.map, id_eq] using same

/-- Keep the exact pending writer log alongside the projected primitive state. -/
def zeroLogged (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    Primitive × PqxdhRecordLiftLoggedAdapters.Frames := (zeroPrimitive state.1, state.2)

/-- The actual frame logger preserves every writer buffer, including failure, while removing only uniform instrumentation. -/
theorem logged_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    Prod.map id zeroLogged <$>
      (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec) query).run state =
      (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec) query).run (zeroLogged state) := by
  have same := congrArg (fun work => PqxdhRecordLiftLoggedAdapters.swapResult <$> work)
    (primitive_program_project setup codec ((PqxdhDeploymentNative.frameLog query).run state.2) state.1)
  simpa only [PqxdhRecordLiftLoggedAdapters.loggedNative, StateT.run, Functor.map_map,
    zeroLogged, PqxdhRecordLiftLoggedAdapters.swapResult, Prod.map, id_eq] using same

/-- Full logged source programs retain their complete pending publication history under counter projection. -/
theorem logged_program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {Result : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    Prod.map id zeroLogged <$>
      (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)) client).run state =
      (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec)) client).run (zeroLogged state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ zeroLogged (logged_project setup codec) client state

/-- A mixed coordinate lookup with its native KDF bill and persistent whole output, but no uniform-counter update. -/
noncomputable def lookup {Slot : Type} [DecidableEq Slot]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds Slot) (ideal : PqxdhRecordLiftChainState.Coordinate Slot → Bool) :
    PqxdhRecordLiftChainCompiler.Lookup Slot Primitive := fun coordinate state => do
  let primitive := PqxdhRecordLiftChainOracle.charge state.2
  if ideal coordinate then
    match state.1 coordinate with
    | some output => pure (output, (state.1, primitive))
    | none =>
      let output ← $ᵗ PqxdhFullSecretInputKdf.FullOutput
      pure (output, (state.1.cacheQuery coordinate output, primitive))
  else
    let output := PqxdhRecordLiftRealTable.output source seeds state.1 coordinate
    pure (output, (state.1.cacheQuery coordinate output, primitive))

/-- Counter removal commutes with repeated, real and ideal coordinate lookup; all source KDF charges remain present. -/
theorem lookup_project {Slot : Type} [DecidableEq Slot]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds Slot) (ideal : PqxdhRecordLiftChainState.Coordinate Slot → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate Slot)
    (state : PqxdhRecordLiftChainCompiler.Execution Slot Primitive) :
    Prod.map id (Prod.map id zeroPrimitive) <$>
      (PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state =
      (lookup source seeds ideal coordinate).run (Prod.map id zeroPrimitive state) := by
  have sample (primitive : Primitive) : PqxdhRecordLiftChainOracle.sample primitive =
      (fun output => (output, ({ primitive.1 with uniform := primitive.1.uniform + 76 }, primitive.2))) <$>
        ($ᵗ PqxdhFullSecretInputKdf.FullOutput) := PqxdhRecordLiftChainOracle.sample_exact primitive
  simp only [PqxdhRecordLiftChainOracle.lookup, lookup, StateT.run, Prod.map, id_eq]
  by_cases chosen : ideal coordinate
  · simp only [chosen, ite_true]
    cases cached : state.1 coordinate
    · simp only [sample,
        bind_pure_comp, Functor.map_map, zeroPrimitive, PqxdhRecordLiftChainOracle.charge]
      simp only [Prod.map, zeroPrimitive, id_eq]
    · simp only [map_pure, zeroPrimitive, PqxdhRecordLiftChainOracle.charge]
      rfl
  · simp only [chosen, Bool.false_eq_true, ite_false, map_pure, zeroPrimitive, PqxdhRecordLiftChainOracle.charge]
    rfl

/-- The entire source send adapter keeps its real optional reply and writer log. -/
theorem send_program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {Result : Type} (client : OracleComp RawCtxSourceSend.PrimitiveSpec Result)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    Prod.map id zeroLogged <$>
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftProtocol.recordNative setup codec)) client).run state =
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec))) client).run (zeroLogged state) := by
  simp only [PqxdhRecordLiftWorldCompiler.sendNative, PqxdhRecordLiftProtocol.recordNative,
    QueryImpl.simulateQ_compose]
  exact logged_program_project setup codec (simulateQ RawCtxMixedOwner.sendAdapter client) state

/-- The entire source receive adapter returns the challenger's optional plaintext unchanged. -/
theorem receive_program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {Result : Type} (client : OracleComp RawCtxWholeOwner.PrimitiveSpec Result)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    Prod.map id zeroLogged <$>
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftProtocol.recordNative setup codec)) client).run state =
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec))) client).run (zeroLogged state) := by
  simpa only [PqxdhRecordLiftWorldCompiler.receiveNative, PqxdhRecordLiftProtocol.recordNative,
    QueryImpl.simulateQ_compose] using
    logged_program_project setup codec (simulateQ RawCtxMixedOwner.receiveAdapter client) state

/-- The complete record projection keeps the chain table and literal pending frames. -/
def zeroRecord (state : PqxdhRecordLiftProtocol.RecordState n) : PqxdhRecordLiftProtocol.RecordState n :=
  (state.1, zeroLogged state.2)

/-- Counter projection carries the pending writer buffer through the actual mixed coordinate lookup. -/
theorem liftLookup_project
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (coordinate : PqxdhRecordLiftWorldCompiler.Label n) (state : PqxdhRecordLiftProtocol.RecordState n) :
    Prod.map id zeroRecord <$>
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup source seeds ideal) coordinate).run state =
      (PqxdhRecordLiftLoggedAdapters.liftLookup (lookup source seeds ideal) coordinate).run (zeroRecord state) := by
  have same := congrArg (fun work =>
    (fun reply => (reply.1, (reply.2.1, (reply.2.2, state.2.2)))) <$> work)
    (lookup_project source seeds ideal coordinate (state.1, state.2.1))
  simpa only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, Functor.map_map,
    zeroRecord, zeroLogged, Prod.map, id_eq] using same

/-- The same local source services with only uniform instrumentation removed. -/
noncomputable def localInterpreter
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n)) :
    QueryImpl (PqxdhRecordLiftProtocol.LocalSpec n) (StateT (PqxdhRecordLiftProtocol.RecordState n) ProbComp) :=
  PqxdhRecordLiftOpaqueDrivers.interpreter seeds
    (PqxdhRecordLiftLoggedAdapters.liftLookup (lookup setup.source seeds ideal))
    (PqxdhRecordLiftNativeAdapters.receiveOpen (PqxdhRecordLiftWorldCompiler.receiveNative
      (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec))))
    (PqxdhRecordLiftNativeAdapters.sendSeal (PqxdhRecordLiftWorldCompiler.sendNative
      (PqxdhRecordLiftLoggedAdapters.loggedNative (primitives setup codec))))

/-- Each actual local callback preserves its reply, chain table and native writer effects under the counter projection. -/
theorem local_project
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (query : (PqxdhRecordLiftProtocol.LocalSpec n).Domain) (state : PqxdhRecordLiftProtocol.RecordState n) :
    Prod.map id zeroRecord <$>
      (PqxdhRecordLiftProtocol.localInterpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal)
        setup codec seeds query).run state =
      (localInterpreter ideal setup codec seeds query).run (zeroRecord state) := by
  rcases query with coordinate | pending
  · have same := congrArg (fun work => (fun reply => ((), reply.2)) <$> work)
      (liftLookup_project setup.source seeds ideal coordinate state)
    simpa only [PqxdhRecordLiftProtocol.localInterpreter, localInterpreter,
      PqxdhRecordLiftOpaqueDrivers.interpreter, PqxdhRecordLiftMixedWorld.policy,
      StateT.run_map, Functor.map_map, Prod.map, id_eq] using same
  · rcases pending with pending | pending
    · have same := congrArg (fun work => (fun reply => (reply.1, (state.1, reply.2))) <$> work)
        (receive_program_project setup codec
          (RawCtxWholeOwner.adapter (.inr (RawCtxInterpretedOpening.toNative
            (PqxdhRecordLiftMaterialTable.eraseOpening seeds state.1 pending)))) state.2)
      simp only [PqxdhRecordLiftProtocol.localInterpreter, localInterpreter,
        PqxdhRecordLiftOpaqueDrivers.interpreter, PqxdhRecordLiftNativeAdapters.receiveOpen,
        StateT.run, bind_pure_comp, Functor.map_map, zeroRecord, Prod.map, id_eq] at same ⊢
      convert same using 1
    · have same := congrArg (fun work => (fun reply => (reply.1, (state.1, reply.2))) <$> work)
        (send_program_project setup codec
          (RawCtxSourceSend.adapter (.inr (RawCtxInterpretedSend.nativeSeal
            (PqxdhRecordLiftMaterialTable.eraseSeal seeds state.1 pending)))) state.2)
      simp only [PqxdhRecordLiftProtocol.localInterpreter, localInterpreter,
        PqxdhRecordLiftOpaqueDrivers.interpreter, PqxdhRecordLiftNativeAdapters.sendSeal,
        StateT.run, bind_pure_comp, Functor.map_map, zeroRecord, Prod.map, id_eq] at same ⊢
      convert same using 1

/-- Lifting any projected record computation preserves all other private fields. -/
theorem withRecord_project {Result : Type}
    (before after : StateT (PqxdhRecordLiftProtocol.RecordState n) ProbComp Result)
    (project : ∀ state, Prod.map id zeroRecord <$> before.run state = after.run (zeroRecord state))
    (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id zeroPrivate <$> (PqxdhRecordLiftProtocol.withRecord before).run state =
      (PqxdhRecordLiftProtocol.withRecord after).run (zeroPrivate state) := by
  have same := congrArg (fun work =>
    Prod.map id (PqxdhRecordLiftProtocol.putRecord (zeroPrivate state)) <$> work)
    (project (PqxdhRecordLiftProtocol.recordState state))
  simp only [PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.putRecord,
    PqxdhRecordLiftProtocol.recordState, StateT.run, bind_pure_comp, Functor.map_map,
    zeroPrivate, zeroRecord, zeroLogged, Prod.map, id_eq] at same ⊢
  convert same using 1
  rfl

end BeaconcryptCore.Computational.PqxdhRecordFactsCounter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.primitives_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.primitives_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.primitive_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.primitive_program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.sampled_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.sampled_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.logged_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.logged_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.logged_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.logged_program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.lookup_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.lookup_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.send_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.send_program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.receive_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.receive_program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.liftLookup_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.liftLookup_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.local_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.local_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounter.withRecord_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounter.withRecord_project
