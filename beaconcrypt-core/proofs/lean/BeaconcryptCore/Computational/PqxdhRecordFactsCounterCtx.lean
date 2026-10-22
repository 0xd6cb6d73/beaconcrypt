-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily

/-! Exact uniform-counter projection of the actual CTX service interpreter. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx
open PqxdhRecordFactsCounter
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Original CTX service selection with the already defined counterless endpoints. -/
noncomputable def interpreter (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ (PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state
  | .sealing pending => fun state => do
      let result ← (simulateQ (PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
  | query => onBase (PqxdhRecordFactsCounterProtocol.interpreter (fun _ => true) setup codec query)

/-- Each actual keyed request preserves its exact optional plaintext or record and entire state except uniform instrumentation. -/
theorem keyed_project (modes : Label n → KeyMode) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id zeroCtx <$> (keyed modes decode crypto query).run state =
      (PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed modes decode crypto query).run (zeroCtx state) := by
  rw [PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed_run]
  have same := congrArg (fun work => (fun reply => ((reply.1.1.1,
    { base := { reply.2 with primitive := (reply.2.primitive.1, reply.1.2) }
      keys := Function.update state.keys query.1 reply.1.1.2 }) : (KeyedSpec n).Range query × CtxPrivate n)) <$> work)
    (sampled_project ((simulateQ AdaptiveCtxSharedHash.hashImpl
      ((keyImpl decode crypto (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
        (state.keys query.1))).run state.base.primitive.2) state.base)
  simp only [keyed,
    PqxdhRecordFactsPrivateCacheRandom.linked, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, bind_pure_comp, Functor.map_map,
    zeroCtx, zeroPrivate, zeroPrimitive, Prod.map, id_eq] at same ⊢
  exact same

/-- Arbitrary adaptive keyed continuations retain the complete result and projected poststate. -/
theorem keyed_program_project (modes : Label n → KeyMode) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) {Result : Type} (client : OracleComp (KeyedSpec n) Result) (state : CtxPrivate n) :
    Prod.map id zeroCtx <$> (simulateQ (keyed modes decode crypto) client).run state =
      (simulateQ (PqxdhRecordFactsPrivateCacheFamily.uncountedKeyed modes decode crypto) client).run (zeroCtx state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ zeroCtx (keyed_project modes decode crypto) client state

/-- Framing a projected base-only operation preserves every keyed state. -/
theorem onBase_project {Result : Type}
    (before after : StateT (PqxdhRecordLiftProtocol.Private n) ProbComp Result)
    (project : ∀ state, Prod.map id zeroPrivate <$> before.run state = after.run (zeroPrivate state))
    (state : CtxPrivate n) :
    Prod.map id zeroCtx <$> (onBase before).run state =
      (onBase after).run (zeroCtx state) := by
  have same := congrArg (fun work => (fun result => (result.1, { state with base := result.2 })) <$> work)
    (project state.base)
  simp only [onBase, StateT.run, Functor.map_map, zeroCtx, Prod.map, id_eq] at same ⊢
  exact same

/-- Every actual CTX service retains its complete operational result after projecting only the uniform counter. -/
theorem interpreter_project (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id zeroCtx <$> (ctxInterpreter modes replace setup codec query).run state =
      (interpreter modes replace setup codec query).run (zeroCtx state) := by
  cases query with
  | sealing pending =>
      have same := congrArg (fun work =>
        (fun result => (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) <$> work)
        (keyed_program_project modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
          ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending) state)
      simp only [ctxInterpreter, interpreter, StateT.run, bind_pure_comp, Functor.map_map,
        zeroCtx, zeroPrivate, Prod.map, id_eq] at same ⊢
      exact same
  | opening pending =>
      exact keyed_program_project modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending) state
  | _ => exact onBase_project _ _ (PqxdhRecordFactsCounterProtocol.interpreter_project
      (fun _ => true) setup codec _) state

/-- The complete adaptive CTX service execution has the same returned result and projected private state. -/
theorem program_project (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : CtxPrivate n) :
    Prod.map id zeroCtx <$> (simulateQ (ctxInterpreter modes replace setup codec) client).run state =
      (simulateQ (interpreter modes replace setup codec) client).run (zeroCtx state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ zeroCtx (interpreter_project modes replace setup codec) client state

end BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.keyed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.keyed_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.keyed_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.keyed_program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.onBase_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.onBase_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.interpreter_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.interpreter_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx.program_project
