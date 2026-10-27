-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler
import BeaconcryptCore.Computational.PqxdhRecordFactsCounterCtx

/-! Private-cache discard for the actual adaptive CTX service program and its permitted view. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftProtocol (Private ServiceSpec)
open PqxdhRecordFactsPrivateCacheFamily (observeFamily)
open PqxdhRecordFactsPrivateCacheServices (mixed)
open PqxdhRecordFactsPrivateCacheCompiler (base compile erasedInterpreter)
open PqxdhServerAuthExperiment (Setup Codec)
open LazyOracleDiscard
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The concrete counterless chain service used by the original all-ideal CTX world. -/
noncomputable abbrev baseInterpreter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :=
  PqxdhRecordFactsCounterProtocol.interpreter (n := n) (fun _ => true) setup codec

/-- The actual service compiler instantiated with the source's writer, decoder and base interpreter. -/
noncomputable def compiledInterpreter (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp) :=
  mixed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto (base (baseInterpreter setup codec))
    ∘ₛ compile codec.frameWrite replace

/-- The exact counterless CTX endpoint equals its internal service compilation. -/
theorem compiled_interpreter (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    compiledInterpreter modes replace setup codec = PqxdhRecordFactsCounterCtx.interpreter modes replace setup codec := by
  ext query state
  exact PqxdhRecordFactsPrivateCacheCompiler.compile_service modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (baseInterpreter setup codec) codec.frameWrite replace query state

/-- Counterless source services with precisely the discarded raw private-cache completions omitted. -/
noncomputable def erased (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp) :=
  erasedInterpreter modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (baseInterpreter setup codec) codec.frameWrite replace

/-- Exact family observation equality for the actual counterless CTX services through any adaptive continuation. -/
theorem counterless_observation (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : CtxPrivate n) :
    LawEq (Prod.map id observeFamily <$>
      (simulateQ (PqxdhRecordFactsCounterCtx.interpreter modes replace setup codec) client).run state)
      (Prod.map id observeFamily <$> (simulateQ (erased modes replace setup codec) client).run state) := by
  rw [← compiled_interpreter, compiledInterpreter, QueryImpl.simulateQ_compose]
  exact PqxdhRecordFactsPrivateCacheCompiler.compiled_observation modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto (baseInterpreter setup codec)
    codec.frameWrite replace supported client state

/-- Retain all base fields except uniform instrumentation and all local histories except private suffix caches. -/
def observe (state : CtxPrivate n) := observeFamily (PqxdhRecordFactsCounter.zeroCtx state)

/-- The counted source CTX program has the same complete observation after removing its counter and discarded raw private-cache completions. -/
theorem program_observation (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : CtxPrivate n) :
    LawEq (Prod.map id observe <$> (simulateQ (ctxInterpreter modes replace setup codec) client).run state)
      (Prod.map id observeFamily <$>
        (simulateQ (erased modes replace setup codec) client).run (PqxdhRecordFactsCounter.zeroCtx state)) := by
  have same := congrArg (fun work => Prod.map id observeFamily <$> work)
    (PqxdhRecordFactsCounterCtx.program_project modes replace setup codec client state)
  have before : Prod.map id observe <$> (simulateQ (ctxInterpreter modes replace setup codec) client).run state =
      Prod.map id observeFamily <$>
        (simulateQ (PqxdhRecordFactsCounterCtx.interpreter modes replace setup codec) client).run
          (PqxdhRecordFactsCounter.zeroCtx state) := by
    simp only [Functor.map_map] at same
    exact same
  exact (LawEq.of_eq before).trans (counterless_observation modes replace setup codec supported client _)

/-- The identical source environment/adversary schedule with only counter and discarded-cache observation instrumentation changed. -/
noncomputable def erasedRun {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ProbComp (Client n E X × CtxPrivate n) :=
  (simulateQ (erased modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)

/-- The complete actual CTX run and erased run retain the same client result, normalized base state and all per-coordinate local histories. -/
theorem run_observation {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (supported : ∀ label, modes label ≠ .real) :
    LawEq (Prod.map id observe <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      (Prod.map id observeFamily <$> erasedRun modes replace setup codec route env serverKid bounds mode adversary) :=
  program_observation modes replace setup codec supported _ CtxPrivate.initial

/-- In particular, the actual permitted view has the same law through every evaluated continuation; no cache or private counter is exposed. -/
theorem view_observation {E X : Type} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (supported : ∀ label, modes label ≠ .real) :
    LawEq (ctxView <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      (ctxView <$> erasedRun modes replace setup codec route env serverKid bounds mode adversary) := by
  have same := (run_observation modes replace setup codec route env serverKid bounds mode adversary supported).map
    (fun result : Client n E X × (Private n × (Label n → PqxdhRecordFactsPrivateCache.Local)) =>
      viewOf result.1 result.2.1.produced)
  simp only [Functor.map_map] at same
  exact same

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.compiled_interpreter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.compiled_interpreter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.counterless_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.counterless_observation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.program_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.program_observation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.run_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.run_observation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.view_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld.view_observation
