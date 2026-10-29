-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginProgram
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds

/-! Private cache discard changes only the retained observation of the actual guarded source program; it does not identify sibling execution paths or modify its fallible writer. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginObservation
open PqxdhRecordLiftIdeal
open PqxdhRecordFactsPrivateCacheWorld (observe)
open PqxdhRecordFactsPrivateCacheFamily (observeFamily)
open PqxdhRecordFactsOriginPublicationEvent (FailedWriterAt)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Entry)
open PqxdhRecordFactsOriginErasedPublication (law_support)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

noncomputable def ctxRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : ProbComp (Client n E X × CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run CtxPrivate.initial

noncomputable def erasedRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : ProbComp (Client n E X × CtxPrivate n) :=
  (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)

/-- The exact raw program and its erased cache program retain the same complete view and sealing dictionaries. -/
theorem run_observation (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (ideal : ∀ label, modes label ≠ .real) :
    LazyOracleDiscard.LawEq
      (Prod.map id observe <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      (Prod.map id observeFamily <$> erasedRun modes replace setup codec route env serverKid bounds mode adversary) :=
  PqxdhRecordFactsPrivateCacheWorld.program_observation modes replace setup codec ideal _ CtxPrivate.initial

/-- This source endpoint is exactly the arbitrary-client CTX world used by the proved cryptographic telescope. -/
theorem ctxRunOf_eq (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
      (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary) =
        ctxRun modes replace setup codec route env serverKid bounds mode adversary := rfl

/-- Each supported erased final observation is realized by an original supported final observation; this asserts no path correspondence. -/
theorem retained_support (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (erasedRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∃ original ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary),
      Prod.map id observe original = Prod.map id observeFamily result := by
  have observed : Prod.map id observeFamily result ∈ support
      (Prod.map id observeFamily <$> erasedRun modes replace setup codec route env serverKid bounds mode adversary) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  have original := (law_support (run_observation modes replace setup codec route env serverKid bounds mode adversary ideal) _).mpr observed
  simpa only [support_map, Set.mem_image] using original

/-- The observation retains the entire permitted view, including actual transcript and production history. -/
theorem retained_view (original result : Client n E X × CtxPrivate n)
    (same : Prod.map id observe original = Prod.map id observeFamily result) :
    ctxView original = ctxView result := by
  exact congrArg (fun observed => viewOf observed.1 observed.2.1.produced) same

/-- Failed-writer evidence reads only retained client fields and complete per-coordinate successful-seal dictionaries. -/
theorem retained_failed (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (original result : Client n E X × CtxPrivate n)
    (same : Prod.map id observe original = Prod.map id observeFamily result)
    (event : Entry) (failed : FailedWriterAt codec route original.1.2 original.2 event) :
    FailedWriterAt codec route result.1.2 result.2 event := by
  have clients := congrArg Prod.fst same
  change original.1 = result.1 at clients
  have keys : ∀ label, (original.2.keys label).1 = (result.2.keys label).1 :=
    fun label => congrArg (fun observed => observed.2.2 label) same
  simpa only [FailedWriterAt, clients, keys] using failed


end BeaconcryptCore.Computational.CborRawRecordOriginObservation

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginObservation.run_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginObservation.run_observation
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginObservation.ctxRunOf_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginObservation.ctxRunOf_eq
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_support
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_view
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginObservation.retained_failed
