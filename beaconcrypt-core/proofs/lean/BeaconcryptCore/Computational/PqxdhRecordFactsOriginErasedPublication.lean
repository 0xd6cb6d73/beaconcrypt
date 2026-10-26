-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent

/-! Transport only retained final-state failed-writer evidence through the proved observation law. No execution-path identification is inferred from equality in law. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication
open PqxdhRecordLiftIdeal PqxdhRecordFactsPrivateCacheWorld
open PqxdhRecordFactsPrivateCacheFamily (observeFamily)
open PqxdhRecordFactsOriginPublicationEvent (FailedWriterAt)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Entry)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Contextual law equality for probabilistic programs preserves support, including higher-order retained states. -/
theorem law_support {α : Type} {left right : ProbComp α}
    (same : LazyOracleDiscard.LawEq left right) (value : α) :
    value ∈ support left ↔ value ∈ support right := by
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  have point := congrArg (fun measure => measure {value}) same.evalDist_eq
  rw [OracleComp.mem_support_iff_evalDist_singleton_pos, OracleComp.mem_support_iff_evalDist_singleton_pos, point]

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

/-- Every actual erased unpublished acceptance has the retained failed-writer seal evidence proved for the original full source. The consumer selects its own execution cut separately. -/
theorem erased_unpublished_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (erasedRun modes replace setup codec route env serverKid bounds mode adversary))
    (unpublished : UnpublishedAccept codec route (ctxView result)) :
    ∃ value ∈ (ctxView result).result, ∃ before event after,
      value.2.1.transcript = before ++ event :: after ∧
      FailedWriterAt codec route result.1.2 result.2 event := by
  obtain ⟨original, reached, same⟩ := retained_support modes ideal replace setup codec route env serverKid bounds mode adversary result supported
  have view := retained_view original result same
  have originalEvent : UnpublishedAccept codec route (ctxView original) := view ▸ unpublished
  obtain ⟨value, present, before, event, after, split, failed⟩ :=
    PqxdhRecordFactsOriginPublicationEvent.ctxRun_unpublished_failed modes ideal replace setup codec route readback env serverKid bounds mode adversary original reached originalEvent
  exact ⟨value, view ▸ present, before, event, after, split, retained_failed codec route original result same event failed⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.law_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.law_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.retained_failed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.erased_unpublished_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication.erased_unpublished_failed
