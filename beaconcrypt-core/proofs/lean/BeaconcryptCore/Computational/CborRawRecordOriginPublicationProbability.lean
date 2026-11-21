-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginObservation
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability

/-! The raw guarded source's literal unpublished-acceptance event has exactly its private-cache-erased event law. The observation preserves the original public transcript and fallible writer, rather than equating sibling execution paths. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client ctxView UnpublishedAccept unpublishedEvent viewOf)
open PqxdhRecordLiftProtocol (Private)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open CborRawRecordOriginObservation (ctxRun erasedRun)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The complete actual raw source and its cache erasure retain the exact same unpublished-acceptance Boolean law. -/
theorem unpublished_observation (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    LazyOracleDiscard.LawEq
      ((fun result => unpublishedEvent codec route (ctxView result)) <$>
        ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      ((fun result => unpublishedEvent codec route (ctxView result)) <$>
        erasedRun modes replace setup codec route env serverKid bounds mode adversary) := by
  have same := (CborRawRecordOriginObservation.run_observation modes replace setup codec route env serverKid bounds mode adversary ideal).map
    (fun result : Client n E X × (Private n × (Label n → PqxdhRecordFactsPrivateCache.Local)) =>
      unpublishedEvent codec route (viewOf result.1 result.2.1.produced))
  simp only [Functor.map_map] at same
  exact same

/-- Actual guarded publication probability equals the literal erased source event probability. -/
theorem unpublished_probability (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} =
    𝒟[erasedRun modes replace setup codec route env serverKid bounds mode adversary]
      {result | UnpublishedAccept codec route (ctxView result)} := by
  rw [(unpublished_observation modes ideal replace setup codec route env serverKid bounds mode adversary).evalDist_eq]
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map, ← prEvent_eq_evalDist_of_discrete]
  simp only [unpublishedEvent, decide_eq_true_eq]

end BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability.unpublished_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability.unpublished_observation
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability.unpublished_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability.unpublished_probability
