-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld

/-! Exact publication-event observation and accounting for the original complete ideal source worlds. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client ctxRun ctxView UnpublishedAccept unpublishedEvent publicationTerm)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The original full ideal source and its checked cache/counter erasure have identical unpublished-accept Boolean laws. -/
theorem unpublished_observation (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    LazyOracleDiscard.LawEq
      ((fun result => unpublishedEvent codec route (ctxView result)) <$>
        ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      ((fun result => unpublishedEvent codec route (ctxView result)) <$>
        PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary) := by
  simpa only [Functor.map_map] using
    (PqxdhRecordFactsPrivateCacheWorld.view_observation modes replace setup codec route env serverKid bounds mode adversary ideal).map
      (unpublishedEvent codec route)

/-- The exact original Boolean event probability equals the concrete erased-run event probability. -/
theorem unpublished_probability (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} =
    𝒟[PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary]
      {result | UnpublishedAccept codec route (ctxView result)} := by
  rw [(unpublished_observation modes ideal replace setup codec route env serverKid bounds mode adversary).evalDist_eq]
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map, ← prEvent_eq_evalDist_of_discrete]
  simp only [unpublishedEvent, decide_eq_true_eq]

/-- The derived two-branch, receive-times-send term is exactly the unchanged frozen publication term. -/
theorem publication_term (budget : Budget) :
    2 * (budget.receives : ENNReal) * budget.sends * ((2 ^ 512 : Nat) : ENNReal)⁻¹ = publicationTerm budget := by
  simp only [publicationTerm, PqxdhRecordLiftIdeal.guessTerm, Nat.cast_mul, Nat.cast_ofNat]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.unpublished_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.unpublished_observation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.unpublished_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.unpublished_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.publication_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability.publication_term
