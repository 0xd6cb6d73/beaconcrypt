-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationProbability
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-! The unchanged ideal-record origin statement, with its concrete source event and explicit publication loss discharged. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The exact erased source unpublished-accept event satisfies the coefficient-two receive-times-send bound, with every source cover and marked-resumption obligation discharged. -/
theorem erased_unpublished_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary]
      {result | UnpublishedAccept codec route (ctxView result)} ≤
      2 * (budget.receives : ENNReal) * budget.sends * ((2 ^ 512 : Nat) : ENNReal)⁻¹ := by
  exact PqxdhRecordFactsOriginSourceProbability.source_event_bound modes ideal replace setup codec route
    env startup allowance framed serverKid bounds mode budget adversary respects
    (fun result => UnpublishedAccept codec route (ctxView result))
    (PqxdhRecordFactsOriginCutEvent.FailedCutEvent codec route)
    (PqxdhRecordFactsOriginCutEvent.source_cover modes ideal replace setup codec route readback env serverKid bounds mode budget adversary respects)
    (fun index cut selected => PqxdhRecordFactsOriginCutEvent.scan_marked modes ideal replace setup codec route env serverKid bounds mode adversary index.val cut selected)

/-- The original complete source world has the unchanged frozen publication loss, via exact retained-event observation. -/
theorem ctxRun_unpublished_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget := by
  rw [PqxdhRecordFactsOriginPublicationProbability.unpublished_probability modes ideal replace setup codec route env serverKid bounds mode adversary]
  exact (erased_unpublished_bound modes ideal replace setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects).trans_eq
    (PqxdhRecordFactsOriginPublicationProbability.publication_term budget)

/-- Integrity-ideal records have the explicit unpublished-origin loss in both observation modes. -/
theorem idealAuth_unpublished_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget :=
  ctxRun_unpublished_bound (fun _ => .replay) (by intro label; decide) id setup codec route readback
    env startup allowance framed serverKid bounds mode budget adversary respects

/-- The actual mode-selected ideal-record world has the unchanged publication loss. -/
theorem idealRecords_unpublished_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget :=
  ctxRun_unpublished_bound (fun _ => recordMode mode) (by intro label; cases mode <;> decide) id setup codec route readback
    env startup allowance framed serverKid bounds mode budget adversary respects

/-- The fully random-record world also has the explicit publication loss in both observation modes. -/
theorem randomRecords_unpublished_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      randomRecords setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget :=
  ctxRun_unpublished_bound (fun _ => .random) (by intro label; decide) id setup codec route readback
    env startup allowance framed serverKid bounds mode budget adversary respects

/-- The unchanged frozen origin statement: two structural zero events and the explicit publication loss in all three ideal record worlds. No caller-supplied event cover, marker, or origin conclusion remains. -/
theorem origin_statement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) :
    OriginStatement setup codec route serverKid bounds n := by
  intro readback _agreement E X env startup allowance framed mode adversary budget respects
  exact ⟨PqxdhRecordFactsOriginGlobal.idealAuth_unproduced_zero setup codec route readback env serverKid bounds mode adversary,
    PqxdhRecordFactsOriginGlobal.idealRecords_unproduced_zero setup codec route readback env serverKid bounds mode adversary,
    idealAuth_unpublished_bound setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects,
    idealRecords_unpublished_bound setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects,
    randomRecords_unpublished_bound setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.erased_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.erased_unpublished_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.ctxRun_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.ctxRun_unpublished_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.idealAuth_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.idealAuth_unpublished_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.idealRecords_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.idealRecords_unpublished_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.randomRecords_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.randomRecords_unpublished_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.origin_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginClosure.origin_statement
