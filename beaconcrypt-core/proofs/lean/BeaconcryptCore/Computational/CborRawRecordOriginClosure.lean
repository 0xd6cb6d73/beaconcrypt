-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginProbability
import BeaconcryptCore.Computational.CborRawRecordOriginCutEvent
import BeaconcryptCore.Computational.CborRawRecordOriginPublicationProbability

/-! The actual guarded raw record world has the explicit coefficient-two receive-times-send unpublished-origin bound. Every source cover, selected marker and fallible-writer failure is discharged from the same concrete execution; no whole-origin or event-simulation premise is supplied. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginClosure
open PqxdhRecordLiftIdeal hiding ctxRun
open CborRawRecordOriginObservation (ctxRun erasedRun)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The literal erased raw source has its same-run failed-writer cut bound. -/
theorem erased_unpublished_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[erasedRun modes replace setup codec route env serverKid bounds mode adversary]
      {result | UnpublishedAccept codec route (ctxView result)} ≤
      2 * (budget.receives : ENNReal) * budget.sends * ((2 ^ 512 : Nat) : ENNReal)⁻¹ := by
  exact CborRawRecordOriginProbability.source_event_bound modes ideal replace setup codec route
    env startup allowance framed serverKid bounds mode budget adversary respects
    (fun result => UnpublishedAccept codec route (ctxView result))
    (CborRawRecordOriginCutEvent.FailedCutEvent codec route)
    (CborRawRecordOriginCutEvent.source_cover modes ideal replace setup codec route readback env serverKid bounds mode budget adversary respects)
    (fun index cut selected => CborRawRecordOriginCutEvent.scan_marked modes ideal replace setup codec route env serverKid bounds mode adversary index.val cut selected)


/-- The complete actual raw source retains the explicit frozen publication term. -/
theorem ctxRun_unpublished_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤ publicationTerm budget := by
  rw [CborRawRecordOriginPublicationProbability.unpublished_probability modes ideal replace setup codec route env serverKid bounds mode adversary]
  exact (erased_unpublished_bound modes ideal replace setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects).trans_eq
    (PqxdhRecordFactsOriginPublicationProbability.publication_term budget)


/-- The actual cursor-wrapped arbitrary-client CTX world satisfies the concrete unpublished-origin bound at the explicit source bills. -/
theorem ctxRunOf_unpublished_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => unpublishedEvent codec route (ctxView result)) <$>
      PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
        (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary)] {true} ≤
      publicationTerm budget := by
  rw [CborRawRecordOriginObservation.ctxRunOf_eq]
  exact ctxRun_unpublished_bound modes ideal replace setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects

end BeaconcryptCore.Computational.CborRawRecordOriginClosure

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginClosure.erased_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginClosure.erased_unpublished_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginClosure.ctxRun_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginClosure.ctxRun_unpublished_bound
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginClosure.ctxRunOf_unpublished_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginClosure.ctxRunOf_unpublished_bound
