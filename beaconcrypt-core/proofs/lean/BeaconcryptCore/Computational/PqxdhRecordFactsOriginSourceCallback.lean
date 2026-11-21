-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh

/-! Source-derived hypotheses for every actual selected callback probability. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhRecordFactsOriginOrdinalCut (Cut resume scan)
open PqxdhRecordFactsOriginFailedResume (resumeMarked)
open PqxdhRecordFactsPrivateCacheSource (Reach)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace ((Client n E X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((Client n E X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- Every literal reached source seal has the complete callback bound, with freshness, initial dictionary, future exclusion, and raw query cap discharged from the source. -/
theorem reached_bound (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (cut : Cut n (Client n E X)) (ideal : modes cut.pending.material ≠ .real)
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past) :
    𝒟[resumeMarked modes setup codec replace cut] {result | result.2 = true} ≤
      2 * budget.receives * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  apply PqxdhRecordFactsOriginFailedCallback.marked_bound modes setup codec replace cut ideal
  · exact PqxdhRecordFactsPrivateCacheSource.source_prefix_fresh modes replace setup codec route env serverKid bounds mode adversary
      (.sealing cut.pending) cut.next cut.state cut.past reached
  · exact PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty modes replace setup codec route env serverKid bounds mode adversary
      cut.pending cut.next cut.state cut.past reached
  · exact PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next
      (PqxdhRecordFactsPrivateCacheSource.reach_fresh _
        (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary) reached) none
  · exact PqxdhRecordFactsOriginRawBounds.source_seal_continuation env startup allowance framed setup.source.crypto codec route
      serverKid bounds mode budget adversary respects (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      _ cut.state [] cut.past cut.pending cut.next reached none

/-- Each supported attempted-ordinal cut has the source-derived bound on its literal resumption, with only the concrete same-run event implication remaining. -/
theorem scan_event_bound (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : Frame env startup allowance) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (index : Nat) (cut : Cut n (Client n E X)) (ideal : modes cut.pending.material ≠ .real)
    (selected : Sum.inr cut ∈ support (scan (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      index (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []))
    (event : Client n E X × CtxPrivate n → Prop)
    (covered : ∀ result ∈ support (resumeMarked modes setup codec replace cut), event result.1 → result.2 = true) :
    𝒟[resume (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.inr cut)] {result | event result} ≤
      2 * budget.receives * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  exact (PqxdhRecordFactsOriginFailedResume.event_le_flag modes setup codec replace cut event covered).trans
    (reached_bound modes replace setup codec route env startup allowance framed serverKid bounds mode budget adversary respects cut ideal
      (PqxdhRecordFactsOriginOrdinalCut.scan_prefix _ _ index _ [] cut selected).1)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback.reached_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback.reached_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback.scan_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback.scan_event_bound
