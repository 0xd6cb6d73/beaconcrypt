-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceCallback
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability

/-! Actual source attempted-ordinal averaging with explicit semantic event obligations. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhRecordFactsOriginOrdinalCut (Cut resume scan)
open PqxdhRecordFactsOriginOrdinalTrace (track)
open PqxdhRecordFactsOriginFailedResume (resumeMarked)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
local instance : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The actual complete source experiment has the coefficient-two receive-times-send bound once its concrete event is covered by same-run failed-writer match events at attempted sealing cuts. -/
theorem source_event_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (sourceEvent : Client n E X × CtxPrivate n → Prop)
    (event : Cut n (Client n E X) → Client n E X × CtxPrivate n → Prop)
    (covered : ∀ result ∈ support (track (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []), sourceEvent result.2 →
        ∃ cut ∈ result.1, event cut result.2)
    (marked : ∀ index : Fin budget.sends, ∀ cut,
      Sum.inr cut ∈ support (scan (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
        index.val (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []) →
      ∀ result ∈ support (resumeMarked modes setup codec replace cut), event cut result.1 → result.2 = true) :
    𝒟[(simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)] {result | sourceEvent result} ≤
      2 * budget.receives * budget.sends * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  have bound := PqxdhRecordFactsOriginOrdinalProbability.source_event_bound
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] sourceEvent event budget.sends
    (2 * budget.receives * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹)
    (PqxdhRecordFactsHashSealBills.program_seals env setup.source.crypto codec route serverKid bounds mode budget adversary respects)
    covered (fun index cut selected => PqxdhRecordFactsOriginSourceCallback.scan_event_bound modes replace setup codec route
      env startup allowance framed serverKid bounds mode budget adversary respects index.val cut (ideal _) selected
      (event cut) (marked index cut selected))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using bound

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability.source_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability.source_event_bound
