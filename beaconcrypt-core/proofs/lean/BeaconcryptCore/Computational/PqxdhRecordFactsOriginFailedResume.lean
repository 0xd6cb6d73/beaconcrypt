-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut

/-! Full original selected resumption with an erased-source failed-writer match flag. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginOrdinalCut (Cut resume)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (X × CtxPrivate n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩

/-- Execute the literal selected callback and full original continuation; mark only a failed selected writer followed by a selected replay match. -/
noncomputable def resumeMarked (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) : ProbComp ((X × CtxPrivate n) × Bool) := do
  let reply ← (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state
  let result ← (simulateQ (marked cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) (cut.next reply.1)).run (reply.2, false)
  pure ((result.1, result.2.1), reply.1.isNone && result.2.2)

/-- Erasing only the analysis flag restores the complete original selected callback and actual continuation in the same source experiment. -/
theorem resume_marked_erase (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) :
    Prod.fst <$> resumeMarked modes setup codec replace cut =
      resume (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.inr cut) := by
  simp only [resumeMarked, resume, map_bind, map_pure]
  apply bind_congr
  intro reply
  simp only [bind_pure_comp]
  convert PqxdhRecordFactsOriginMuteAdaptive.complete_erase cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (cut.next reply.1) (reply.2, false) using 1
  congr 1


/-- Any actual final-result event that forces the failed-writer match flag on every supported execution is bounded by that flag's probability. -/
theorem event_le_flag (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) (event : X × CtxPrivate n → Prop)
    (covered : ∀ result ∈ support (resumeMarked modes setup codec replace cut), event result.1 → result.2 = true) :
    𝒟[resume (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.inr cut)] {result | event result} ≤
      𝒟[resumeMarked modes setup codec replace cut] {result | result.2 = true} := by
  rw [← resume_marked_erase modes setup codec replace cut, ← prEvent_eq_evalDist_of_discrete,
    ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  exact prEvent_mono_of_support _ _ _ covered

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume.resume_marked_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume.resume_marked_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume.event_le_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume.event_le_flag
