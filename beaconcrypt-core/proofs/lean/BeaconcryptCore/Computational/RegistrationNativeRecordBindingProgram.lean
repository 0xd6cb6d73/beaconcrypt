-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability

/-! The whole actual native World schedule compiles into one coherent private/ordinary digest cache. Actual startup and ML-pin hashes contribute their original source category bill. Its retained hidden commitment conflicts have the explicit two-class collision bound; no native cross-handle event inclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (categoryCost)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed)
open RegistrationNativeRecordPackage (Extra client)
open RegistrationNativeRecordOriginProgram (program)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
variable (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
local notation "start" => PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))

noncomputable def erased : ProbComp (Client n (Extra E) Value × CtxPrivate n) :=
  (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (program codec route work)).run start

/-- The complete native startup and adaptive continuation share one actual memoized private/ordinary digest cache. -/
theorem source_exact (ideal : ∀ label, modes label ≠ .real) :
    (simulateQ plain ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
      (program codec route work)).run start)).run ∅ = packed <$> erased modes replace setup codec route work := by
  rw [← PqxdhRecordFactsDigestCache.cacheOf_initial (n := n)]
  simpa only [PqxdhRecordFactsHashSource.compiled_self, erased] using
    PqxdhRecordFactsPrivateCacheSourceDrawMemo.program_compile (fun _ => $ᵗ CtxRomAuth.CtxDigest)
      (PqxdhRecordFactsHashSource.compiler modes replace setup codec) modes replace setup codec
      (PqxdhRecordFactsHashSource.ambient_exact modes replace setup codec) ideal (program codec route work) start []
      PqxdhRecordFactsPrivateCacheSource.initial_virgin (RegistrationNativeRecordOriginProgram.fresh codec route work)

/-- Real native source seal/hash category bills bound collision probability in that same compiled cache, including repeated hashes and failed writers. -/
theorem source_collision (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (client work))
    (hashCap : Nat) (hashes : Weighted (categoryCost .hash) (program codec route work) hashCap) :
    𝒟[(fun result => @decide (PqxdhRecordFactsCollisionCache.Collision PqxdhRecordFactsHashCollision.privateInput result.2)
      (Classical.propDecidable _)) <$>
      (simulateQ plain ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
        (program codec route work)).run start)).run ∅] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  apply PqxdhRecordFactsHashPairBills.ctx_collision_bound PqxdhRecordFactsHashCollision.privateInput
  · rw [PqxdhRecordFactsHashCollision.private_class]
    exact PqxdhRecordFactsHashPrivateBills.program_private modes replace setup codec _ budget.sends
      (RegistrationNativeRecordOriginProgram.seals codec route work budget records) _
  · rw [PqxdhRecordFactsHashCollision.ordinary_class]
    exact PqxdhRecordFactsHashOrdinaryBills.program_ordinary modes replace setup codec _ hashCap hashes _

/-- The bound reads the actual native schedule's retained combined cache, not a separately sampled digest world. -/
theorem erased_collision (ideal : ∀ label, modes label ≠ .real) (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (client work))
    (hashCap : Nat) (hashes : Weighted (categoryCost .hash) (program codec route work) hashCap) :
    𝒟[(fun result => @decide (PqxdhRecordFactsCollisionCache.Collision PqxdhRecordFactsHashCollision.privateInput
      (PqxdhRecordFactsDigestCache.cacheOf result.2)) (Classical.propDecidable _)) <$>
      erased modes replace setup codec route work] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  have bound := source_collision modes replace setup codec route work budget records hashCap hashes
  rw [source_exact modes replace setup codec route work ideal, Functor.map_map] at bound
  exact bound

/-- Every retained hidden commitment in this actual native schedule is cached at its literal private suffix input. -/
theorem cached (ideal : ∀ label, modes label ≠ .real)
    (result : Client n (Extra E) Value × CtxPrivate n)
    (supported : result ∈ support (erased modes replace setup codec route work)) :
    PqxdhRecordFactsBindingCache.AllCached result.2 :=
  PqxdhRecordFactsBindingCache.erased_program_cached modes ideal replace setup codec _ start
    PqxdhRecordFactsBindingCache.initial_cached result supported

/-- Native retained commitment conflict has the explicit collision term after actual source cache representation is discharged. -/
theorem conflict_bound (ideal : ∀ label, modes label ≠ .real) (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (client work))
    (hashCap : Nat) (hashes : Weighted (categoryCost .hash) (program codec route work) hashCap) :
    𝒟[(fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      erased modes replace setup codec route work] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  apply le_trans _ (erased_collision modes replace setup codec route work ideal budget records hashCap hashes)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result supported conflict
  exact @decide_eq_true _ (Classical.propDecidable _)
    (PqxdhRecordFactsBindingEvent.conflict_collision result.2
      (cached modes replace setup codec route work ideal result supported) (@of_decide_eq_true _ (Classical.propDecidable _) conflict))

end BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.source_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.source_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.source_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.erased_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.erased_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram.conflict_bound
