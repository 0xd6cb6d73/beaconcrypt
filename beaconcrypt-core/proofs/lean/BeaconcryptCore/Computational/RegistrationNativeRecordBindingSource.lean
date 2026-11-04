-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingProgram
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills

/-! The actual initialized native record schedule has its retained-conflict bound in the counted original CTX interpretation. The loss uses the actual source startup and original typed-adversary budgets, including the one ML-pin hash, rather than an independent ideal world or a caller-supplied collision event bound. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativeRecordBindingProgram (erased)
open RegistrationNativeRecordOriginProgram (program)
open RegistrationNativeRecordPackage (Extra)
variable {n : Nat} {ι KemSK Reader Response E Value ProviderState : Type} {base : OracleSpec ι}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
  (setup : Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder)
  (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))

/-- Normalizing only the source counter and discarded private digest-cache completions retains this same execution's commitment-conflict event. -/
theorem observation (ideal : ∀ label, modes label ≠ .real) :
    LazyOracleDiscard.LawEq
      ((fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
        (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) (program codec route work)).run CtxPrivate.initial)
      ((fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
        erased modes replace setup codec route work) := by
  have same := (PqxdhRecordFactsPrivateCacheWorld.program_observation modes replace setup codec ideal
    (program codec route work) CtxPrivate.initial).map
    (fun result : PqxdhRecordLiftIdeal.Client n (Extra E) Value ×
      (PqxdhRecordLiftProtocol.Private n × (Label n → PqxdhRecordFactsPrivateCache.Local)) =>
      PqxdhRecordFactsBindingEvent.conflictEvent ⟨result.2.1, fun label => (result.2.2 label, ∅)⟩)
  simp only [Functor.map_map] at same
  convert same using 1 <;> congr 1

/-- The full actual counted native schedule has the collision bound at its source-derived seal and shared-hash caps. -/
theorem conflict_bound (ideal : ∀ label, modes label ≠ .real) (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (RegistrationNativeRecordPackage.client work))
    (hashCap : Nat) (hashes : PqxdhRecordLiftCtxProgramBounds.Weighted (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash)
      (program codec route work) hashCap) :
    𝒟[(fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) (program codec route work)).run CtxPrivate.initial] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  rw [(observation modes replace setup codec route work ideal).evalDist_eq]
  exact RegistrationNativeRecordBindingProgram.conflict_bound modes replace setup codec route work ideal budget records hashCap hashes

end BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource.observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource.observation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource.conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource.conflict_bound
