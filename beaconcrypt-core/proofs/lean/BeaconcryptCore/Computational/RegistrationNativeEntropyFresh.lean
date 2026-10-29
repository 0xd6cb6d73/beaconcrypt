-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyRun

/-! Byte-accurate fresh-message guessing in the actual native ML-pin-aware cursor-filtered record-ideal world. The hidden-handle predicate reads the actual installed record origins, and the original private fresh entry is retained literally. No target/session-count multiplier or desired-game equality is assumed. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyFresh
open RegistrationNativeEntropyInterface (Environment)
open RegistrationNativeEntropyRun (Result run project)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK E Value Reader Response : Type} {base : OracleSpec ι}

def FreshHit (claim : Value → Option (Nat × Pqxdh.Bytes)) (result : Result n E Value) : Prop :=
  ∃ born ∈ result.1.1, ∃ index guess entry, claim born.2.1.1 = some (index, guess) ∧
    born.2.1.2.ledger.fresh[index]? = some entry ∧
    (PqxdhRecordLiftIdeal.handleSlot result.1.2 entry.handle).isSome ∧ entry.message = guess

noncomputable def event (claim : Value → Option (Nat × Pqxdh.Bytes)) (result : Result n E Value) : Bool :=
  @decide (FreshHit claim result) (Classical.propDecidable _)

/-- Native restoration keeps the exact fresh hit and the actual hidden-origin map of the transported record world. -/
theorem project_event (claim : Value → Option (Nat × Pqxdh.Bytes))
    (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value ×
      PqxdhRecordLiftIdeal.CtxPrivate n) :
    event claim (project old) = PqxdhRecordLiftIdeal.freshEvent claim (PqxdhRecordLiftIdeal.ctxView old) := by
  classical
  rcases old with ⟨⟨born, control⟩, secret⟩
  cases born with
  | none =>
      simp [event, FreshHit, project, RegistrationNativeEntropyProgram.outcome,
        PqxdhRecordLiftIdeal.freshEvent, PqxdhRecordLiftIdeal.FreshHit,
        PqxdhRecordLiftIdeal.ctxView, PqxdhRecordLiftIdeal.viewOf]
  | some born =>
      simp only [event, PqxdhRecordLiftIdeal.freshEvent]
      apply decide_eq_decide.mpr
      simp [FreshHit, project, RegistrationNativeEntropyProgram.outcome,
        RegistrationNativeEntropyExecution.result, RegistrationNativeEntropyRestore.ledger,
        PqxdhRecordLiftIdeal.ctxView, PqxdhRecordLiftIdeal.viewOf, PqxdhRecordLiftIdeal.FreshHit]

/-- The native random-record ideal world has the exact byte guessing term, with the original full private ledger and cursor refusals. -/
theorem fresh_bytes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    𝒟[event claim <$> run (fun _ => .random) id setup codec route env serverKid bounds .P work] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← RegistrationNativeEntropyRun.run_transport, Functor.map_map]
  simp only [project_event]
  exact CborRawRecordFresh.fresh_bytes setup codec route (RegistrationNativeEntropyPort.environment env)
    serverKid bounds (RegistrationNativeEntropyCompile.compile .P work) claim

end BeaconcryptCore.Computational.RegistrationNativeEntropyFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyFresh.project_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyFresh.project_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyFresh.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyFresh.fresh_bytes
