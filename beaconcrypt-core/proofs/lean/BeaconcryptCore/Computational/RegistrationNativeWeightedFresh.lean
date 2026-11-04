-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector
import BeaconcryptCore.Computational.RegistrationNativeEntropyFresh

/-! Selector-weighted entropy in the actual native random-record experiment. The selector is the finite public-transcript computation, not a predicate on private messages or a hidden good-state condition. Both the winning event and its selector mass are transported through the actual native entropy interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedFresh
open RegistrationNativeCanonicalSelector (Target selected analysisSelector)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK E Value Reader Response : Type} {base : OracleSpec ι}

noncomputable def selection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (result : RegistrationNativeEntropyRun.Result n E Value) : Bool :=
  match result.1.1 with
  | none => false
  | some born => selected crypto wire serverKeyId budget claim target born.2.1.1 born.2.1.2

noncomputable def winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (result : RegistrationNativeEntropyRun.Result n E Value) : Bool :=
  selection crypto wire serverKeyId budget claim target result && RegistrationNativeEntropyFresh.event claim result

theorem project_selection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value ×
      PqxdhRecordLiftIdeal.CtxPrivate n) :
    selection crypto wire serverKeyId budget claim target (RegistrationNativeEntropyRun.project old) =
      analysisSelector crypto wire serverKeyId budget claim target
        (PqxdhRecordLiftIdeal.publicHiding (PqxdhRecordLiftIdeal.ctxView old)) := by
  rcases old with ⟨⟨born, control⟩, secret⟩
  cases born with
  | none => rfl
  | some born =>
      simpa only [selection, RegistrationNativeEntropyRun.project, RegistrationNativeEntropyProgram.outcome,
        RegistrationNativeEntropyExecution.result, PqxdhRecordLiftIdeal.ctxView,
        PqxdhRecordLiftIdeal.viewOf, Option.map_some, Prod.map_def, id_eq] using
        (RegistrationNativeCanonicalSelector.analysis_exact crypto wire serverKeyId budget claim target
          born.2.1.1 born.2.1.2 born.2.2 secret.base.produced (PqxdhRecordLiftProtocol.rawCounters control)
          (PqxdhRecordLiftIdeal.handleSlot control)).symm

theorem project_winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value ×
      PqxdhRecordLiftIdeal.CtxPrivate n) :
    winning crypto wire serverKeyId budget claim target (RegistrationNativeEntropyRun.project old) =
      (analysisSelector crypto wire serverKeyId budget claim target
        (PqxdhRecordLiftIdeal.publicHiding (PqxdhRecordLiftIdeal.ctxView old)) &&
          PqxdhRecordLiftIdeal.freshEvent claim (PqxdhRecordLiftIdeal.ctxView old)) :=
  congrArg₂ (fun first second : Bool => first && second)
    (project_selection crypto wire serverKeyId budget claim target old)
    (RegistrationNativeEntropyFresh.project_event claim old)

/-- Native selector-weighted entropy retains the original messages and complete execution, with the same selector probability on the right. -/
theorem fresh_bytes (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (env : RegistrationNativeEntropyInterface.Environment n E)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget) :
    𝒟[winning setup.source.crypto wire serverKeyId budget claim target <$>
      RegistrationNativeEntropyRun.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
        route env serverKeyId bounds .P work] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[selection setup.source.crypto wire serverKeyId budget claim target <$>
          RegistrationNativeEntropyRun.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
            route env serverKeyId bounds .P work] {true} := by
  rw [← RegistrationNativeEntropyRun.run_transport]
  simp only [Functor.map_map, project_winning, project_selection]
  exact CborRawRecordWeightedFresh.fresh_bytes setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeEntropyPort.environment env) serverKeyId bounds
    (RegistrationNativeEntropyCompile.compile .P work) claim
    (analysisSelector setup.source.crypto wire serverKeyId budget claim target)

end BeaconcryptCore.Computational.RegistrationNativeWeightedFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.project_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.project_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.project_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.project_winning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedFresh.fresh_bytes
