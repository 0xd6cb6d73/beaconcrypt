-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyLedger

/-! The native full-ledger client executes the same private World program as its transported old-record client. The result map restores only public creation metadata and drops the transport mailbox; all native environment state, raw replies and original private secrecy state remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyExecution
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {E Value Reader Response : Type}

def result (old : (Value × PqxdhDeploymentSecrecy.Ledger) × RegistrationNativeEntropyPort.State E) :
    (Value × RegistrationNativeLedger.State) × E :=
  ((old.1.1, RegistrationNativeEntropyRestore.ledger old.1.2), old.2.2)

/-- The complete original secrecy wrapper and the actual native environment commute through the full adaptive execution. -/
theorem wrapped (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (before : RegistrationNativeEntropyPort.State E) :
    result <$> (simulateQ (PqxdhRecordLiftInterface.native (RegistrationNativeEntropyPort.environment env))
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (RegistrationNativeEntropyCompile.compile .O work))).run before =
      (simulateQ (RegistrationNativeEntropyWorld.native env)
        (RegistrationNativeLedger.wrap crypto codec serverKid bounds work)).run before.2 := by
  calc
    _ = Prod.map id Prod.snd <$>
        (simulateQ (PqxdhRecordLiftInterface.native (RegistrationNativeEntropyPort.environment env))
          (Prod.map id RegistrationNativeEntropyRestore.ledger <$>
            PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
              (RegistrationNativeEntropyCompile.compile .O work))).run before := by
      simp only [simulateQ_map, StateT.run_map, Functor.map_map]
      rfl
    _ = Prod.map id Prod.snd <$>
        (simulateQ (PqxdhRecordLiftInterface.native (RegistrationNativeEntropyPort.environment env))
          (simulateQ RegistrationNativeEntropyCore.compiler
            (RegistrationNativeLedger.wrap crypto codec serverKid bounds work))).run before := by
      rw [RegistrationNativeEntropyLedger.wrap]
    _ = _ := by
      rw [← QueryImpl.simulateQ_compose]
      exact RegistrationNativeEntropyCore.program_drop env _ before

/-- The public Mode P wrapper commutes with transport while its original full Mode O ledger stays private. -/
theorem wrapped_mode (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeEntropyPort.State E) :
    result <$> (simulateQ (PqxdhRecordLiftInterface.native (RegistrationNativeEntropyPort.environment env))
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)))).run before =
      (simulateQ (RegistrationNativeEntropyWorld.native env)
        (RegistrationNativeLedger.wrap crypto codec serverKid bounds
          (RegistrationNativeInterface.asModeO mode work))).run before.2 := by
  cases mode with
  | O => exact wrapped env crypto codec serverKid bounds work before
  | P =>
      rw [← RegistrationNativeEntropyCompile.observation_program]
      exact wrapped env crypto codec serverKid bounds (RegistrationNativeInterface.asModeO .P work) before

end BeaconcryptCore.Computational.RegistrationNativeEntropyExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyExecution.wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyExecution.wrapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyExecution.wrapped_mode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyExecution.wrapped_mode
