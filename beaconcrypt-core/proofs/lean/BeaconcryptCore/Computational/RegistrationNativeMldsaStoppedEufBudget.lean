-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEuf
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateStoppedBounds

/-! The ordinary one-key EUF endpoint uses the actual native creation budget qCreate+1. The unchanged raw compiler supplies the finite generation allowance, including failed attempts, so no whole source-program or security premise is exposed. The event is the first actual protected-key candidate of the selected-first eager native experiment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)

/-- The actual bounded typed adversary needs exactly one startup generation plus its permitted creation slots. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (target : Fin (cap + 1)) :
    Pr{let won ← (RegistrationNativeMldsaStoppedEuf.game (n := n) source setup checks wire route representation adversary
      ensureInit identityIndex serverKeyId target)}[won = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary
          ensureInit identityIndex serverKeyId)) :=
  RegistrationNativeMldsaStoppedEuf.bound source setup checks wire route representation adversary ensureInit identityIndex serverKeyId
    target (RegistrationNativeMldsaGenerateStoppedBounds.program source setup checks wire route representation adversary cap bounded
      ensureInit identityIndex serverKeyId)

/-- Every original raw native mode and adaptive bounded adversary has the concrete selected-attempt ordinary EUF reduction, with finite tape size budget.create+1 derived from the actual compiler. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (target : Fin (budget.create + 1)) :
    Pr{let won ← (RegistrationNativeMldsaStoppedEuf.game (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      ensureInit identityIndex serverKeyId target)}[won = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          ensureInit identityIndex serverKeyId)) :=
  RegistrationNativeMldsaStoppedEuf.bound source setup checks wire route representation _ ensureInit identityIndex serverKeyId
    target (RegistrationNativeMldsaGenerateStoppedBounds.compiled source setup checks wire route representation bounds mode adversary budget bounded
      ensureInit identityIndex serverKeyId)
end BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget.compiled
