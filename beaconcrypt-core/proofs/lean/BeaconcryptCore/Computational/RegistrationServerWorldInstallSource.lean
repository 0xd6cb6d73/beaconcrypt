-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSigningWorldSource

/-! Concrete Server occupancy and known-kernel installation ignore exactly the private analysis coordinates omitted by the source view. Their actual vacancy/current-state decisions and complete transferred binding/kernel remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerWorldInstallSource
variable {n : Nat}

/-- Occupancy reads the actual live peer map and retains the source-view World. -/
theorem occupancy (keyId : U64) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeWorldView.project <$>
      (PqxdhRecordLiftWorld.effects (.inr (.peerPresent keyId))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.peerPresent keyId))).run (RegistrationNativeWorldView.project before) := by
  have distinct : PqxdhRecordLiftInterface.EffectKind.administrative ≠ .coin := by decide
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    map_pure, Prod.map_def, id_eq, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    PqxdhRecordLiftWorld.chargeEffect, PqxdhRecordLiftInterface.effectKind,
    Function.update_of_ne distinct, Function.update_comm distinct]

/-- Actual known-kernel insertion retains its exact vacancy test, transferred peer and full native World after the stated analysis view. -/
theorem install (keyId : U64) (identity : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeWorldView.project <$>
      (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId identity (.known kernel)))).run before =
      (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId identity (.known kernel)))).run
        (RegistrationNativeWorldView.project before) := by
  have distinct : PqxdhRecordLiftInterface.EffectKind.administrative ≠ .coin := by decide
  cases available : before.server with
  | none =>
      simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
        PqxdhRecordLiftWorld.installServer, PqxdhRecordLiftWorld.chargeEffect,
        RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
        RegistrationWorldCoinCompiler.eraseCoin, available, StateT.run, map_pure, Prod.map_def, id_eq, PqxdhRecordLiftInterface.effectKind,
        Function.update_of_ne distinct, Function.update_comm distinct]
  | some server =>
      by_cases vacant : server.records.server.peers keyId = none
      · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
          PqxdhRecordLiftWorld.installServer, PqxdhRecordLiftWorld.chargeEffect,
          RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
          RegistrationWorldCoinCompiler.eraseCoin, available, vacant, true_and,
          PqxdhRecordLiftWorld.Unused, PqxdhRecordLiftWorld.resolve,
          PqxdhRecordLiftWorld.markUsed, StateT.run, StateT.monad_pure_def, StateT.pure, pure_bind, map_pure,
          Prod.map_def, id_eq, ite_true, PqxdhRecordLiftInterface.effectKind,
          Function.update_of_ne distinct, Function.update_comm distinct]
      · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
          PqxdhRecordLiftWorld.installServer, PqxdhRecordLiftWorld.chargeEffect,
          RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
          RegistrationWorldCoinCompiler.eraseCoin, available, vacant, false_and, ite_false,
          StateT.run, map_pure, Prod.map_def, id_eq, PqxdhRecordLiftInterface.effectKind,
          Function.update_of_ne distinct, Function.update_comm distinct]

end BeaconcryptCore.Computational.RegistrationServerWorldInstallSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldInstallSource.occupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldInstallSource.occupancy
/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldInstallSource.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldInstallSource.install
