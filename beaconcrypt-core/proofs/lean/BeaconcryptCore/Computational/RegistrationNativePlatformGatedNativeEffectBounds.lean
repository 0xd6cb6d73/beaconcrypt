-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedEffectBounds
import BeaconcryptCore.Computational.RegistrationNativeEntropyFrame

/-! The actual native gated stage inherits explicit source-effect bills through the real entropy compiler. Its conservative transport budget includes the metadata command class, while the public allocator has a separate narrow uniform cap. Full state, failure poststates, original mode and ledger remain; genuine startup is charged separately. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (EffectKind Caps)
open PqxdhRecordLiftBudget (WorldEffect)
open PqxdhDeploymentInterface (Mode FreshBounds Budget)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {E Failure V Reader Response : Type}

def effectBudget (budget : Budget) (bounds : FreshBounds) (allowance : Fin 14 → EffectKind → Nat)
    (reserveCoins : Nat) (kind : EffectKind) : Nat :=
  PqxdhRecordLiftBudget.directCost (RegistrationNativeEntropyBounds.budget budget) bounds kind +
    (∑ queryKind : Fin 14, (RegistrationNativeEntropyBounds.budget budget).cap queryKind * allowance queryKind kind) +
    RegistrationNativePlatformGatedEffectBounds.reserveCost reserveCoins kind * budget.sends

private theorem reserve_lift (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (coins : Nat)
    (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound coins)
    (amount : Nat) (before : RegistrationNativeEntropyPort.State E) :
    ((RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve amount).run before).IsTotalQueryBound coins := by
  simpa only [RegistrationNativePlatformGatedNativeEntropy.reserveLift, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff] using bounded amount before.2

/-- The complete original native ledger wrapper has the explicit transported environment bill plus the separate reached-reserve coin allowance. -/
theorem wrapped (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : RegistrationNativeEntropyFrame.Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (reserveCoins : Nat)
    (boundedReserve : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound reserveCoins)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : E) (kind : EffectKind) :
    ((simulateQ (RegistrationNativePlatformGatedNativeEntropy.native env reserve)
      (RegistrationNativeLedger.wrap crypto codec serverKeyId bounds (RegistrationNativeInterface.asModeO mode work))).run before).IsQueryBoundP
      (WorldEffect kind) (effectBudget budget bounds allowance reserveCoins kind) := by
  have old := RegistrationNativePlatformGatedEffectBounds.wrapped_bound
    (RegistrationNativeEntropyPort.environment env) startup allowance
    (RegistrationNativeEntropyFrame.environment_frame env startup allowance framed)
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) reserveCoins
    (reserve_lift reserve reserveCoins boundedReserve)
    crypto codec serverKeyId bounds mode (⟨RegistrationNativeEntropyBounds.budget budget, 0⟩ : Caps)
    (RegistrationNativeEntropyCompile.compile mode work)
    (RegistrationNativeEntropyBounds.compile_respects mode work budget bounded) kind ([], before)
  rw [← RegistrationNativePlatformGatedNativeEntropy.wrapped_mode env reserve crypto codec serverKeyId bounds mode work ([], before)]
  apply (isQueryBoundP_map_iff _ _ _).mpr
  simpa only [effectBudget, Caps.envTotal, (RegistrationNativeEntropyBounds.retained_budget budget bounds).1] using old

/-- The literal native stage keeps this same effect budget, without charging its separately executed genuine startup twice. -/
theorem program (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : RegistrationNativeEntropyFrame.Frame env startup allowance)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (reserveCoins : Nat)
    (boundedReserve : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound reserveCoins)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V) (bounded : RegistrationNativeInterface.Respects budget work)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : E) (kind : EffectKind) :
    (RegistrationNativePlatformGatedNativeEntropy.program env reserve crypto codec serverKeyId bounds mode work created before).IsQueryBoundP
      (WorldEffect kind) (effectBudget budget bounds allowance reserveCoins kind) := by
  unfold RegistrationNativePlatformGatedNativeEntropy.program
  rw [isQueryBoundP_map_iff]
  exact wrapped env startup allowance framed reserve reserveCoins boundedReserve crypto codec serverKeyId bounds mode budget work bounded before kind

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds.wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds.wrapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds.program
