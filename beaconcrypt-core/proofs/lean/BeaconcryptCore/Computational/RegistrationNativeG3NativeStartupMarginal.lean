-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-! The original startup client's candidate-independent ledger decision is the pure marginal of the complete unchanged startup/value client. Actual constructor, ML pin hash and reached World are retained before the decision erases extra trace and context. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK A B Value : Type} {base : OracleSpec ι}

def phaseCoins : QueryImpl unifSpec (OracleComp (RegistrationNativeOpenKey.PhaseSpec KemSK)) :=
  RegistrationNativeOpenKey.phaseLift ∘ₛ RegistrationNativeOpenKeyClosure.phaseCoins

private theorem phase_coin (query : unifSpec.Domain) (flags : RegistrationNativeRetainedService.Flags) :
    (simulateQ RegistrationNativeOpenKey.phaseCompiler (RegistrationNativeOpenRetainedStartup.coins query)).run flags =
      (fun reply => (reply, flags)) <$> (phaseCoins (KemSK := KemSK) query) := by
  simp only [RegistrationNativeOpenRetainedStartup.coins, RegistrationNativePublicRetained.coins,
    QueryImpl.apply_compose, simulateQ_spec_query, RegistrationNativeOpenRetained.baseLift,
    RegistrationNativeOpenKey.phaseCompiler, RegistrationNativeRetainedService.compiler, StateT.run,
    StateT.lift, simulateQ_map, simulateQ_spec_query, bind_pure_comp,
    phaseCoins, RegistrationNativeOpenKeyClosure.phaseCoins, RegistrationNativeOpenKey.phaseLift]
  rfl

private theorem key_coin (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : unifSpec.Domain) (metadata : RegistrationNativeKeyPhases.Meta) :
    (simulateQ (RegistrationNativeOpenKey.keyCompiler keySource input inside) (phaseCoins query)).run metadata =
      (fun reply => (reply, metadata)) <$> (RegistrationNativeG3NativeStartupUniformValue.coins (KemSK := KemSK) query) := by
  simp only [phaseCoins, RegistrationNativeOpenKeyClosure.phaseCoins, RegistrationNativeOpenKey.phaseLift,
    QueryImpl.apply_compose, simulateQ_spec_query, RegistrationNativeOpenKey.keyCompiler,
    RegistrationNativeKeyCompiler.compiler, RegistrationNativeKeyCompiler.liftProb, StateT.run,
    StateT.lift, simulateQ_map, simulateQ_spec_query, bind_pure_comp, RegistrationNativeG3NativeStartupUniformValue.coins,
    RegistrationNativeOpenKey.keyLift, RegistrationNativeKeyCompiler.coins]
  rfl

/-- Actual startup probability draws commute through the real two-pass compiler without changing its private metadata. -/
theorem client_prefix (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (prior : ProbComp A) (next : A → OracleComp (RegistrationNativeOpenRetained.Spec KemSK) B) :
    RegistrationNativeOpenKey.client keySource input inside
      (simulateQ RegistrationNativeOpenRetainedStartup.coins prior >>= next) =
      (simulateQ RegistrationNativeG3NativeStartupUniformValue.coins prior >>= fun value =>
        RegistrationNativeOpenKey.client keySource input inside (next value)) := by
  have first := RegistrationNativeOpenCompile.coin_program (RegistrationNativeOpenKey.phaseCompiler (KemSK := KemSK))
    RegistrationNativeOpenRetainedStartup.coins phaseCoins phase_coin prior (fun _ => false)
  have second := RegistrationNativeOpenCompile.coin_program (RegistrationNativeOpenKey.keyCompiler (KemSK := KemSK) keySource input inside)
    phaseCoins RegistrationNativeG3NativeStartupUniformValue.coins (key_coin keySource input inside) prior RegistrationNativeKeyPhases.emptyMeta
  simp only [RegistrationNativeOpenKey.client, RegistrationNativeOpenKey.phaseClient, StateT.run'_eq,
    simulateQ_bind, StateT.run_bind, map_bind, first, bind_map_left, simulateQ_map, StateT.run_map,
    Functor.map_map, second]

/-- Both complete compiler passes preserve a pure final output observation. -/
theorem client_map (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (map : A → B) (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) A) :
    RegistrationNativeOpenKey.client keySource input inside (map <$> work) =
      map <$> RegistrationNativeOpenKey.client keySource input inside work := by
  simp only [RegistrationNativeOpenKey.client, RegistrationNativeOpenKey.phaseClient, StateT.run'_eq,
    simulateQ_map, StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal.client_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal.client_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal.client_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupMarginal.client_map
