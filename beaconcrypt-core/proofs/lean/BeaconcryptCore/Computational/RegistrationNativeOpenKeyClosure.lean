-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenCompile
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedStartupSource

/-! The actual retained/phase/key compiler stack can be closed with the same external KEM provider before or after compilation. These equalities follow from the real coin branches of both compilers and retain all adaptive prepare/demand dependencies. The real specialization can therefore be connected to the existing closed G2 experiment; a candidate specialization uses its own literal provider. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {KemSK ProviderState Value : Type}

def phaseCoins : QueryImpl unifSpec (OracleComp RegistrationNativeKeyPhases.Spec) :=
  fun query => RegistrationNativeKeyPhases.Spec.query (.inl query)

theorem phase_coin (query : unifSpec.Domain) (before : RegistrationNativeRetainedService.Flags) :
    (simulateQ RegistrationNativeRetainedService.compiler (RegistrationNativePublicRetained.coins query)).run before =
      (fun reply => (reply, before)) <$> phaseCoins query := by
  simp only [RegistrationNativePublicRetained.coins, simulateQ_spec_query,
    RegistrationNativeRetainedService.compiler, StateT.run_lift, bind_pure_comp]
  rfl

theorem key_coin (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : unifSpec.Domain) (before : RegistrationNativeKeyPhases.Meta) :
    (simulateQ (RegistrationNativeKeyCompiler.compiler source input inside) (phaseCoins query)).run before =
      (fun reply => (reply, before)) <$> RegistrationNativeKeyCompiler.coins query := by
  simp only [phaseCoins, simulateQ_spec_query, RegistrationNativeKeyCompiler.compiler,
    RegistrationNativeKeyCompiler.liftProb, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query]
  rfl

private theorem extend_phase :
    RegistrationNativeOpenCompile.extend RegistrationNativeRetainedService.compiler =
      (RegistrationNativeOpenKey.phaseCompiler : QueryImpl (RegistrationNativeOpenRetained.Spec KemSK)
        (StateT RegistrationNativeRetainedService.Flags (OracleComp (RegistrationNativeOpenKey.PhaseSpec KemSK)))) := by
  funext query
  cases query <;> rfl

private theorem extend_key (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    RegistrationNativeOpenCompile.extend (RegistrationNativeKeyCompiler.compiler source input inside) =
      (RegistrationNativeOpenKey.keyCompiler source input inside : QueryImpl (RegistrationNativeOpenKey.PhaseSpec KemSK)
        (StateT RegistrationNativeKeyPhases.Meta (OracleComp (RegistrationNativeOpenKey.Spec KemSK)))) := by
  funext query
  cases query <;> rfl

private theorem close_retained (provider : RegistrationNativeProviderInterpreter.Provider KemSK ProviderState) :
    RegistrationNativeOpenCompile.close RegistrationNativePublicRetained.coins provider =
      RegistrationNativeOpenRetainedSource.close provider := by
  funext query
  cases query <;> rfl

/-- Closing the same provider commutes with the public preparation-flag compiler. -/
theorem phase_close (provider : RegistrationNativeProviderInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value)
    (before : PqxdhLiveKemBirth.Pool KemSK × ProviderState) :
    (simulateQ (RegistrationNativeOpenCompile.close phaseCoins provider)
      (RegistrationNativeOpenKey.phaseClient work)).run' before =
      RegistrationNativeRetainedService.client
        ((simulateQ (RegistrationNativeOpenRetainedSource.close provider) work).run' before) := by
  have actual := RegistrationNativeOpenCompile.client_swap RegistrationNativeRetainedService.compiler
    RegistrationNativePublicRetained.coins phaseCoins phase_coin provider work before (fun _ => false)
  rw [extend_phase, close_retained] at actual
  exact actual.symm

/-- Closing the same provider commutes with the complete root-free key compiler, retaining prepare-time flags and dependent known replies. -/
theorem key_close (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (provider : RegistrationNativeProviderInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value)
    (before : PqxdhLiveKemBirth.Pool KemSK × ProviderState) :
    (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
      (RegistrationNativeOpenKey.client source input inside work)).run' before =
      RegistrationNativeKeyCompiler.client source input inside
        (RegistrationNativeRetainedService.client
          ((simulateQ (RegistrationNativeOpenRetainedSource.close provider) work).run' before))
        RegistrationNativeKeyPhases.emptyMeta := by
  have closed := RegistrationNativeOpenCompile.client_swap (RegistrationNativeKeyCompiler.compiler source input inside)
    phaseCoins RegistrationNativeKeyCompiler.coins (key_coin source input inside) provider
    (RegistrationNativeOpenKey.phaseClient work) before RegistrationNativeKeyPhases.emptyMeta
  rw [extend_key] at closed
  have same : RegistrationNativeKeyCompiler.client source input inside
      ((simulateQ (RegistrationNativeOpenCompile.close phaseCoins provider)
        (RegistrationNativeOpenKey.phaseClient work)).run' before) RegistrationNativeKeyPhases.emptyMeta =
        (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (RegistrationNativeOpenKey.client source input inside work)).run' before := by
    convert closed using 1 <;> rfl
  rw [phase_close] at same
  exact same.symm

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.phase_coin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.phase_coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.key_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.key_coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.phase_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.phase_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.key_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure.key_close
