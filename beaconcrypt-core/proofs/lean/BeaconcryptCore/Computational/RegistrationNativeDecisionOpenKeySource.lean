-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
import BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource
import BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment

/-! The complete real open key/KEM client closes to the exact global key adversary used by the actual-native G2 bound. The source challenges, optional generated startup, original full ledger and material dependencies remain inside this operator equality. A subsequent KEM candidate game is a separate hop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

theorem coins_close (provider : RegistrationNativeProviderInterpreter.Provider KemSK Unit)
    (work : ProbComp Value) (before : PqxdhLiveKemBirth.Pool KemSK × Unit) :
    (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
      (simulateQ RegistrationNativeOpenKeyStartup.coins work)).run before =
      (fun value => (value, before)) <$> simulateQ RegistrationNativeKeyCompiler.coins work := by
  apply RegistrationNativeOpenCompile.coin_program
  intro query state
  simp only [RegistrationNativeOpenKeyStartup.coins, QueryImpl.apply_compose,
    RegistrationNativeKeyCompiler.coins, simulateQ_spec_query, RegistrationNativeOpenKey.keyLift,
    RegistrationNativeOpenCompile.close, StateT.run_lift, bind_pure_comp]

/-- Closing the literal real KEM service in the complete generated open client recovers exactly the earlier global uniform-key client. -/
theorem client_real (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins (RegistrationNativeOpenRetainedReal.provider setup))
      (RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision)).run' (PqxdhLiveKemBirth.empty, ()) =
      RegistrationNativeDecisionKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision := by
  unfold RegistrationNativeOpenKeyStartup.client RegistrationNativeDecisionKeyExperiment.entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, coins_close, bind_map_left, map_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [← StateT.run'_eq, RegistrationNativeOpenKeyClosure.key_close,
    RegistrationNativeDecisionOpenRetainedSource.client_real]

end BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource.coins_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource.coins_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource.client_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionOpenKeySource.client_real
