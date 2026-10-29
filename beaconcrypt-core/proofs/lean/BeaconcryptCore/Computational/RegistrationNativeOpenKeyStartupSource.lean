-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
import BeaconcryptCore.Computational.RegistrationNativePublicKeyExperiment

/-! The complete real open key/KEM client closes to the exact global key adversary used by the actual-native G2 bound. The source challenges, optional generated startup, original full ledger and material dependencies remain inside this operator equality. A subsequent KEM candidate game is a separate hop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource
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
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) :
    (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins (RegistrationNativeOpenRetainedReal.provider setup))
      (RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds .P adversary
        (fun result => RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim
          (result.1, (result.2, ()))))).run' (PqxdhLiveKemBirth.empty, ()) =
      RegistrationNativePublicKeyExperiment.entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds budget claim adversary := by
  unfold RegistrationNativeOpenKeyStartup.client RegistrationNativePublicKeyExperiment.entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, coins_close, bind_map_left, map_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [← StateT.run'_eq, RegistrationNativeOpenKeyClosure.key_close,
    RegistrationNativeOpenRetainedStartupSource.client_real]

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource.coins_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource.coins_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource.client_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartupSource.client_real
