-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedOpenClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable

/-! The original closed early native key client is the actual byte-indexed execution of the complete alias client. Its observation retains the full result, original ledger, native frontend and same chronological trace. This is an exact source equality before any literal-hit or statistical estimate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def view {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) :=
  Prod.map (Prod.map id (RegistrationNativeSecretWordMessage.State.eval candidate))
    (RegistrationNativeSecretWordCheckedTrace.state candidate) result.1

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
  (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (before : RegistrationNativeSecretWordMessage.State source)
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

noncomputable def aliasClient :=
  RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside target)
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before ordinary kem

/-- The original open early native key client is the real suffix interpretation of the same complete alias client, retaining its original full frontend observation. -/
theorem open_source (empty : before.server.sessions = []) :
    RegistrationNativeG3NativeCheckedOpenClient.client setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
      target selected pairs publicKey challenge candidate work before ordinary kem =
      simulateQ (RegistrationNativeSecretWordServiceSource.realize setup.source candidate)
        (view candidate <$> aliasClient setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode seed scalar target selected pairs publicKey challenge work before ordinary kem) := by
  rw [RegistrationNativeG3NativeCheckedOpenClient.client_source setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary kem empty,
    RegistrationNativeSecretWordNativePlainSource.run_source]
  simp only [RegistrationNativeSecretWordAliasReadiness.nativeRun]
  rw [RegistrationNativeSecretWordAliasSource.run_source setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode (RegistrationNativeSecretWordProtection.inside target)
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    candidate seed scalar work before empty ordinary kem]
  simp only [simulateQ_map, Functor.map_map, aliasClient, Prod.map_def, id_eq]
  rfl

private theorem bytes_handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : MlKemSharedSecret) :
    PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ RegistrationNativeSecretWordServiceSource.realize source candidate =
      RegistrationNativeSecretWordRecoveryBound.bytes source candidate := by
  funext query before
  rcases query with (coin | key) | head
  all_goals simp only [QueryImpl.compose, RegistrationNativeSecretWordServiceSource.realize,
    simulateQ_spec_query, simulateQ_pure, RegistrationNativeSecretWordRecoveryBound.bytes,
    RegistrationNativeSecretWordSource.byteSource, PqxdhRegistrationJointKemSecondEntry.lazyImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
  all_goals rfl

/-- Closing the original lazy108-byte table gives precisely the same full native frontend observation in the actual byte-view alias execution, for each mathematical candidate. -/
theorem bytes_source (empty : before.server.sessions = []) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
      (RegistrationNativeG3NativeCheckedOpenClient.client setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
        target selected pairs publicKey challenge candidate work before ordinary kem)).run' ∅ =
      view candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
        (aliasClient setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode seed scalar target selected pairs publicKey challenge work before ordinary kem)).run' ∅ := by
  rw [open_source setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
    target selected pairs publicKey challenge candidate work before ordinary kem empty,
    ← QueryImpl.simulateQ_compose, bytes_handler]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource.open_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource.open_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource.bytes_source
