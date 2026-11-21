-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedActual
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-! The actual established open native phase/key client closes through its original concrete early provider and equals the same initialized native full-ledger chronological execution. Only private compiler, ordinary and provider bookkeeping is erased by this value equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedOpenClient
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWordNativePlainProvider (embed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
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

private theorem client_map {A B : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (map : A → B) (work : OracleComp RegistrationNativeRetainedService.Spec A) :
    RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client (map <$> work)) RegistrationNativeKeyPhases.emptyMeta =
      map <$> RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work) RegistrationNativeKeyPhases.emptyMeta := by
  simp only [RegistrationNativeKeyCompiler.client, RegistrationNativeRetainedService.client,
    simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

noncomputable def client :=
  (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
    (RegistrationNativeOpenKey.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target)
      (RegistrationNativeOpenRetained.client setup wire route sign
        (RegistrationNativeG2Trace.program
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
            bounds mode work (before.eval candidate))) ordinary))).run'
    (RegistrationNativeSecretWordKemProvider.evalState candidate kem)

/-- The original open early native G2 client has the exact initialized full-ledger chronological output; preparation safety is derived from its actual cold frontend internally. -/
theorem client_source (empty : before.server.sessions = []) :
    client setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
      target selected pairs publicKey challenge candidate work before ordinary kem =
      Prod.fst <$> RegistrationNativeSecretWordNativePlainSource.run setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary kem := by
  rw [client, RegistrationNativeOpenKeyClosure.key_close]
  have actual := RegistrationNativeG3NativeCheckedActual.client_source setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary kem empty
  let full := RegistrationNativeG3NativeCheckedClient.retained setup wire route sign
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
    (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work (before.eval candidate))
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear ordinary))
    (RegistrationNativeSecretWordKemProvider.evalState candidate kem)
  have wrapped : (simulateQ (RegistrationNativeOpenRetainedSource.close
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
      (RegistrationNativeOpenRetained.client setup wire route sign
        (RegistrationNativeG2Trace.program
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
            bounds mode work (before.eval candidate))) ordinary)).run'
      (RegistrationNativeSecretWordKemProvider.evalState candidate kem) =
        (fun result => result.1.1) <$> full := by
    simp only [full, RegistrationNativeG3NativeCheckedClient.retained, RegistrationNativeOpenRetained.client,
      StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  rw [wrapped, client_map]
  change (fun result => result.1.1) <$>
    RegistrationNativeG3NativeCheckedActual.client setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary kem = _
  rw [actual]
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedOpenClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedOpenClient.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedOpenClient.client_source
