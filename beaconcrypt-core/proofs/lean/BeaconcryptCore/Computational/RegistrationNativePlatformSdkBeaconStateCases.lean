-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon
open CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases
universe u
variable [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
open beaconcrypt_public_wrapper.beacon
variable {U : Sort u} (value : BeaconState)
variable (fresh : ∀control prekey kem,value=.Fresh control prekey kem→U)
variable (withCoins : ∀control prekey oneTime kem,value=.FreshWithCoins control prekey oneTime kem→U)
variable (sent : ∀pending prekey oneTime kem,value=.InitSent pending prekey oneTime kem→U)
variable (established : ∀control binding manager,value=.Established control binding manager→U)
variable (aborted : ∀control,value=.Aborted control→U)

theorem rec_fresh (control :pqxdh.BeaconFresh) (prekey :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (selected :value=.Fresh control prekey kem) :
    BeaconState.rec (motive:=fun current=>value=current→U) fresh withCoins sent established aborted value rfl=
      fresh control prekey kem selected :=by
  cases selected
  rfl

theorem rec_withCoins (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (selected :value=.FreshWithCoins control prekey oneTime kem) :
    BeaconState.rec (motive:=fun current=>value=current→U) fresh withCoins sent established aborted value rfl=
      withCoins control prekey oneTime kem selected :=by
  cases selected
  rfl

theorem rec_sent (pending :registration.BeaconPending) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (selected :value=.InitSent pending prekey oneTime kem) :
    BeaconState.rec (motive:=fun current=>value=current→U) fresh withCoins sent established aborted value rfl=
      sent pending prekey oneTime kem selected :=by
  cases selected
  rfl

theorem rec_established (control :pqxdh.BeaconEstablished) (binding :session.SessionBinding) (manager :beaconcrypt_public_wrapper.ratchet.RatchetManager)
    (selected :value=.Established control binding manager) :
    BeaconState.rec (motive:=fun current=>value=current→U) fresh withCoins sent established aborted value rfl=
      established control binding manager selected :=by
  cases selected
  rfl

theorem rec_aborted (control :pqxdh.BeaconAborted)
    (selected :value=.Aborted control) :
    BeaconState.rec (motive:=fun current=>value=current→U) fresh withCoins sent established aborted value rfl=
      aborted control selected :=by
  cases selected
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_sent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_sent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_established

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_aborted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases.rec_aborted
