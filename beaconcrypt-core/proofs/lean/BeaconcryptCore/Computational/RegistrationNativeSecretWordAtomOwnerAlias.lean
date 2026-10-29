-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient

/-! The Beacon atom-attempt conservation law applies to the exact complete alias client after its outer Combined oracle is closed. The result retains its full original ledger, frontend, observer and private provider state. This is a supported-execution statement for an actual closed oracle, not a byte-cache statelessness assertion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAlias
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The actual complete alias-client trace has at most one Beacon atom installation attempt under any closed outer table replies. -/
theorem client_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) (owners : front.beacons = []) (keys : kem.1.keys = [])
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
      selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem))) :
    RegistrationNativeSecretWordAtomInstallTrace.count .beacon result.1.2 ≤ 1 := by
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
  have actual : result ∈ support ((simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer)
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler (RegistrationNativeSecretWordFrontend.run setup checks wire source sign
        selected selectedAccept publicPrekey serverKeyId bounds mode work front)).run RegistrationNativeSecretWordFrontendTrace.initial)).run
          (RegistrationNativeSecretWordInterpreter.initial ordinary kem)) := by
    change result ∈ support ((simulateQ (outer.mapStateTBase
      (RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider))
      (RegistrationNativeSecretWordFrontendTrace.program (RegistrationNativeSecretWordFrontend.run setup checks wire source sign
        selected selectedAccept publicPrekey serverKeyId bounds mode work front))).run
          (RegistrationNativeSecretWordInterpreter.initial ordinary kem))
    rw [← QueryImpl.simulateQ_mapStateTBase_run]
    exact supported
  rw [← RegistrationNativeSecretWordAtomTracedSource.run_trace setup wire route sign input inside provider outer checks selected selectedAccept publicPrekey
    serverKeyId bounds mode work (front, RegistrationNativeSecretWordFrontendTrace.initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem), support_map] at actual
  obtain ⟨reached, called, equal⟩ := actual
  cases equal
  exact RegistrationNativeSecretWordAtomOwnerAttempts.run_one setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedAccept publicPrekey serverKeyId bounds mode work front (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
      owners keys reached called

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAlias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAlias.client_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAlias.client_one
