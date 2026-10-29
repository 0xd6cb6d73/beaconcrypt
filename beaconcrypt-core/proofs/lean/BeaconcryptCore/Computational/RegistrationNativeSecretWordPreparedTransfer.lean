-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource

/-! Actual flag-enforcing query prefixes coincide with checked prefixes once the native frontend has derived preparation internally. This transfers the reached live flag receipt itself, rather than only the final execution equality, so later source monitors can justify their actual protected material queries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (State Provider handler)
open RegistrationNativeSecretWordInterpreterChecked (Prefix AllPrepared handlerChecked)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)

/-- Every actual supported flag-service prefix is the identical checked prefix on all private fields. -/
theorem prefix_source (work residual : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before after : State n KemSK)
    (prepared : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before)
    (path : Prefix (handler setup wire route sign input inside provider) work before residual after) :
    Prefix (handlerChecked setup wire route sign input inside provider) work before residual after := by
  revert prepared
  induction path with
  | refl work before => intro _prepared; exact .refl work before
  | step query next before reply middle residual after supported later ih =>
      intro prepared
      have current := prepared query next before (.refl _ _)
      have checked : (reply, middle) ∈ support ((handlerChecked setup wire route sign input inside provider query).run before) := by
        rw [RegistrationNativeSecretWordInterpreterChecked.query_source setup wire route sign input inside provider query before current]
        exact supported
      apply Prefix.step query next before reply middle residual after checked
      apply ih
      intro later tail reached laterPath
      exact prepared later tail reached (.step query next before reply middle _ reached checked laterPath)

/-- The full preparation certificate therefore holds at actual flag-enforcing prefixes, not only in the checked source comparison. -/
theorem program (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value) (before : State n KemSK)
    (prepared : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before) :
    AllPrepared input (handler setup wire route sign input inside provider) work before := by
  intro query next after path
  exact prepared query next after (prefix_source setup wire route sign input inside provider _ _ before after prepared path)

/-- The exact complete chronological original native client derives actual prefix preparation internally from its empty session table. -/
theorem traced (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (empty : front.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    AllPrepared input (handler setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))
      (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  program setup wire route sign input inside provider _ _
    (RegistrationNativeSecretWordLiveFrontendSource.traced_prepared setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front empty ordinary kem)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.prefix_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer.traced
