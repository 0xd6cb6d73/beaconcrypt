-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial

/-! The full native unchecked interpreter uses actual full-byte preparation and material requests, unchanged ordinary World callbacks and the literal evaluated KEM provider. The symbolic source differs only in representation of its private KEM words. The entire ledger, chronology, World and provider state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordCheckedClosure (Frame plain)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {ι KemSK Value ProviderState : Type} {base : OracleSpec ι}

abbrev NativeFrame (n : Nat) (KemSK ProviderState : Type) := RegistrationNativePublicInterpreter.State n KemSK × ProviderState
abbrev NativeProvider (KemSK ProviderState : Type) := QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK) (StateT ProviderState ProbComp)

def realized (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK) : NativeProvider KemSK (RegistrationNativeSecretWordKemProvider.State KemSK) := fun query before =>
  Prod.map (RegistrationNativeSecretWordKemProvider.evalReply candidate query) id <$> (provider query).run before

def ordinary (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) :
    StateT (NativeFrame n KemSK ProviderState) (OracleComp KeySpec) Value := fun before =>
  (fun result => (result.1, (RegistrationNativeOpenRetained.mask result.2, before.2))) <$>
    simulateQ RegistrationNativeKeyCompiler.coins
      (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac)
        (work.run (RegistrationNativeOpenRetained.mask before.1)))

noncomputable def native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (NativeFrame n KemSK ProviderState) (OracleComp KeySpec))
  | .inl (.inl message) => StateT.lift
      (pure ((RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message).map (fun _ => message)))
  | .inl (.inr (.inl (.inl message))) => StateT.lift
      (match RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message with
      | none => pure none
      | some bytes => (some ∘ RegistrationNativePairedChoice.Choice.known) <$>
          RegistrationNativeSecretWordNativeMaterial.material setup.source (RegistrationNativeKeyFamilyPreparation.inside target) bytes)
  | .inl (.inr (.inl (.inr query))) => ordinary setup.hmac (RegistrationNativePublicInterpreter.common setup wire sign query)
  | .inl (.inr (.inr query)) => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$>
        simulateQ RegistrationNativeKeyCompiler.coins ((provider query).run before.2)
  | .inr query => ordinary setup.hmac (RegistrationNativePublicInterpreter.world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
