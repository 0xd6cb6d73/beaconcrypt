-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProvider
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler

/-! The concrete combined alias client closes every ordinary native callback with the actual retained World compiler and size-admitted record controller. Only the symbolic protected-key table and the extra ordinary suffix-key oracle remain external. The indexed KEM provider owns a separate genuine-key pool and ciphertext-only phase. Its state and the executable frontend contain no candidate bytes. The retained ordinary uniform-counter projection is explicit on both inputs and outputs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordService (Flags Combined)
open RegistrationNativeSecretWord (Key)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Provider (KemSK : Type) := QueryImpl (RegistrationNativeSecretWordKemInterface.Routed KemSK)
  (StateT (RegistrationNativeSecretWordKemProvider.State KemSK) ProbComp)

structure State (n : Nat) (KemSK : Type) where
  flags : Flags
  ordinary : RegistrationNativePublicInterpreter.State n KemSK
  kem : RegistrationNativeSecretWordKemProvider.State KemSK

abbrev M (n : Nat) (KemSK Value : Type) := StateT (State n KemSK) (OracleComp Combined) Value

def initial (before : RegistrationNativePublicInterpreter.State n KemSK)
    (providerState : RegistrationNativeSecretWordKemProvider.State KemSK) : State n KemSK :=
  ⟨fun _ => false, RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear before), providerState⟩

def roots (work : StateT Flags (OracleComp Combined) Value) : M n KemSK Value := fun before =>
  (fun result => (result.1, { before with flags := result.2 })) <$> work.run before.flags

def ordinary (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) : M n KemSK Value := fun before =>
  (fun result => (result.1, { before with ordinary := RegistrationNativeOpenRetained.mask result.2 })) <$>
    simulateQ RegistrationNativeSecretWordService.coins
      (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac)
        (work.run (RegistrationNativeOpenRetained.mask before.ordinary)))

def routed (provider : Provider KemSK) (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) :
    M n KemSK ((RegistrationNativeSecretWordKemInterface.Routed KemSK).Range query) := fun before =>
  (fun result => (result.1, { before with kem := result.2 })) <$>
    simulateQ RegistrationNativeSecretWordService.coins ((provider query).run before.kem)

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (M n KemSK)
  | .inl (.inl message) => roots (RegistrationNativeSecretWordService.handler (n := n) setup.source input inside (.inl message))
  | .inl (.inr (.inl (.inl message))) => roots (RegistrationNativeSecretWordService.handler (n := n) setup.source input inside (.inr message))
  | .inl (.inr (.inl (.inr query))) => ordinary setup.hmac (RegistrationNativePublicInterpreter.common setup wire sign query)
  | .inl (.inr (.inr query)) => routed provider query
  | .inr query => ordinary setup.hmac (RegistrationNativePublicInterpreter.world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))

noncomputable def execute (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value) (before : State n KemSK) :
    OracleComp Combined (Value × State n KemSK) :=
  (simulateQ (handler setup wire route sign input inside provider) work).run before

/-- Preparation changes only the exact symbolic descriptor flags, with ordinary World and the entire word KEM pool retained. -/
theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message : Message) (before : State n KemSK) :
    (handler setup wire route sign input inside provider (.inl (.inl message))).run before =
      pure ((input message).map (fun _ => message),
        { before with flags := Function.update before.flags message (input message).isSome }) := by
  simp only [handler, roots, StateT.run, RegistrationNativeSecretWordService.handler, map_pure]

/-- Indexed native KEM operations execute the same candidate-free provider on its complete current pool and phase. -/
theorem kem_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) (before : State n KemSK) :
    (handler setup wire route sign input inside provider (.inl (.inr (.inr query)))).run before =
      (fun result => (result.1, { before with kem := result.2 })) <$>
        simulateQ RegistrationNativeSecretWordService.coins ((provider query).run before.kem) := rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter.kem_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter.kem_run
