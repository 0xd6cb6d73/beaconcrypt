-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendPost

/-! The internal prepared-reference invariant is preserved by every adaptive typed program and by the literal original native secrecy compiler and full ledger. It starts from the generated empty Server session table and the concrete checked interpreter's empty flags. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveFrontendState (Good)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)

/-- Every supported adaptive typed execution retains valid flags and preparation of every stored Server reference. -/
theorem program_good (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeSecretWordMessage.State source) (context : State n KemSK)
    (good : Good input before context)
    (result : (Value × RegistrationNativeSecretWordMessage.State source) × State n KemSK)
    (supported : result ∈ support ((simulateQ (handlerChecked setup wire route sign input inside provider)
      ((simulateQ (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before)).run context)) :
    Good input result.1.2 result.2 := by
  induction work using OracleComp.inductionOn generalizing before context with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, called, supported⟩ := supported
      have nextGood := RegistrationNativeSecretWordLiveFrontendPost.query setup wire route sign input inside provider checks source
        selectedOwner selectedAccept publicPrekey query before context good reached called
      exact ih reached.1.1 reached.1.2 reached.2 nextGood supported

/-- The concrete initial flags and empty native capability table establish the internal invariant. -/
theorem initial (before : RegistrationNativeSecretWordMessage.State source)
    (empty : before.server.sessions = []) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    Good input before (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  ⟨RegistrationNativeSecretWordLiveFlags.initial input ordinary kem,
    RegistrationNativeSecretWordLiveSessions.initial before.server _ empty⟩

/-- The actual original full raw/secrecy ledger inherits the invariant from its concrete initialized Server table and private empty flags. -/
theorem run_good (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (empty : before.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) × State n KemSK)
    (supported : result ∈ support ((simulateQ (handlerChecked setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before)).run
        (RegistrationNativeSecretWordInterpreter.initial ordinary kem))) :
    Good input result.1.2 result.2 :=
  program_good setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before _
    (initial source input before empty ordinary kem) result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram.run_good
