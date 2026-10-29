-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram

/-! The complete original raw secrecy ledger and its actual native G2 trace have the evaluated symbolic frontend source. This theorem consumes the concrete audited per-command source and both chronological observer equations. It retains the full final frontend, original ledger and all prepare/demand/encapsulation/install events; no whole-program or trace correspondence is supplied by the caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTypedTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State input)
open RegistrationNativeSecretWordCheckedFrontend (erase native implementation)
open RegistrationNativeSecretWordCheckedTrace (handler state)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The actual complete native secrecy run and native chronological G2 trace are precisely the evaluated symbolic run and symbolic trace under the concrete checked source. -/
theorem query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) :
    simulateQ (erase ∘ₛ native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run (before.eval candidate))).run (state candidate trace)) =
      Prod.map (Prod.map id (State.eval candidate)) (state candidate) <$>
        simulateQ (erase ∘ₛ implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
            ((RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)).run trace) := by
  have result := congrArg (fun program =>
    (simulateQ (handler candidate) program).run (state candidate trace))
    (RegistrationNativeSecretWordCheckedFrontendStep.query (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey inside candidate seed scalar query before)
  rw [← RegistrationNativeSecretWordCheckedTraceNative.program_source] at result
  simp only [simulateQ_map, StateT.run_map] at result
  have word := RegistrationNativeSecretWordCheckedTraceSource.word_program (n := n) (KemSK := KemSK)
    setup.source inside candidate (input setup.joint setup.dh seed scalar)
    ((RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before) trace
  change _ = (simulateQ (handler candidate)
    (simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before))).run (state candidate trace) at word
  rw [← word] at result
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using result

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTypedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTypedTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTypedTrace.query
