-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram

/-! The complete original raw secrecy ledger and its actual native G2 trace have the evaluated symbolic frontend source. This theorem consumes the concrete audited per-command source and both chronological observer equations. It retains the full final frontend, original ledger and all prepare/demand/encapsulation/install events; no whole-program or trace correspondence is supplied by the caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State input)
open RegistrationNativeSecretWordCheckedFrontend (erase native implementation)
open RegistrationNativeSecretWordCheckedTrace (handler state)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The actual complete native secrecy run and native chronological G2 trace are precisely the evaluated symbolic run and symbolic trace under the concrete checked source. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    simulateQ (erase ∘ₛ native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
          serverKeyId bounds mode work (before.eval candidate))) =
      Prod.map (Prod.map id (State.eval candidate)) (state candidate) <$>
        simulateQ (erase ∘ₛ implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (RegistrationNativeSecretWordFrontendTrace.program
            (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
              serverKeyId bounds mode work before)) := by
  have result := congrArg (fun program =>
    (simulateQ (handler candidate) program).run RegistrationNativeG2Trace.initial)
    (RegistrationNativeSecretWordCheckedFrontendProgram.run (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode inside candidate seed scalar work before)
  rw [← RegistrationNativeSecretWordCheckedTraceNative.program_source] at result
  simp only [simulateQ_map, StateT.run_map] at result
  have word := RegistrationNativeSecretWordCheckedTraceSource.word_program (n := n) (KemSK := KemSK)
    setup.source inside candidate (input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
      serverKeyId bounds mode work before) RegistrationNativeSecretWordFrontendTrace.initial
  change _ = (simulateQ (handler candidate)
    (simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before))).run RegistrationNativeG2Trace.initial at word
  rw [← word] at result
  simpa only [RegistrationNativeG2Trace.program, RegistrationNativeSecretWordFrontendTrace.program,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using result

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceRun.run
