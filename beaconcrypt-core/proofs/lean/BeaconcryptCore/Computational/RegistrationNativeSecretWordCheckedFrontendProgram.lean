-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendStep

/-! The concrete per-command source equations compose through arbitrary adaptive typed work and the literal original secrecy compiler. The equality retains the complete frontend state, original raw ledger and internal chronological audit callbacks. It assumes no full-program source relation or preservation condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State input)
open RegistrationNativeSecretWordCheckedFrontend (native implementation)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The complete actual adaptive typed frontend has the exact symbolic checked source, including every failed poststate and audit. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((simulateQ (RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, QueryImpl.simulateQ_mapStateTBase_run]
  apply (map_run_simulateQ_eq_of_query_map_eq _ _ (State.eval candidate) ?_ work before).symm
  intro query current
  simpa only [QueryImpl.mapStateTBase, StateT.run_mk] using
    (RegistrationNativeSecretWordCheckedFrontendStep.query setup checks wire source sign selectedOwner selectedAccept publicPrekey
      inside candidate seed scalar query current).symm

/-- The exact original raw secrecy ledger runs above the complete symbolic frontend without changing any original designation or record event. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
            serverKeyId bounds mode work before) :=
  program setup checks wire source sign selectedOwner selectedAccept publicPrekey inside candidate seed scalar _ before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendProgram.run
