-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild

/-! Actual whole-frontend Server components consume the finite checked authentication and one-use build source laws through the proven routed query embeddings. No component equality or secure callback is assumed by these endpoints. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State input)
open RegistrationNativeSecretWordCheckedFrontend (native implementation)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept
  RegistrationNativeSecretWordServerCompiler.accept RegistrationServerOpenReferenceCompiler.build
  RegistrationNativeSecretWordServerCompiler.build native implementation

/-- Actual mandatory Server accept retains its complete whole-frontend state through the same selected routed KEM provider. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : registration.InitPacket) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.serverOpen selected
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.serverOpen selected
            (RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet)).run before) := by
  simp only [RegistrationNativePublicFrontend.serverOpen, RegistrationNativeSecretWordFrontend.serverOpen,
    StateT.run, simulateQ_map]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program,
    RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]
  simp only [State.eval]
  have localSource := RegistrationNativeSecretWordCheckedServerAccept.accept (n := n) setup checks verify inside candidate seed scalar packet before.server before.environment
  simp only [StateT.run] at localSource
  rw [localSource, simulateQ_map]
  simp only [Functor.map_map]
  rfl

/-- Actual raw Server build preserves its consumed handle, all publication failures and the whole current frontend state. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    {source : RegistrationNativeMldsa.Source}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (handle : Nat) (application : Option (Slice U8)) (before : State source) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (implementation (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.serverOpen false
            (RegistrationNativeSecretWordServerCompiler.build setup.source wire checks sign handle application)).run before) := by
  simp only [RegistrationNativePublicFrontend.serverOpen, RegistrationNativeSecretWordFrontend.serverOpen,
    StateT.run, simulateQ_map]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program,
    RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]
  simp only [State.eval]
  have localSource := RegistrationNativeSecretWordCheckedServerBuild.build (n := n) (KemSK := KemSK) setup.source inside candidate setup.joint setup.dh seed scalar
    setup.source wire checks sign handle application before.server before.environment
  simp only [StateT.run] at localSource
  rw [localSource, simulateQ_map]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendServer.build
