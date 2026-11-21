-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView
/-! The complete corrected accept kernel uses the same shared platform reservation and exact routed checked dictionary. The symbolic reference table is evaluated only by the private comparison; the executable Word controller receives no candidate bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState input)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordFrontendView (nativeBase wordBase native_hom word_hom target wordLocal native_local word_local)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}

/-- The actual OPEN kernel, including repeated pin and mutable reservation, has the same complete checked global execution as its Word counterpart. -/
theorem kernel (setup : Setup base KemSK) (checks : Checks)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment) :
    nativeBase setup.source inside candidate (input setup.joint setup.dh seed scalar)
      (((RegistrationNativePlatformServerOpenControl.accept
        (RegistrationNativePlatformPublicFrontend.localHandler (n := n) (KemSK := KemSK) selected)
        (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        wordBase setup.source inside candidate (input setup.joint setup.dh seed scalar)
          (((RegistrationNativePlatformSecretWordOpen.accept (wordLocal selected)
            (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet).run before).run env) := by
  have nativeMap := RegistrationNativePlatformSecretWordOpenMap.native_accept
    (hom := native_hom setup.source inside candidate (input setup.joint setup.dh seed scalar))
    (nativeImplementation := RegistrationNativePlatformPublicFrontend.localHandler (n := n) (KemSK := KemSK) selected)
    (reserve := RegistrationNativePlatformPublicFrontend.platform reserve) (setup := setup) (checks := checks)
    (verify := verify) (packet := packet) (before := before.eval candidate) (env := env)
  have wordMap := RegistrationNativePlatformSecretWordOpenMap.accept
    (hom := word_hom setup.source inside candidate (input setup.joint setup.dh seed scalar))
    (implementation := wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
    (reserve := RegistrationNativePlatformSecretWordOrdinary.platform reserve) (setup := setup) (checks := checks)
    (verify := verify) (packet := packet) (before := before) (env := env)
  simp only [native_local, RegistrationNativePlatformSecretWordFrontendView.platform] at nativeMap
  simp only [word_local] at wordMap
  have sourceEq := RegistrationNativePlatformSecretWordOpen.accept_source setup checks inside candidate seed scalar
    (target (n := n) (KemSK := KemSK) (Platform := Platform) selected)
    (wordBase setup.source inside candidate (input setup.joint setup.dh seed scalar)
      (RegistrationNativePlatformSecretWordOrdinary.platform reserve)) verify packet before env
  rw [← wordMap] at sourceEq
  exact nativeMap.trans sourceEq

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptSource.kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptSource.kernel
