-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure

/-! The actual full native G2 chronology closes into the concrete combined symbolic alias client under its real suffix-key interpretation. This composition retains the original ledger, evaluated frontend, every chronological event, ordinary World and complete opaque KEM provider state. Only preparation flags are dropped, after the actual initialized frontend has derived their safety internally. The separate provider-to-native KEM game transport is not assumed here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordInterpreter (Provider initial)
open RegistrationNativeSecretWordCheckedClosure (plain drop)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The complete native chronological source is the actual flag-enforcing combined alias execution with only private flags erased, not a caller-supplied checked or trace correspondence. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (empty : before.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    (simulateQ (plain setup wire route sign (input setup.joint setup.dh seed scalar) inside provider candidate)
      (simulateQ (RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
        RegistrationNativeSecretWordCheckedFrontend.native setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (RegistrationNativeG2Trace.program
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
            bounds mode work (before.eval candidate))))).run (drop (initial ordinary kem)) =
      simulateQ (RegistrationNativeSecretWordServiceSource.realize setup.source candidate)
        (Prod.map
          (Prod.map (Prod.map id (RegistrationNativeSecretWordMessage.State.eval candidate))
            (RegistrationNativeSecretWordCheckedTrace.state candidate)) drop <$>
          RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign
            (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey serverKeyId
            bounds mode work before ordinary kem) := by
  have traced := RegistrationNativeSecretWordCheckedTraceRun.run (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode inside candidate seed scalar work before
  have lifted := congrArg (fun program =>
    (simulateQ (plain setup wire route sign (input setup.joint setup.dh seed scalar) inside provider candidate) program).run
      (drop (initial ordinary kem))) traced
  simp only [simulateQ_map, StateT.run_map] at lifted
  rw [← RegistrationNativeSecretWordCheckedClosure.program] at lifted
  rw [RegistrationNativeSecretWordLiveFrontendSource.traced_source setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode work before empty ordinary kem] at lifted
  simpa only [RegistrationNativeSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute,
    simulateQ_map, Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using lifted

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasSource.run_source
