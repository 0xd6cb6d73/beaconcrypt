-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry

/-! The concrete original frontend Server entry retains its owner roster and parsed-accept counter while the same-provider native SDK executes authentication and agreement. This is an operational source equation; only the explicitly displayed private root memo is erased from its observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute localImpl)
open RegistrationNativeProviderAcceptRun (State close)
open RegistrationNativeProviderAcceptAgreement (project nativeProject restore)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def unpack (before : FrontState n KemSK ProviderState source) : State n KemSK ProviderState :=
  (before.1.server, before.1.environment, before.2)

def pack (before : FrontState n KemSK ProviderState source) (after : State n KemSK ProviderState) :
    FrontState n KemSK ProviderState source :=
  ({ before.1 with server := after.1, environment := after.2.1 }, after.2.2)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- The original frontend Server wrapper closes the exact local controller under the selected route, with no KEM interpretation replacement. -/
theorem serverOpen_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : FrontState n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.serverOpen selected work)).run before =
      Prod.map id (pack before) <$>
        (close (localImpl setup wire route sign seed scalar provider selected) work).run (unpack before) := by
  have localExecution := RegistrationNativeProviderSource.local_program setup wire route sign seed scalar provider selected
    ((work.run before.1.server).run before.1.environment) before.2
  have mapped := congrArg (fun distribution =>
    (fun result => (result.1.1.1,
      ({ before.1 with server := result.1.1.2, environment := result.1.2 }, result.2))) <$> distribution) localExecution
  simpa only [execute, RegistrationNativePublicFrontend.serverOpen, RegistrationNativeProviderSource.close,
    RegistrationNativeProviderAcceptRun.close, RegistrationNativeProviderLocal.lower, StateT.run,
    state_map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, unpack, pack] using mapped

/-- Whole frontend acceptance preserves the untouched public owner roster and ordinal, and derives the literal native SDK result under the same total provider. -/
theorem accept_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (verify : MldsaTranscriptAuth.Verify)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (packet : registration.InitPacket) (memo : RegistrationNativeReferenceInterpreter.State)
    (before : FrontState n KemSK ProviderState source) :
    (fun result => (result.1,
      (result.2.1.beacons, result.2.1.parsedAccepts,
        project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) memo
          (unpack result.2)))) <$>
      (execute setup wire route sign seed scalar provider
        (RegistrationNativePublicFrontend.serverOpen selected
          (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet))).run before =
      (fun result => (result.1,
        (before.1.beacons, before.1.parsedAccepts, nativeProject memo result.2))) <$>
        (RegistrationNativeProviderAcceptSdk.accept setup checks wire route sign seed scalar provider selected verify packet).run
          (restore (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) (unpack before)) := by
  rw [serverOpen_run]
  simp only [Functor.map_map, Prod.map_def, id_eq, pack, unpack]
  have actual := RegistrationNativeProviderAcceptEntry.accept_native setup checks wire route sign seed scalar provider selected verify
    correct packet memo (unpack before)
  have framed := congrArg (fun distribution => (fun result =>
    (result.1, (before.1.beacons, before.1.parsedAccepts, result.2))) <$> distribution) actual
  simpa only [Functor.map_map, Prod.map_def, id_eq, unpack] using framed

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend.serverOpen_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend.serverOpen_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend.accept_source
