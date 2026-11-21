-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource
/-! The actual new stateful public frontend closes through the genuine open retained/KEM compiler to its same byte alias observation. Public P, the original ledger, current corrected callbacks and every optional failure are retained at each fixed challenge; no earlier whole frontend equation is used. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativePlatformSecretWordAliasClient (Result)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open PqxdhKemIndCca
open RegistrationNativePlatformSecretWordOrdinary (evaluate)
variable (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

abbrev Result (source : RegistrationNativeMldsa.Source) (A Platform : Type) :=
  (((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State)

omit primitive in
def observe (candidate : MlKemSharedSecret) (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform) : Result source A Platform :=
  Prod.map (Prod.map id (evaluate candidate)) (RegistrationNativeSecretWordCheckedTrace.state candidate) result.1

noncomputable def openProgram : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source A Platform) :=
  RegistrationNativeOpenKey.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside target)
    (RegistrationNativeOpenRetained.client setup canonical route sign
      (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work
          (evaluate RegistrationNativeSecretWordMessage.zero before)))) ordinary)

omit primitive in
private theorem reference_values {A P : Type}
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P) (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

/-- Each fixed early challenge has the exact actual corrected public callback result, ledger, P and native chronology of its same byte-view alias client. -/
theorem fixed_source (empty : before.1.server.sessions = []) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (openProgram setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer route seed scalar target serverKeyId bounds mode work before ordinary)).run'
      ((PqxdhLiveKemBirth.empty, none), ∅) =
      observe source candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
        (RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) (RegistrationNativeSecretWordProtection.inside target)
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
          serverKeyId bounds mode work before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅ := by
  have actual := congrArg (fun tree => (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl tree).run' ∅)
    (RegistrationNativePlatformG3CheckedActual.client_source setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before
      ordinary (RegistrationNativeSecretWordKemPool.empty, none) target selected pairs publicKey challenge empty)
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at actual
  have bytes := RegistrationNativePlatformSecretWordAliasSource.bytes_source setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary
    (RegistrationNativeSecretWordKemPool.empty, none) target selected pairs publicKey challenge empty
  change _ = _ <$> (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativePlatformG3CheckedActual.nativeRun setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary
      (RegistrationNativeSecretWordKemPool.empty, none) target selected pairs publicKey challenge)).run ∅ at actual
  change (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativePlatformG3CheckedActual.nativeRun setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary
      (RegistrationNativeSecretWordKemPool.empty, none) target selected pairs publicKey challenge)).run' ∅ = _ at bytes
  rw [StateT.run'_eq] at bytes
  have projected := congrArg (Functor.map Prod.fst) bytes
  simp only [Functor.map_map] at projected
  rw [projected] at actual
  have cold : evaluate candidate before = evaluate RegistrationNativeSecretWordMessage.zero before := by
    exact congrArg (fun front => (front, before.2)) (RegistrationNativeG3NativeCheckedUniformSource.cold_eval before.1 empty candidate)
  simp only [RegistrationNativePlatformG3CheckedActual.client, RegistrationNativePlatformG3OpenClosure.client, cold] at actual
  rw [RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
  simpa only [openProgram, observe, RegistrationNativePlatformSecretWordAliasSource.observation, Prod.map_def, id_eq, Function.comp_def, StateT.run'_eq, RegistrationNativeSecretWordKemProvider.evalState,
    RegistrationNativeSecretWordKemPool.eval_empty, Option.map_none, simulateQ_map, StateT.run_map, Functor.map_map] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource.fixed_source
