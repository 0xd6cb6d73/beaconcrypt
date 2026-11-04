-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource
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

variable (route : RawCtxServerRouting.SenderDecoder) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
open RegistrationNativeSecretWordCheckedFrontend (erase native implementation)
open RegistrationNativeSecretWordCheckedTrace (handler state)
open RegistrationNativePlatformSecretWordOrdinary (evaluate)
open RegistrationNativeSecretWordMessage (input)
local notation "word" => RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before
local notation "actual" => simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
  (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work (evaluate candidate before))

/-- The literal corrected public source and its original native trace equal the evaluated Word tree and its same chronology. -/
theorem traced :
    simulateQ (erase ∘ₛ native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (RegistrationNativeG2Trace.program actual) =
      Prod.map (Prod.map id (evaluate candidate)) (state candidate) <$>
        simulateQ (erase ∘ₛ implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (RegistrationNativeSecretWordFrontendTrace.program word) := by
  have result := congrArg (fun program => (simulateQ (handler (n := n) (KemSK := KemSK) candidate) program).run RegistrationNativeG2Trace.initial)
    (RegistrationNativePlatformSecretWordFrontendSource.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer inside candidate seed scalar serverKeyId bounds mode work before)
  rw [← RegistrationNativeSecretWordCheckedTraceNative.program_source] at result
  simp only [simulateQ_map, StateT.run_map] at result
  have wordSource := RegistrationNativeSecretWordCheckedTraceSource.word_program (n := n) (KemSK := KemSK) setup.source inside candidate
    (input setup.joint setup.dh seed scalar) word RegistrationNativeSecretWordFrontendTrace.initial
  change _ = (simulateQ (handler (n := n) (KemSK := KemSK) candidate) (simulateQ (implementation setup.source inside candidate
    (input setup.joint setup.dh seed scalar)) word)).run RegistrationNativeG2Trace.initial at wordSource
  rw [← wordSource] at result
  simpa only [RegistrationNativeG2Trace.program, RegistrationNativeSecretWordFrontendTrace.program,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using result

/-- The complete actual checked source closure erases only the internally derived preparation flags, retaining private World/provider state and public P. -/
theorem plain_source (empty : before.1.server.sessions = []) :
    (simulateQ (RegistrationNativeSecretWordCheckedClosure.plain setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign
      (input setup.joint setup.dh seed scalar) inside provider candidate)
      (simulateQ (erase ∘ₛ native setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (RegistrationNativeG2Trace.program actual))).run
          (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem)) =
      simulateQ (RegistrationNativeSecretWordServiceSource.realize setup.source candidate)
        (Prod.map
          (Prod.map (Prod.map id (evaluate candidate)) (state candidate)) RegistrationNativeSecretWordCheckedClosure.drop <$>
          RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign selectedOwner selectedAccept publicPrekey
            view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route (input setup.joint setup.dh seed scalar)
            inside provider serverKeyId bounds mode work before ordinary kem) := by
  have lifted := congrArg (fun program =>
    (simulateQ (RegistrationNativeSecretWordCheckedClosure.plain setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign
      (input setup.joint setup.dh seed scalar) inside provider candidate) program).run
      (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem)))
    (traced setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer inside candidate seed scalar serverKeyId bounds mode work before)
  simp only [simulateQ_map, StateT.run_map] at lifted
  rw [← RegistrationNativeSecretWordCheckedClosure.program] at lifted
  rw [RegistrationNativePlatformSecretWordLiveSource.traced_source setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode work before empty ordinary kem] at lifted
  simpa only [RegistrationNativePlatformSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute,
    simulateQ_map, Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using lifted


omit primitive in
def observation (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (result : Result source n KemSK A Platform) :=
  Prod.map (Prod.map (Prod.map id (evaluate candidate)) (state candidate))
    (RegistrationNativeSecretWordNativePlainProvider.embed candidate ∘ RegistrationNativeSecretWordCheckedClosure.drop) result

variable (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (publicKey : PqxdhKemIndCca.MlKem768PublicKey)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
local notation "early" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "protected" => RegistrationNativeSecretWordProtection.inside target
local notation "aliasClient" => RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route (input setup.joint setup.dh seed scalar)
  protected early serverKeyId bounds mode work before ordinary kem
local notation "nativeRun" => StateT.run (simulateQ (RegistrationNativeSecretWordNativePlain.native setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
  route sign seed scalar target (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
  (RegistrationNativeG2Trace.program actual))
    (RegistrationNativeSecretWordNativePlainProvider.embed candidate
      (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem)))

/-- The same literal corrected native tree realizes the actual early provider and the complete alias result, retaining the full private frame and platform state. -/
theorem native_source (empty : before.1.server.sessions = []) :
    nativeRun = simulateQ (RegistrationNativeSecretWordServiceSource.realize setup.source candidate)
      (observation source candidate <$> aliasClient) := by
  rw [← RegistrationNativeSecretWordNativePlainProvider.program_source, ← RegistrationNativeSecretWordNativePlain.program_source]
  rw [plain_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route protected early candidate seed scalar serverKeyId bounds mode work before ordinary kem empty]
  simp only [simulateQ_map, Functor.map_map]
  rfl

omit primitive in
private theorem bytes_handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ RegistrationNativeSecretWordServiceSource.realize source candidate =
      RegistrationNativeSecretWordRecoveryBound.bytes source candidate := by
  funext query before
  rcases query with (coin | key) | head
  all_goals simp only [QueryImpl.compose, RegistrationNativeSecretWordServiceSource.realize,
    simulateQ_spec_query, simulateQ_pure, RegistrationNativeSecretWordRecoveryBound.bytes,
    RegistrationNativeSecretWordSource.byteSource, PqxdhRegistrationJointKemSecondEntry.lazyImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
  all_goals rfl

/-- Closing the actual key table yields the exact byte-view alias observation at each fixed mathematical candidate; no native source or trace law is a premise. -/
theorem bytes_source (empty : before.1.server.sessions = []) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl nativeRun).run' ∅ =
      observation source candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate) aliasClient).run' ∅ := by
  rw [native_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge empty,
    ← QueryImpl.simulateQ_compose, bytes_handler]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.traced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.plain_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.plain_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.native_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource.bytes_source
