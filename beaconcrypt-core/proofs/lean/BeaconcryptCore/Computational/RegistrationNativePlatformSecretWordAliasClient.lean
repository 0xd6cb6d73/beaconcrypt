-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound
/-! One candidate-independent recovery client runs the actual corrected Word frontend, its chronological observer and the concrete combined Word/ordinary/KEM interpreter. All new source allocation and serializer outcomes and the same persistent platform state are retained. The inherited ordinary interpreter's named accounting projection is explicit; this component is not a whole native-World equality or the final repeated-role bound. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

abbrev Result (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK A Platform : Type) :=
  ((((A × RegistrationNativeLedger.State) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) ×
    RegistrationNativeSecretWordFrontendTrace.State) × RegistrationNativeSecretWordInterpreter.State n KemSK)

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

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

noncomputable def client : OracleComp Combined (Result source n KemSK A Platform) :=
  RegistrationNativeSecretWordInterpreter.execute setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    route sign input inside provider
    (RegistrationNativeSecretWordFrontendTrace.program
      (RegistrationNativePlatformSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))
    (RegistrationNativeSecretWordInterpreter.initial ordinary kem)

/-- Both recovery-oracle bills follow from the literal corrected raw source budget, with the full trace and persistent platform state retained. -/
theorem client_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (kind : Kind) :
    (client setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem).IsQueryBoundP
      (Counted kind) (budget.cap 4 + budget.cap 5) := by
  apply RegistrationNativeSecretWordInterpreterCaps.program_bound setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    route sign input inside provider _ _ _ _ kind
  apply RegistrationNativeSecretWordFrontendTrace.program_bound
  exact (RegistrationNativePlatformSecretWordFrontendCaps.run_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded before).of_imp
    (fun _ counted => counted)

/-- A single explicit suffix-key adversary compares the complete actual corrected symbolic client and its byte-table realization. -/
theorem observed_close (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (observe : RegistrationNativeSuffixKeyPrf.Secret →
      (Result source n KemSK A Platform × RegistrationNativeSecretWordSource.ByteCache) → Observation) :
    let actual := client setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem
    ENNReal.ofReal (discreteDistance
      (RegistrationNativeSecretWordRecoveryBound.symbolicView setup.source observe actual)
      (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe actual)) ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordRecoveryBound.observed_close setup.source observe _ _ _
    (client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem budget bounded .suffix)
    (client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem budget bounded .key)

/-- All literal hits in this same complete candidate-independent client are charged to that client's one explicit recovery advantage. -/
theorem literal_hit_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    let actual := client setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem
    Pr{let pair ← (do
      let candidate ← $ᵗ RegistrationNativeSuffixKeyPrf.Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[pair.1 ∈ pair.2.2.2] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordAliasPriorBound.literal_hit_bound setup.source _ (budget.cap 4 + budget.cap 5)
    (client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem budget bounded .suffix)
    (client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem budget bounded .key)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.client_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.observed_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.observed_close

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.literal_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient.literal_hit_bound
