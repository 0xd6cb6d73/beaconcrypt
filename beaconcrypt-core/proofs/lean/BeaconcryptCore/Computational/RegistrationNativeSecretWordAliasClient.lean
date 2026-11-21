-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource

/-! The ordinary suffix-key recovery experiment now uses the actual complete symbolic frontend and chronological observer. Both oracle bills follow from the original native build-plus-finish budget. The executing client receives no mathematical candidate; its final observer may inspect the candidate, full original ledger, entire frontend/private state, chronological events and actual byte cache. This endpoint does not itself assert the native G2 source correspondence or the absence of repeated atom-role attempts. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {ι KemSK Value Observation : Type} {base : OracleSpec ι}

abbrev Result (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK Value : Type) :=
  ((((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
    RegistrationNativeSecretWordFrontendTrace.State) × RegistrationNativeSecretWordInterpreter.State n KemSK)

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    OracleComp Combined (Result source n KemSK Value) :=
  RegistrationNativeSecretWordInterpreter.execute setup wire route sign input inside provider
    (RegistrationNativeSecretWordFrontendTrace.program
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before))
    (RegistrationNativeSecretWordInterpreter.initial ordinary kem)

/-- The actual full-ledger alias client inherits each recovery-oracle allowance from the original native budget, including its entire trace layer. -/
theorem client_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeSecretWordMessage.State source)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (kind : Kind) :
    (client setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work before ordinary kem).IsQueryBoundP (Counted kind) (budget.cap 4 + budget.cap 5) := by
  apply RegistrationNativeSecretWordInterpreterCaps.program_bound setup wire route sign input inside provider _ _ _ _ kind
  apply RegistrationNativeSecretWordFrontendTrace.program_bound
  exact RegistrationNativeSecretWordFrontendCaps.run_bound setup checks wire source sign selectedOwner selectedAccept
    publicPrekey serverKeyId bounds mode work budget bounded before

/-- One explicit ordinary suffix-key adversary bounds the concrete complete native alias client, with both numerical allowances derived from original Respects. -/
theorem observed_close (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeSecretWordMessage.State source)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (observe : RegistrationNativeSuffixKeyPrf.Secret →
      (Result source n KemSK Value × RegistrationNativeSecretWordSource.ByteCache) → Observation) :
    let actual := client setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
      serverKeyId bounds mode work before ordinary kem
    ENNReal.ofReal (discreteDistance
      (RegistrationNativeSecretWordRecoveryBound.symbolicView setup.source observe actual)
      (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe actual)) ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordRecoveryBound.observed_close setup.source observe _ _ _
    (client_bound setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work budget bounded before ordinary kem .suffix)
    (client_bound setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work budget bounded before ordinary kem .key)

/-- All candidate-equal literal queries in the same complete real-side-information execution are bounded by its concrete recovery adversary; the literal list is never assumed independent of the candidate. -/
theorem literal_hit_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeSecretWordMessage.State source)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    let actual := client setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
      serverKeyId bounds mode work before ordinary kem
    Pr{let pair ← (do
      let candidate ← $ᵗ RegistrationNativeSuffixKeyPrf.Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[pair.1 ∈ pair.2.2.2] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  let actual := client setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
    serverKeyId bounds mode work before ordinary kem
  have sourceEq (candidate : RegistrationNativeSuffixKeyPrf.Secret) :
      simulateQ (RegistrationNativeSuffixKeyPrf.realImpl setup.source candidate)
        (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) =
      (fun result => result.2.2) <$> RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual := by
    simp only [RegistrationNativeSecretWordRecoveryCompiler.guesses, RegistrationNativeSecretWordRecoveryCompiler.run,
      simulateQ_map, RegistrationNativeSecretWordRecoveryCompiler.program_source,
      RegistrationNativeSecretWordRecoveryBound.logged]
  have boundedKey := RegistrationNativeSuffixKeyRecovery.key_recovery_bound setup.source
    (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) (budget.cap 4 + budget.cap 5) (budget.cap 4 + budget.cap 5)
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_bound actual _
      (client_bound setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode work budget bounded before ordinary kem .suffix))
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_length actual _
      (client_bound setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode work budget bounded before ordinary kem .key))
  simpa only [RegistrationNativeSuffixKeyRecovery.guessed, sourceEq, map_bind,
    bind_pure_comp, Functor.map_map, decide_eq_true_eq, Nat.cast_add] using boundedKey

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.observed_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.observed_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.literal_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient.literal_hit_bound
