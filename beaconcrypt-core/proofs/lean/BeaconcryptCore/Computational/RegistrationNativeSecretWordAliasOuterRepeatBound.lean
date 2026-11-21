-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuter

/-! The complete candidate-independent prior is included inside one actual alias/recovery client. Same-run literal exposure and original lifecycle facts lift through its exact coin prefix. The byte repeat bound consequently uses twice one explicit suffix-key recovery advantage for this whole outer client, with both numerical allowances still supplied by original Respects. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhKemIndCca
open RegistrationNativeSecretWordAliasOuter (Profile inner client)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
private theorem symbolic_logged {Result : Type}
    (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (client : OracleComp Combined Result) :
    RegistrationNativeSecretWordRecoveryBound.symbolicView keySource (fun candidate result => (candidate, result.1)) client =
      (fun pair => (pair.1, pair.2.1)) <$> (do
        let candidate ← $ᵗ Secret
        let result ← RegistrationNativeSecretWordRecoveryBound.logged keySource candidate client
        pure (candidate, result)) := by
  simp only [RegistrationNativeSecretWordRecoveryBound.symbolicView, map_bind, map_pure]
  apply bind_congr
  intro candidate
  have source := RawCtxSelectedQueryTrace.complete
    (RegistrationNativeSecretWordRecoveryCompiler.closed keySource candidate)
    RegistrationNativeSecretWordRecoveryCompiler.literals client (∅, [])
  have mapped := congrArg (fun work => (fun result => (candidate, result.1)) <$> work) source
  simpa only [RegistrationNativeSecretWordRecoveryBound.logged, Functor.map_map, Prod.map_def,
    id_eq, bind_pure_comp] using mapped.symm

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
  (kem : RegistrationNativeSecretWordKemProvider.State KemSK) (prior : ProbComp (Profile KemSK))

local notation "interpret" => input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "actual" => client setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
  bounds mode work front ordinary kem prior

/-- The same actual logged outer result derives its protected literal hit from the original complete lifecycle and service log. -/
theorem logged_hit (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0)
    (owners : front.beacons = []) (keys : kem.1.keys = []) (candidate : Secret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value ×
      (RegistrationNativeSecretWord.Cache × List Secret))
    (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual))
    (repeated : RegistrationNativeG2Trace.RepeatedRoleAttempt
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate)
      (result.1.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))) : candidate ∈ result.2.2 := by
  rw [RegistrationNativeSecretWordAliasOuter.logged_source] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨profile, _sampled, possible⟩ := supported
  have exposed := RegistrationNativeSecretWordAliasRepeatBound.logged_literal setup checks wire source route sign seed scalar
    selected profile.pairs profile.publicKey profile.challenge selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem
    sessions parsed owners keys candidate result possible repeated
  obtain ⟨role, message, key, member, realized, protectedInput, literal⟩ := exposed
  exact RegistrationNativeSecretWordAliasServiceClient.install_logged setup checks wire source route sign interpret inside
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected profile.pairs profile.publicKey profile.challenge)
    selected selectedAccept publicPrekey serverKeyId bounds mode work front sessions ordinary kem candidate result possible
    role message key member realized protectedInput literal

/-- All actual outer literal hits are bounded by one concrete recovery adversary whose code samples the complete prior itself. -/
theorem literal_hit_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[pair.1 ∈ pair.2.2.2] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have sourceEq (candidate : Secret) :
      simulateQ (RegistrationNativeSuffixKeyPrf.realImpl setup.source candidate)
        (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) =
      (fun result => result.2.2) <$> RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual := by
    simp only [RegistrationNativeSecretWordRecoveryCompiler.guesses, RegistrationNativeSecretWordRecoveryCompiler.run,
      simulateQ_map, RegistrationNativeSecretWordRecoveryCompiler.program_source,
      RegistrationNativeSecretWordRecoveryBound.logged]
  have boundedKey := RegistrationNativeSuffixKeyRecovery.key_recovery_bound setup.source
    (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) (budget.cap 4 + budget.cap 5) (budget.cap 4 + budget.cap 5)
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_bound actual _
      (RegistrationNativeSecretWordAliasOuter.client_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
        bounds mode work front ordinary kem prior budget bounded .suffix))
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_length actual _
      (RegistrationNativeSecretWordAliasOuter.client_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
        bounds mode work front ordinary kem prior budget bounded .key))
  simpa only [RegistrationNativeSuffixKeyRecovery.guessed, sourceEq, map_bind,
    bind_pure_comp, Functor.map_map, decide_eq_true_eq, Nat.cast_add] using boundedKey

/-- The complete logged outer repeat event has the one explicit whole-prior recovery bound. -/
theorem logged_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0)
    (owners : front.beacons = []) (keys : kem.1.keys = []) :
    Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[
        RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSelectiveHiddenService.selected
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) pair.1)
          (pair.2.1.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event pair.1))] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  refine le_trans ?_ (literal_hit_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
    bounds mode work front ordinary kem prior budget bounded)
  apply prEvent_mono_of_support
  intro pair supported repeated
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨candidate, _draw, result, possible, rfl⟩ := supported
  exact logged_hit setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
    bounds mode work front ordinary kem prior sessions parsed owners keys candidate result possible repeated
/-- Repetition in the actual byte-table view is bounded conservatively by the same literal-recovery loss twice: once for its real-table source comparison and once for the same-run repetition event. -/
theorem bytes_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0)
    (owners : front.beacons = []) (keys : kem.1.keys = []) :
    Pr{let pair ← (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
      (fun candidate result => (candidate, result.1)) actual)}[
        RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSelectiveHiddenService.selected
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) pair.1)
          (pair.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event pair.1))] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  let observe := fun (candidate : Secret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value × RegistrationNativeSecretWordSource.ByteCache) =>
      (candidate, result.1)
  let event := fun (pair : Secret × RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) =>
    RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) pair.1)
      (pair.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event pair.1))
  have symbolicBound :
      Pr{let pair ← RegistrationNativeSecretWordRecoveryBound.symbolicView setup.source observe actual}[event pair] ≤
        ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
          (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
          (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
          (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
    rw [show observe = (fun candidate result => (candidate, result.1)) from rfl, symbolic_logged, prEvent_map]
    exact logged_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
      bounds mode work front ordinary kem prior budget bounded sessions parsed owners keys
  have compared := prEvent_le_prEvent_add_ofReal_discreteDistance
    (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe actual)
    (RegistrationNativeSecretWordRecoveryBound.symbolicView setup.source observe actual) event
  rw [discreteDistance_comm] at compared
  have close := RegistrationNativeSecretWordRecoveryBound.observed_close setup.source observe actual
    (budget.cap 4 + budget.cap 5) (budget.cap 4 + budget.cap 5)
    (RegistrationNativeSecretWordAliasOuter.client_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
      bounds mode work front ordinary kem prior budget bounded .suffix)
    (RegistrationNativeSecretWordAliasOuter.client_bound setup checks wire source route sign seed scalar selected selectedAccept publicPrekey serverKeyId
      bounds mode work front ordinary kem prior budget bounded .key)
  simp only [Nat.cast_add] at close
  simpa only [two_mul] using compared.trans (add_le_add symbolicBound close)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.logged_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.logged_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.literal_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.literal_hit_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.logged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.logged_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound.bytes_bound
