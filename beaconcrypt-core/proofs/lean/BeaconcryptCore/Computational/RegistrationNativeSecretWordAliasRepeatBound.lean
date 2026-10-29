-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat

/-! The same complete real-side-information alias execution bounds native selected-input repetition by its actual protected literal exposure. Full-support sampling is used only to recover an existing operational support certificate from an arbitrary stateful interpretation, not to change the probability experiment. The quantitative bound is the original concrete suffix-key recovery bound. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

local instance : ∀ query : Combined.Domain, SampleableType (Combined.Range query) := by
  intro query
  rcases query with (coin | key) | head <;> infer_instance

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
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
  (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

local notation "interpret" => input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "actual" => RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign interpret inside
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
  selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem

/-- The actual logged stateful client derives the original one-use lifecycle and literal exposure certificate on the very same complete result. -/
theorem logged_literal (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0)
    (owners : front.beacons = []) (keys : kem.1.keys = []) (candidate : Secret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value ×
      (RegistrationNativeSecretWord.Cache × List Secret))
    (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual))
    (repeated : RegistrationNativeG2Trace.RepeatedRoleAttempt
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate)
      (result.1.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))) :
    RegistrationNativeSecretWordAliasExposureBound.Exposure interpret inside candidate result.1.1.2 := by
  have reached : result.1 ∈ support actual := by
    apply OracleComp.support_simulateQ_run'_subset
      (RawCtxSelectedQueryTrace.recorded (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
        RegistrationNativeSecretWordRecoveryCompiler.literals) actual (∅, [])
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have uniformReached : result.1 ∈ support (simulateQ (uniformSampleImpl (spec := Combined)) actual) := by
    rw [uniformSampleImpl.support_simulateQ]
    exact reached
  exact RegistrationNativeSecretWordAliasRepeat.repeated_literal setup checks wire source route sign seed scalar selected pairs publicKey challenge
    uniformSampleImpl selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem sessions parsed owners keys
    result.1 uniformReached candidate repeated

/-- Native selected-role repetition in the complete logged client is bounded by its concrete original suffix-key recovery adversary and original build-plus-finish allowances. -/
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
  have included :
      Pr{let pair ← (do
        let candidate ← $ᵗ Secret
        let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
        pure (candidate, result))}[
          RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
            (RegistrationNativeSelectiveHiddenService.selected
              (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) pair.1)
            (pair.2.1.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event pair.1))] ≤
      Pr{let pair ← (do
        let candidate ← $ᵗ Secret
        let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
        pure (candidate, result))}[
          RegistrationNativeSecretWordAliasExposureBound.Exposure interpret inside pair.1 pair.2.1.1.2] := by
    apply prEvent_mono_of_support
    intro pair supported repeated
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨candidate, _draw, result, possible, rfl⟩ := supported
    exact logged_literal setup checks wire source route sign seed scalar selected pairs publicKey challenge selectedAccept publicPrekey serverKeyId
      bounds mode work front ordinary kem sessions parsed owners keys candidate result possible repeated
  exact included.trans (RegistrationNativeSecretWordAliasExposureBound.bound setup checks wire source route sign interpret inside
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    selected selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front sessions ordinary kem)

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
    exact logged_bound setup checks wire source route sign seed scalar selected pairs publicKey challenge selectedAccept publicPrekey serverKeyId
      bounds mode work front ordinary kem budget bounded sessions parsed owners keys
  have compared := prEvent_le_prEvent_add_ofReal_discreteDistance
    (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source observe actual)
    (RegistrationNativeSecretWordRecoveryBound.symbolicView setup.source observe actual) event
  rw [discreteDistance_comm] at compared
  have close := RegistrationNativeSecretWordAliasClient.observed_close setup checks wire source route sign interpret inside
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    selected selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front ordinary kem observe
  simpa only [two_mul] using compared.trans (add_le_add symbolicBound close)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.logged_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.logged_literal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.logged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.logged_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeatBound.bytes_bound
