-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPrior

/-! One actual alias client includes an arbitrary actual probability prefix and all following frontend work. A same-run literal-hit certificate and original query bills give one explicit recovery advantage for that whole client; the conservative byte comparison pays this loss twice. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {Result : Type}
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


/-- All literal hits for one complete actual client are charged to its own explicit recovery adversary. -/
theorem literal_hit_bound (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (actual : OracleComp Combined Result) (q : Nat)
    (suffixes : actual.IsQueryBoundP (Counted .suffix) q)
    (keys : actual.IsQueryBoundP (Counted .key) q) :
    Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged keySource candidate actual
      pure (candidate, result))}[pair.1 ∈ pair.2.2.2] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage keySource
        (RegistrationNativeSuffixKeyRecovery.adversary keySource
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      q * (256 ^ 160 : ℝ≥0∞)⁻¹ + q * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have sourceEq (candidate : Secret) :
      simulateQ (RegistrationNativeSuffixKeyPrf.realImpl keySource candidate)
        (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) =
      (fun result => result.2.2) <$> RegistrationNativeSecretWordRecoveryBound.logged keySource candidate actual := by
    simp only [RegistrationNativeSecretWordRecoveryCompiler.guesses, RegistrationNativeSecretWordRecoveryCompiler.run,
      simulateQ_map, RegistrationNativeSecretWordRecoveryCompiler.program_source,
      RegistrationNativeSecretWordRecoveryBound.logged]
  have boundedKey := RegistrationNativeSuffixKeyRecovery.key_recovery_bound keySource
    (RegistrationNativeSecretWordRecoveryCompiler.guesses actual) q q
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_bound actual _ suffixes)
    (RegistrationNativeSecretWordRecoveryCompiler.guesses_length actual _ keys)
  simpa only [RegistrationNativeSuffixKeyRecovery.guessed, sourceEq, map_bind,
    bind_pure_comp, Functor.map_map, decide_eq_true_eq] using boundedKey

/-- A same-run event-to-literal implication gives one recovery loss in the complete logged execution. -/
theorem logged_bound (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (actual : OracleComp Combined Result) (q : Nat)
    (suffixes : actual.IsQueryBoundP (Counted .suffix) q)
    (keys : actual.IsQueryBoundP (Counted .key) q)
    (event : Secret → Result → Prop)
    (hit : ∀ candidate result, result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged keySource candidate actual) →
      event candidate result.1 → candidate ∈ result.2.2) :
    Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged keySource candidate actual
      pure (candidate, result))}[event pair.1 pair.2.1] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage keySource
        (RegistrationNativeSuffixKeyRecovery.adversary keySource (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      q * (256 ^ 160 : ℝ≥0∞)⁻¹ + q * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  refine le_trans ?_ (literal_hit_bound keySource actual q suffixes keys)
  apply prEvent_mono_of_support
  intro pair supported repeated
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨candidate, _draw, result, possible, rfl⟩ := supported
  exact hit candidate result possible repeated

/-- The same one complete recovery adversary bounds the byte observation with the conservative factor two. -/
theorem bytes_bound (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (actual : OracleComp Combined Result) (q : Nat)
    (suffixes : actual.IsQueryBoundP (Counted .suffix) q)
    (keys : actual.IsQueryBoundP (Counted .key) q)
    (event : Secret → Result → Prop)
    (hit : ∀ candidate result, result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged keySource candidate actual) →
      event candidate result.1 → candidate ∈ result.2.2) :
    Pr{let pair ← (RegistrationNativeSecretWordRecoveryBound.bytesView keySource
      (fun candidate result => (candidate, result.1)) actual)}[event pair.1 pair.2] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage keySource
        (RegistrationNativeSuffixKeyRecovery.adversary keySource (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      q * (256 ^ 160 : ℝ≥0∞)⁻¹ + q * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  let observe := fun (candidate : Secret) (result : Result × RegistrationNativeSecretWordSource.ByteCache) => (candidate, result.1)
  let selected := fun pair : Secret × Result => event pair.1 pair.2
  have symbolicBound :
      Pr{let pair ← RegistrationNativeSecretWordRecoveryBound.symbolicView keySource observe actual}[selected pair] ≤
        ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage keySource
          (RegistrationNativeSuffixKeyRecovery.adversary keySource (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
          q * (256 ^ 160 : ℝ≥0∞)⁻¹ + q * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
    rw [show observe = (fun candidate result => (candidate, result.1)) from rfl, symbolic_logged, prEvent_map]
    exact logged_bound keySource actual q suffixes keys event hit
  have compared := prEvent_le_prEvent_add_ofReal_discreteDistance
    (RegistrationNativeSecretWordRecoveryBound.bytesView keySource observe actual)
    (RegistrationNativeSecretWordRecoveryBound.symbolicView keySource observe actual) selected
  rw [discreteDistance_comm] at compared
  have close := RegistrationNativeSecretWordRecoveryBound.observed_close keySource observe actual q q suffixes keys
  simpa only [two_mul] using compared.trans (add_le_add symbolicBound close)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.literal_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.literal_hit_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.logged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.logged_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound.bytes_bound
