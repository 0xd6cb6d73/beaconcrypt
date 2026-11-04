-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity

/-! The same original native LR winning and eligibility observers traverse all-test provenance, the whole-client repeat audit and each billed record reduction separately. The provider remains an arbitrary actual provider here; the concrete early source supplies the selected-test receipts in LorRecordSecurity.full_hit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectedRecordTrace (outcomeSelected)
open RegistrationNativeLorRecordSecurity (observer recordObserver record_event)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
  (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
local notation "sourceObserve" => observer setup.source.crypto wire serverKeyId budget filter guess target
local notation "recordObserve" => recordObserver (n := n) (E := RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
  setup.source.crypto wire serverKeyId budget filter guess target
local notation "nativeWork" => RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "fullNative" => RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "actualNative" => RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "auditNative" => RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "realRecord" => RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "idealRecord" => RegistrationNativeRecordPackage.ctx (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "hitObserve" => RegistrationNativeLorRecordSecurity.hitObserver setup wire source serverKeyId seed scalar candidate budget target filter guess

noncomputable def full (winning : Bool) : ProbComp Bool := outcomeSelected (sourceObserve winning) <$> fullNative
noncomputable def hitFull (winning : Bool) : ProbComp Bool := hitObserve winning <$> fullNative

/-- The real record event derives hiddenness of every admitted test in the same original ledger. -/
theorem hit_real (winning : Bool) :
    𝒟[hitObserve winning <$> actualNative] {true} ≤ 𝒟[recordObserve winning <$> realRecord] {true} := by
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, RegistrationNativeLorRecordSecurity.hitObserver,
    Bool.and_eq_true, decide_eq_true_eq, record_event] using
    RegistrationNativeLorRecordTrace.actual_probability (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary (sourceObserve winning)

theorem real_actual (winning : Bool) :
    𝒟[recordObserve winning <$> realRecord] {true} ≤ 𝒟[outcomeSelected (sourceObserve winning) <$> actualNative] {true} := by
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, record_event] using
    RegistrationNativeLorRecordTrace.forget_probability (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary (sourceObserve winning)

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def loss (winning : Bool) : ℝ≥0∞ :=
  RegistrationNativeWeightedRecordSecurity.recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds adversary budget allowance constructorCoins mlCoins hmac fallback (recordObserve winning)

noncomputable def delta (winning : Bool) : ℝ≥0∞ := 𝒟[auditNative] {true} +
  loss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds
    adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback winning

variable (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
  (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)

include bounded framed constructorBound mlBound correct in
theorem record_distance (winning : Bool) :
    ENNReal.ofReal ((recordObserve winning <$> realRecord).boolDistance (recordObserve winning <$> idealRecord)) ≤
      loss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds
        adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback winning := by
  exact RegistrationNativeWeightedRecordSecurity.record_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds adversary budget allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct (recordObserve winning)

include bounded framed constructorBound mlBound correct in
/-- Both selected-receipt observers reach the literal fair ideal with their own record and repeat loss. -/
theorem hit_to_ideal (winning : Bool) :
    𝒟[hitFull (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess winning] {true} ≤
      𝒟[recordObserve winning <$> idealRecord] {true} +
        delta (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
          allowance constructorCoins mlCoins hmac fallback winning := by
  have repeated := RegistrationNativeSelectedRecordTrace.repeat_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds .P adversary (hitObserve winning)
  rw [prEvent_eq_evalDist_singleton] at repeated
  exact RegistrationNativeLorRecordSecurity.forward_probability _ _ _ _ _ _ _ le_rfl
    (hit_real setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess winning)
    repeated (record_distance setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
      allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct winning)

include bounded framed constructorBound mlBound correct in
/-- The fair ideal returns to the original full observer through its own billed losses. -/
theorem ideal_to_full (winning : Bool) :
    𝒟[recordObserve winning <$> idealRecord] {true} ≤
      𝒟[full (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess winning] {true} +
        delta (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
          allowance constructorCoins mlCoins hmac fallback winning := by
  have repeated := RegistrationNativeSelectedRecordTrace.repeat_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds .P adversary (outcomeSelected (sourceObserve winning))
  rw [prEvent_eq_evalDist_singleton] at repeated
  exact RegistrationNativeLorRecordSecurity.reverse_probability _ _ _ _ _ _
    (real_actual setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess winning)
    repeated (record_distance setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
      allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct winning)


local notation "sourceFull" => full (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
  bounds adversary budget target filter guess
local notation "sourceHit" => hitFull (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
  bounds adversary budget target filter guess
local notation "targetDelta" => delta (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
  bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback

include bounded framed constructorBound mlBound correct in
/-- The two original observer directions pay the win loss plus one half of the eligibility loss. Concrete source provenance supplies the remaining hitFull premises as theorems, not assumptions. -/
theorem bound :
    (𝒟[sourceHit true] {true} ≤ 2⁻¹ * 𝒟[sourceFull false] {true} + targetDelta true + 2⁻¹ * targetDelta false) ∧
      (2⁻¹ * 𝒟[sourceHit false] {true} ≤ 𝒟[sourceFull true] {true} + targetDelta true + 2⁻¹ * targetDelta false) := by
  have fair := RegistrationNativeLorStartup.record_lor (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds adversary budget filter guess target
  change 𝒟[recordObserve true <$> idealRecord] {true} = 2⁻¹ * 𝒟[recordObserve false <$> idealRecord] {true} at fair
  have hitWin := hit_to_ideal setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct true
  have hitElig := hit_to_ideal setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct false
  have backWin := ideal_to_full setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct true
  have backElig := ideal_to_full setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct false
  constructor
  · calc
      _ ≤ 𝒟[recordObserve true <$> idealRecord] {true} + targetDelta true := hitWin
      _ = 2⁻¹ * 𝒟[recordObserve false <$> idealRecord] {true} + targetDelta true := by rw [fair]
      _ ≤ 2⁻¹ * (𝒟[sourceFull false] {true} + targetDelta false) + targetDelta true := add_le_add (mul_le_mul' le_rfl backElig) le_rfl
      _ = _ := by rw [mul_add]; ac_rfl
  · calc
      _ ≤ 2⁻¹ * (𝒟[recordObserve false <$> idealRecord] {true} + targetDelta false) := mul_le_mul' le_rfl hitElig
      _ = 𝒟[recordObserve true <$> idealRecord] {true} + 2⁻¹ * targetDelta false := by rw [mul_add, ← fair]
      _ ≤ (𝒟[sourceFull true] {true} + targetDelta true) + 2⁻¹ * targetDelta false := add_le_add backWin le_rfl

end BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.hit_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.hit_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.real_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.real_actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.record_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.record_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.hit_to_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.hit_to_ideal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.ideal_to_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.ideal_to_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed.bound
