-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity

/-! The actual selected winning and selector observers each traverse the native repeat and record reductions. Their separate losses are kept explicit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectedRecordTrace (outcomeSelected viewSelected)
open RegistrationNativeWeightedRecordView (selection winning)
variable {n : Nat} {ι KemSK ProviderState Value E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)

theorem actual_selection :
    outcomeSelected select <$>
      RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary =
      viewSelected select <$>
        RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
          (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
            selectedOwner selectedAccept bounds mode adversary) := by
  rw [RegistrationNativeG3MaterializedTracedStartup.actual_source,
    ← RegistrationNativeRecordViewCrypto.real_result_source,
    ← RegistrationNativeSelectiveRecordTraceView.real_erase setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary]
  simp only [Functor.map_map]
  congr 1
  funext view
  exact RegistrationNativeSelectedRecordTrace.erase_selection select view

section Weighted
open RegistrationNativeCanonicalSelector (Target selected)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordBills (programBill)
open RegistrationNativeRecordViewCrypto (chainLoss authLoss privacyLoss)
variable (padversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (target : Target budget)
  (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
local notation "targetSelect" => (fun result : Value × RegistrationNativeLedger.State =>
  selected setup.source.crypto wire serverKeyId budget claim target (Prod.fst result) (Prod.snd result))
local notation "nativeWork" => RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P padversary
local notation "fullNative" => RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P padversary
local notation "actualNative" => RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P padversary
local notation "realRecord" => RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "idealRecord" => RegistrationNativeRecordPackage.ctx (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "selectedView" => selection (n := n) (E := RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) setup.source.crypto wire serverKeyId budget claim target
local notation "winningView" => winning (n := n) (E := RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) setup.source.crypto wire serverKeyId budget claim target

local notation "hitObserver" => (fun outcome => RegistrationNativeSelectiveRecordTraceTarget.event setup seed scalar candidate claim outcome &&
  outcomeSelected targetSelect outcome)
local notation "auditNative" => RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider providerState selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P padversary

theorem hit_to_real : 𝒟[hitObserver <$> actualNative] {true} ≤ 𝒟[winningView <$> realRecord] {true} := by
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, Bool.and_eq_true,
    RegistrationNativeSelectiveRecordTraceTarget.event, decide_eq_true_eq,
    RegistrationNativeWeightedRecordView.winning, RegistrationNativeWeightedRecordView.selection,
    RegistrationNativeRecordViewFresh.event, and_comm] using
    RegistrationNativeSelectedRecordTrace.actual_probability (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P padversary claim targetSelect

noncomputable def recordLoss
    (observe : View n (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value → Bool) : ℝ≥0∞ :=
  chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork budget observe hmac +
  authLoss setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork budget observe fallback
    (programBill budget bounds allowance constructorCoins mlCoins .hash)
    (programBill budget bounds allowance constructorCoins mlCoins .raw) +
  privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork budget observe

variable (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (padversary publication))
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
  (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)

include bounded framed constructorBound mlBound correct in
theorem record_distance
    (observe : View n (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value → Bool) :
    ENNReal.ofReal ((observe <$> realRecord).boolDistance (observe <$> idealRecord)) ≤
      recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
        bounds padversary budget allowance constructorCoins mlCoins hmac fallback observe := by
  have compared := RegistrationNativeSelectiveRecordViewSecurity.random_bound setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds .P padversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound observe hmac correct fallback
  have endpoint := congrArg (Functor.map observe)
    (RegistrationNativeSelectiveRecordViewSource.ideal_source setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds .P padversary (fun _ => .random))
  simp only [Functor.map_map] at endpoint
  rw [← endpoint] at compared
  exact compared

set_option maxHeartbeats 1200000 in
include bounded framed constructorBound mlBound correct in
theorem ideal_selector :
    𝒟[selectedView <$> idealRecord] {true} ≤
      𝒟[outcomeSelected targetSelect <$> fullNative] {true} +
        𝒟[auditNative] {true} +
        recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
          bounds padversary budget allowance constructorCoins mlCoins hmac fallback selectedView := by
  have record := record_distance setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds padversary budget allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct selectedView
  have repeated := RegistrationNativeSelectedRecordTrace.repeat_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds .P padversary (outcomeSelected targetSelect)
  have first := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (selectedView <$> idealRecord) (selectedView <$> realRecord)
  rw [ProbComp.boolDistance_comm] at first
  have second := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (outcomeSelected targetSelect <$> actualNative)
    (outcomeSelected targetSelect <$> fullNative)
  rw [ProbComp.boolDistance_comm] at second
  have exactSelection := actual_selection (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds .P padversary targetSelect
  change outcomeSelected targetSelect <$> actualNative = selectedView <$> realRecord at exactSelection
  rw [exactSelection] at second repeated
  rw [prEvent_eq_evalDist_singleton] at repeated
  exact first.trans ((add_le_add ((second.trans (add_le_add le_rfl repeated))) record))

local notation "winLoss" => recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
  selectedOwner selectedAccept bounds padversary budget allowance constructorCoins mlCoins hmac fallback winningView
local notation "selLoss" => recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
  selectedOwner selectedAccept bounds padversary budget allowance constructorCoins mlCoins hmac fallback selectedView

set_option maxHeartbeats 1200000 in
include bounded framed constructorBound mlBound correct in
theorem hit_to_ideal :
    𝒟[hitObserver <$> fullNative] {true} ≤
      𝒟[winningView <$> idealRecord] {true} + 𝒟[auditNative] {true} + winLoss := by
  have repeated := RegistrationNativeSelectedRecordTrace.repeat_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds .P padversary hitObserver
  rw [prEvent_eq_evalDist_singleton] at repeated
  have attached := hit_to_real (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds claim padversary budget target
  have record := record_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds padversary budget allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct winningView
  have first := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (hitObserver <$> fullNative) (hitObserver <$> actualNative)
  have second := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (winningView <$> realRecord) (winningView <$> idealRecord)
  have combined := first.trans (add_le_add (attached.trans (second.trans (add_le_add le_rfl record))) repeated)
  simpa only [add_assoc, add_comm, add_left_comm] using combined

set_option maxHeartbeats 1200000 in
include bounded framed constructorBound mlBound correct in
theorem bound :
    𝒟[hitObserver <$> fullNative] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * 𝒟[outcomeSelected targetSelect <$> fullNative] {true} +
        (𝒟[auditNative] {true} + winLoss) +
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * (𝒟[auditNative] {true} + selLoss) := by
  have won := hit_to_ideal (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds claim padversary budget target allowance constructorCoins mlCoins hmac fallback
    bounded framed constructorBound mlBound correct
  have selectedBound := ideal_selector (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds claim padversary budget target allowance constructorCoins mlCoins hmac fallback
    bounded framed constructorBound mlBound correct
  have entropy := RegistrationNativeWeightedRecordView.fresh_bytes (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds padversary claim budget target
  calc
    _ ≤ 𝒟[winningView <$> idealRecord] {true} + 𝒟[auditNative] {true} + winLoss := won
    _ ≤ (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * 𝒟[selectedView <$> idealRecord] {true}) + 𝒟[auditNative] {true} + winLoss :=
      add_le_add (add_le_add entropy le_rfl) le_rfl
    _ ≤ (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        (𝒟[outcomeSelected targetSelect <$> fullNative] {true} + 𝒟[auditNative] {true} + selLoss)) + 𝒟[auditNative] {true} + winLoss :=
      add_le_add (add_le_add (mul_le_mul' le_rfl selectedBound) le_rfl) le_rfl
    _ = _ := by simp only [mul_add]; ac_rfl

end Weighted


end BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.actual_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.hit_to_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.hit_to_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.record_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.record_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.ideal_selector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.ideal_selector

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.hit_to_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.hit_to_ideal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity.bound
