-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorStartup
import BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace
import BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity
import BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant

/-! Each original native LR observer is retained separately through actual all-test provenance, the whole-client repeat audit and billed record reductions. Public test-session existence is made explicit in the source observer and is derived from firstTest on every supported original native execution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectedRecordTrace (outcomeSelected viewSelected)
variable {n : Nat} {ι KemSK E Value : Type} {base : OracleSpec ι}

noncomputable def observer (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) (result : Value × RegistrationNativeLedger.State) : Bool :=
  (if winning then RegistrationNativeLorCanonical.w crypto wire serverKeyId budget filter guess target result
    else RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target result) && result.2.ledger.test.isSome

noncomputable def recordObserver (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) (view : View n E Value) : Bool :=
  if winning then RegistrationNativeLorEntropy.winningView crypto wire serverKeyId budget filter guess target view
    else RegistrationNativeLorEntropy.eligibleView crypto wire serverKeyId budget filter target view

/-- Every source target observer retains its original public good-target event. -/
theorem observer_good (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) (result : Value × RegistrationNativeLedger.State)
    (hit : observer crypto wire serverKeyId budget filter guess target winning result = true) :
    RegistrationNativeLorCanonical.GoodAt crypto wire serverKeyId budget filter target result := by
  cases winning <;> simp only [observer, Bool.false_eq_true, ite_false, ite_true,
    Bool.and_eq_true, RegistrationNativeLorCanonical.w, RegistrationNativeLorCanonical.j, decide_eq_true_eq] at hit
  · exact hit.1
  · exact hit.1.1

set_option backward.isDefEq.respectTransparency false in
/-- The record observer is exactly all admitted tests hidden and the same source observer on the retained ledger. -/
theorem record_event (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) (view : View n E Value) :
    recordObserver crypto wire serverKeyId budget filter guess target winning view = true ↔
      RegistrationNativeLorRecordTrace.TestsHidden crypto wire serverKeyId view ∧
        viewSelected (observer crypto wire serverKeyId budget filter guess target winning) view = true := by
  rcases view with ⟨outcome, produced, raw, slots⟩
  cases outcome with
  | none => cases winning <;> simp only [recordObserver, Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeLorEntropy.winningView, RegistrationNativeLorEntropy.eligibleView, Option.elim_none,
      viewSelected, outcomeSelected, and_false]
  | some finished =>
      cases winning <;> simp only [recordObserver, Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeLorEntropy.winningView, RegistrationNativeLorEntropy.eligibleView, Option.elim_some,
        RegistrationNativeLorEntropy.HiddenTests, Bool.and_eq_true, decide_eq_true_eq,
        RegistrationNativeLorRecordTrace.TestsHidden, Option.mem_some_iff,
        viewSelected, outcomeSelected, observer]
      all_goals constructor
      all_goals
        first
        | rintro ⟨observed, tested, hidden⟩; exact ⟨⟨finished, rfl, hidden⟩, observed, tested⟩
        | rintro ⟨⟨other, rfl, hidden⟩, observed, tested⟩; exact ⟨observed, tested, hidden⟩


/-- The explicit test-existence conjunct is derived on every supported original native execution, including all send failures. -/
theorem observer_run {NativeState : Type} (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : FreshBounds) (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : NativeState) (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) :
    observer crypto wire serverKeyId budget filter guess target winning (result.1, result.2.1) =
      if winning then RegistrationNativeLorCanonical.w crypto wire serverKeyId budget filter guess target (result.1, result.2.1)
      else RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target (result.1, result.2.1) := by
  have present : (if winning then RegistrationNativeLorCanonical.w crypto wire serverKeyId budget filter guess target (result.1, result.2.1)
      else RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target (result.1, result.2.1)) = true →
      result.2.1.ledger.test.isSome = true := by
    intro observed
    have good : RegistrationNativeLorCanonical.GoodAt crypto wire serverKeyId budget filter target (result.1, result.2.1) := by
      cases winning <;> simp only [Bool.false_eq_true, ite_false, ite_true, RegistrationNativeLorCanonical.w, RegistrationNativeLorCanonical.j,
        Bool.and_eq_true, decide_eq_true_eq] at observed
      · exact observed
      · exact observed.1
    obtain ⟨session, raw, eligible, scanned⟩ := good.1
    obtain ⟨first, tested, designated⟩ := eligible.2.1
    apply RegistrationNativeLedgerTestInvariant.run_test_exists crypto wire serverKeyId bounds typed mode work before result supported
    simp only [tested, Option.isSome_some]
  apply Bool.eq_iff_iff.mpr
  simp only [observer, Bool.and_eq_true]
  exact ⟨And.left, fun observed => ⟨observed, present observed⟩⟩

theorem forward_probability (full hitFull hitActual real ideal audit : ProbComp Bool) (loss : ℝ≥0∞)
    (provenance : 𝒟[full] {true} ≤ 𝒟[hitFull] {true}) (attached : 𝒟[hitActual] {true} ≤ 𝒟[real] {true})
    (repeated : ENNReal.ofReal (hitFull.boolDistance hitActual) ≤ 𝒟[audit] {true})
    (recorded : ENNReal.ofReal (real.boolDistance ideal) ≤ loss) :
    𝒟[full] {true} ≤ 𝒟[ideal] {true} + (𝒟[audit] {true} + loss) := by
  have first := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance hitFull hitActual
  have second := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance real ideal
  have combined := provenance.trans (first.trans (add_le_add (attached.trans (second.trans (add_le_add le_rfl recorded))) repeated))
  exact combined.trans (le_of_eq (by ac_rfl))

theorem reverse_probability (full actual real ideal audit : ProbComp Bool) (loss : ℝ≥0∞)
    (forgotten : 𝒟[real] {true} ≤ 𝒟[actual] {true})
    (repeated : ENNReal.ofReal (full.boolDistance actual) ≤ 𝒟[audit] {true})
    (recorded : ENNReal.ofReal (real.boolDistance ideal) ≤ loss) :
    𝒟[ideal] {true} ≤ 𝒟[full] {true} + (𝒟[audit] {true} + loss) := by
  have first := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance ideal real
  rw [ProbComp.boolDistance_comm] at first
  have second := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance actual full
  rw [ProbComp.boolDistance_comm] at second
  exact first.trans (add_le_add (forgotten.trans (second.trans (add_le_add le_rfl repeated))) recorded) |>.trans (le_of_eq (by ac_rfl))

section GeneralRecord
variable {ProviderState : Type}
/-- Generic direct reduction expression avoids specializing or unfolding the concrete early provider inside the record theorem. -/
theorem generic_record_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (budget : Budget) (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat) (constructorCoins mlCoins : Nat)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (observe : View n (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value → Bool) :
    let work := RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds .P adversary
    ENNReal.ofReal ((observe <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route work).boolDistance
      (observe <$> RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route work)) ≤
      RegistrationNativeRecordViewCrypto.chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe hmac +
        RegistrationNativeRecordViewCrypto.authLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe fallback
          (RegistrationNativeSelectiveRecordBills.programBill budget bounds allowance constructorCoins mlCoins .hash)
          (RegistrationNativeSelectiveRecordBills.programBill budget bounds allowance constructorCoins mlCoins .raw) +
        RegistrationNativeRecordViewCrypto.privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe := by
  simpa only [RegistrationNativeWeightedRecordSecurity.recordLoss] using
    RegistrationNativeWeightedRecordSecurity.record_distance (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds adversary budget allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct observe
end GeneralRecord

section Fixed
open PqxdhRecordLiftInterface (EffectKind)
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (chosen : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
  (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
  (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
local notation "slotsCount" => budget.cap 4 + budget.cap 5
local notation "provider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate
local notation "nativeWork" => RegistrationNativeSelectiveRecordStartup.program (n := slotsCount) setup checks wire source ensureInit identityIndex serverKeyId
  seed scalar candidate provider none (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "fullNative" => RegistrationNativeG3MaterializedTracedStartup.fullGame (n := slotsCount) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider none (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "actualNative" => RegistrationNativeG3MaterializedTracedStartup.actual (n := slotsCount) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider none (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "auditNative" => RegistrationNativeG3MaterializedStartup.audit (n := slotsCount) setup checks wire route source ensureInit identityIndex serverKeyId
  seed scalar candidate provider none (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "realRecord" => RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "idealRecord" => RegistrationNativeRecordPackage.ctx (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) setup (RegistrationNativeWire.ledgerCodec wire) route nativeWork
local notation "sourceObserve" => observer setup.source.crypto wire serverKeyId budget filter guess target
local notation "recordObserve" => recordObserver (n := slotsCount)
  (E := RegistrationNativeSelectiveEntropyEnvironment.State slotsCount KemSK RegistrationNativeKemSwitchSource.Phase source)
  setup.source.crypto wire serverKeyId budget filter guess target

noncomputable def full (winning : Bool) : ProbComp Bool := outcomeSelected (sourceObserve winning) <$> fullNative
noncomputable def hitObserver (winning : Bool)
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) : Bool :=
  @decide (RegistrationNativeLorTargetSource.Hit setup wire serverKeyId seed scalar candidate outcome) (Classical.propDecidable _) &&
    outcomeSelected (sourceObserve winning) outcome

/-- Original canonical good-target provenance supplies every admitted test's receipt while retaining either original observer. -/
theorem full_hit (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[target.2.val]? = some chosen)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (winning : Bool) :
    𝒟[full setup checks wire route source ensureInit identityIndex serverKeyId seed scalar pairs chosen challenge candidate bounds adversary budget target filter guess winning] {true} ≤
      𝒟[hitObserver setup wire source serverKeyId seed scalar candidate budget target filter guess winning <$> fullNative] {true} := by
  have receipts := RegistrationNativeLorTargetSource.startup_probability (source := source) setup checks wire route seed scalar pairs chosen challenge serverKeyId bounds .P
    budget target ensureInit identityIndex adversary candidate filter (sourceObserve winning) bounded reserved chosenAt readback responseReadback
  simp only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, full, hitObserver, Bool.and_eq_true, decide_eq_true_eq] at receipts ⊢
  refine le_trans ?_ receipts
  apply prEvent_mono
  intro outcome observed
  cases outcome with
  | none => simp only [outcomeSelected, Option.elim_none, Bool.false_eq_true] at observed
  | some finished => exact ⟨observer_good setup.source.crypto wire serverKeyId budget filter guess target winning finished.2.1 observed, observed⟩

/-- Actual selected receipts attach to all physical hidden test handles, retaining either original observer. -/
theorem hit_real (winning : Bool) :
    𝒟[hitObserver setup wire source serverKeyId seed scalar candidate budget target filter guess winning <$> actualNative] {true} ≤
      𝒟[recordObserve winning <$> realRecord] {true} := by
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, hitObserver, Bool.and_eq_true, decide_eq_true_eq, record_event] using
    RegistrationNativeLorRecordTrace.actual_probability (n := slotsCount) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider none target.2.val target.1.val bounds .P adversary (sourceObserve winning)

/-- Forgetting physical hiddenness gives the exact original actual observer on its same complete ledger. -/
theorem real_actual (winning : Bool) :
    𝒟[recordObserve winning <$> realRecord] {true} ≤
      𝒟[outcomeSelected (sourceObserve winning) <$> actualNative] {true} := by
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, record_event] using
    RegistrationNativeLorRecordTrace.forget_probability (n := slotsCount) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider none target.2.val target.1.val bounds .P adversary (sourceObserve winning)


end Fixed
end BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.observer_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.observer_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.record_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.record_event

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.observer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.observer_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.forward_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.forward_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.reverse_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.reverse_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.generic_record_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.generic_record_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.full_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.full_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.hit_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.hit_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.real_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity.real_actual
