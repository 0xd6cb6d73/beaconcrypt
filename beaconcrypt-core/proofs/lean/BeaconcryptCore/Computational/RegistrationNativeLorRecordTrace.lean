-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorTargetSource
import BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace

/-! All admitted tests' same-trace selected installation receipts attach to actual physical hidden handles in the real native record observation. Arbitrary original-ledger observers, including the literal test-bit win and public eligibility separately, survive exact erasure. The exported probability statements derive hiddenness from the real execution invariant. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectiveRecordTraceStartup (Extra)
variable {n : Nat} {ι KemSK ProviderState Value E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def TestsHidden (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : Aeneas.Std.U64)
    (view : View n E Value) : Prop :=
  ∃ finished ∈ view.result, RegistrationNativeLorCanonical.OnTests crypto wire serverKeyId finished.2.1.2.ledger.transcript
    (fun handle => (view.slots handle).isSome)

/-- The actual same-trace physical invariant attaches every admitted selected test handle. -/
theorem view_tests (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : Aeneas.Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (view : View n (Extra n KemSK ProviderState source) Value)
    (hidden : RegistrationNativeSelectiveRecordTraceView.Hidden setup seed scalar candidate view)
    (hit : RegistrationNativeLorTargetSource.Hit setup wire serverKeyId seed scalar candidate
      (RegistrationNativeG3MaterializedTracedStartup.publicOutcome view.result)) :
    TestsHidden setup.source.crypto wire serverKeyId (RegistrationNativeSelectiveRecordTraceView.erase view) := by
  cases outcome : view.result with
  | none => simp only [RegistrationNativeG3MaterializedTracedStartup.publicOutcome, outcome, Option.map_none, RegistrationNativeLorTargetSource.Hit] at hit
  | some finished =>
      have selected : RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId finished.2.1.2 finished.2.2.2.events
          (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
        simpa only [RegistrationNativeG3MaterializedTracedStartup.publicOutcome, outcome, Option.map_some, RegistrationNativeLorTargetSource.Hit] using hit
      have origin := hidden finished (by simp only [outcome, Option.mem_some_iff])
      refine ⟨(finished.1, finished.2.1, finished.2.2.1), ?_, ?_⟩
      · simp only [RegistrationNativeSelectiveRecordTraceView.erase, RegistrationNativeSelectiveRecordTraceStartup.forget,
          outcome, Option.map_some, Option.mem_some_iff]
      · intro pre entry post handle left right split query admitted
        obtain ⟨role, ordinal, message, paired, chosen⟩ := selected pre entry post handle left right split query admitted
        exact origin role ordinal message handle paired chosen

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (observe : Value × RegistrationNativeLedger.State → Bool)

/-- All admitted test handles are proved hidden in the actual real record observation, retaining the same original observer. -/
theorem actual_probability :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[
        RegistrationNativeLorTargetSource.Hit setup wire serverKeyId seed scalar candidate outcome ∧
          RegistrationNativeSelectedRecordTrace.outcomeSelected observe outcome = true] ≤
    Pr{let view ← (RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary))}[
          TestsHidden setup.source.crypto wire serverKeyId view ∧ RegistrationNativeSelectedRecordTrace.viewSelected observe view = true] := by
  rw [RegistrationNativeG3MaterializedTracedStartup.actual_source,
    ← RegistrationNativeRecordViewCrypto.real_result_source,
    ← RegistrationNativeSelectiveRecordTraceView.real_erase setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary]
  simp only [prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun view supported hit =>
    ⟨view_tests setup wire serverKeyId seed scalar candidate view
      (RegistrationNativeSelectiveRecordTraceView.real_hidden setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary view supported) hit.1,
      (RegistrationNativeSelectedRecordTrace.erase_selection observe view).symm.trans hit.2⟩

/-- Erasing the hidden-test conjunct returns the exact original actual observer, so the reverse direction needs no hiddenness assumption. -/
theorem forget_probability :
    Pr{let view ← (RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary))}[
          TestsHidden setup.source.crypto wire serverKeyId view ∧ RegistrationNativeSelectedRecordTrace.viewSelected observe view = true] ≤
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[
        RegistrationNativeSelectedRecordTrace.outcomeSelected observe outcome = true] := by
  rw [RegistrationNativeG3MaterializedTracedStartup.actual_source,
    ← RegistrationNativeRecordViewCrypto.real_result_source,
    ← RegistrationNativeSelectiveRecordTraceView.real_erase setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary]
  simp only [prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun view _supported hit =>
    (RegistrationNativeSelectedRecordTrace.erase_selection observe view).trans hit.2

end BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.view_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.view_tests
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.actual_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.actual_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.forget_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace.forget_probability
