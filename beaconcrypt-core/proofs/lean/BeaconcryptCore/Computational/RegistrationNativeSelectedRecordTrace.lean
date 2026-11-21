-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity

/-! Exact trace erasure retains arbitrary original-ledger selection predicates while converting a proved selected physical origin into a hidden fresh hit. Publicness is a separate property of the concrete selector. The whole-client repeat audit applies to each observer independently, retaining failed operations and all later callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectiveRecordTraceStartup (Extra)
variable {n : Nat} {ι KemSK ProviderState Value E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def outcomeSelected (select : Value × RegistrationNativeLedger.State → Bool)
    (outcome : RegistrationNativeEntropyRun.Outcome E Value) : Bool :=
  outcome.elim false (fun finished => select finished.2.1)

def viewSelected (select : Value × RegistrationNativeLedger.State → Bool) (view : View n E Value) : Bool :=
  outcomeSelected select view.result

theorem erase_selection (select : Value × RegistrationNativeLedger.State → Bool)
    (view : View n (Extra n KemSK ProviderState source) Value) :
    outcomeSelected select (RegistrationNativeG3MaterializedTracedStartup.publicOutcome view.result) =
      viewSelected select (RegistrationNativeSelectiveRecordTraceView.erase view) := by
  rcases view with ⟨outcome, produced, raw, slots⟩
  cases outcome <;> rfl

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)

theorem actual_probability :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[
        RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome ∧ outcomeSelected select outcome = true] ≤
      Pr{let view ← (RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary))}[
            RegistrationNativeRecordViewFresh.FreshHit claim view ∧ viewSelected select view = true] := by
  rw [RegistrationNativeG3MaterializedTracedStartup.actual_source,
    ← RegistrationNativeRecordViewCrypto.real_result_source,
    ← RegistrationNativeSelectiveRecordTraceView.real_erase setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary]
  simp only [prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun view supported hit =>
    ⟨RegistrationNativeSelectiveRecordTraceTarget.view_hit setup seed scalar candidate claim view
      (RegistrationNativeSelectiveRecordTraceView.real_hidden setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary view supported) hit.1,
      (erase_selection select view).symm.trans hit.2⟩

/-- The same actual whole-client repeat audit bounds every retained selector or selected winning observer separately. -/
theorem repeat_distance
    (observe : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value → Bool) :
    ENNReal.ofReal
      ((observe <$> RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary).boolDistance
        (observe <$> RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
          seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)) ≤
      Pr{let bad ← (RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[bad = true] := by
  have repeated := RegistrationNativeG3MaterializedTracedStartupBound.bound (n := n) setup checks wire route source serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds mode adversary ensureInit identityIndex
  rw [RegistrationNativeG3MaterializedTracedStartup.audit_source] at repeated
  exact (ENNReal.ofReal_le_ofReal ((boolDistance_le_discreteDistance _ _).trans
    (discreteDistance_map_le observe _ _))).trans repeated

end BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.erase_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.erase_selection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.actual_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.actual_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.repeat_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace.repeat_distance
