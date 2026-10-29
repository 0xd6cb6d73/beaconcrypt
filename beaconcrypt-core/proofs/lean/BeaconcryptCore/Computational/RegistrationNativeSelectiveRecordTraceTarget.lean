-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartup
import BeaconcryptCore.Computational.RegistrationNativeInstallTarget
import BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh

/-! The target predicate reads only the original claim, complete original ledger and native installation trace. In the actual real selective source its selected ordinal gives the same claimed physical hidden handle; only this permitted fresh-hit observation continues through the record cryptographic hops. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectiveRecordTraceStartup (Extra program)
open RegistrationNativeInstallKernelStorage (Selected)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Hit (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) : Prop :=
  match outcome with
  | none => False
  | some finished => RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
      (Selected setup seed scalar candidate)

noncomputable def event (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) : Bool :=
  @decide (Hit setup seed scalar candidate claim outcome) (Classical.propDecidable _)

/-- A selected final ordinal in the same actual annotated trace yields the claimed literal fresh hit in the permitted record view. -/
theorem view_hit (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (view : View n (Extra n KemSK ProviderState source) Value)
    (hidden : RegistrationNativeSelectiveRecordTraceView.Hidden setup seed scalar candidate view)
    (hit : Hit setup seed scalar candidate claim (RegistrationNativeG3MaterializedTracedStartup.publicOutcome view.result)) :
    RegistrationNativeRecordViewFresh.FreshHit claim (RegistrationNativeSelectiveRecordTraceView.erase view) := by
  cases outcome : view.result with
  | none => simp only [RegistrationNativeG3MaterializedTracedStartup.publicOutcome, outcome, Option.map_none, Hit] at hit
  | some finished =>
      have claimed : RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
          (Selected setup seed scalar candidate) := by
        simpa only [RegistrationNativeG3MaterializedTracedStartup.publicOutcome, outcome, Option.map_some, Hit] using hit
      have origin := hidden finished (by simp only [outcome, Option.mem_some_iff])
      obtain ⟨index, guess, entry, claimAt, fresh, guessed, slot⟩ := RegistrationNativeInstallTarget.hidden claim finished.2.1.1
        finished.2.1.2 finished.2.2.2.events (Selected setup seed scalar candidate) view.slots claimed origin
      refine ⟨(finished.1, finished.2.1, finished.2.2.1), ?_, index, guess, entry, claimAt, fresh, slot, guessed⟩
      simp only [RegistrationNativeSelectiveRecordTraceView.erase, RegistrationNativeSelectiveRecordTraceStartup.forget,
        outcome, Option.map_some, Option.mem_some_iff]

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (claim : Value → Option (Nat × Pqxdh.Bytes))

/-- The actual selective target event is bounded by the same claimed hidden fresh hit in the existing real record observation. -/
theorem actual_probability :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[Hit setup seed scalar candidate claim outcome] ≤
      Pr{let view ← (RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary))}[RegistrationNativeRecordViewFresh.FreshHit claim view] := by
  rw [RegistrationNativeG3MaterializedTracedStartup.actual_source,
    ← RegistrationNativeRecordViewCrypto.real_result_source,
    ← RegistrationNativeSelectiveRecordTraceView.real_erase setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary]
  simp only [prEvent_map]
  apply prEvent_mono_of_support
  intro view supported hit
  exact view_hit setup seed scalar candidate claim view
    (RegistrationNativeSelectiveRecordTraceView.real_hidden setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary view supported) hit

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget.view_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget.view_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget.actual_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget.actual_probability
