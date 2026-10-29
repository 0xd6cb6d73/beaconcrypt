-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep
import BeaconcryptCore.Computational.RegistrationNativeScalarRun

/-! The literal original transcript summary lists exactly the configured bindings of the actual current owner roster, in public owner order. Generated startup supplies the empty base case. This closes original OWNER designation against current native pins without owner-before-accept, identity-injectivity or accepted-credential matching assumptions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeOwnerPinSummaryCore (pins)
open RegistrationNativeOwnerPinSummaryStep (advance)
open RegistrationNativeInterface (Entry)
open PqxdhDeploymentTranscript (summarize step)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

private theorem summary_append (transcript : List PqxdhDeploymentInterface.Entry) (entry : PqxdhDeploymentInterface.Entry) :
    (summarize (transcript ++ [entry])).owners = (step (summarize transcript) entry).owners := by
  simp only [summarize, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem step_advance (summary : PqxdhDeploymentTranscript.Summary)
    (query : RegistrationNativeInterface.Spec.Domain) (reply : RegistrationNativeInterface.Spec.Range query) :
    (step summary (Entry.erase ⟨.inl query, reply⟩)).owners = advance summary.owners query reply := by
  cases query with
  | inl coin => rfl
  | inr command => cases command with
    | create edPin mlPin keyId =>
        cases reply with
        | none => rfl
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin edPin <;>
              simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, step,
                PqxdhDeploymentTranscript.stepCommand, advance, parsed]
    | bundle owner =>
        cases reply <;> simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, step,
          PqxdhDeploymentTranscript.stepCommand, advance]
        all_goals split <;> rfl
    | finish owner raw =>
        cases reply <;> simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, step,
          PqxdhDeploymentTranscript.stepCommand, advance]
        all_goals split <;> rfl
    | _ => rfl

private theorem secrecy_pins (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range (.inr secrecy) × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) (.inr secrecy)).run before)) :
    pins result.2.2.beacons = pins before.2.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨current, reached, rfl⟩ := supported
  exact RegistrationNativeOwnerPinSummaryCore.raw_quiet setup checks wire route representation created credential _
    (RegistrationNativeOwnerPinSummaryCore.secrecy_quiet setup.source.crypto wire created.server.server.metadata.sender bounds secrecy before.1)
    before.2 current reached

def Holds (transcript : List Entry) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  (summarize (transcript.map Entry.erase)).owners = pins owners

/-- Every complete original native ledger step implements the exact pin-list summary update. -/
theorem step_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source) (prior : Holds before.1.transcript before.2.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Holds result.2.1.transcript result.2.2.beacons := by
  have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result supported
  change (summarize (result.2.1.transcript.map Entry.erase)).owners = pins result.2.2.beacons
  rw [trace, List.map_append, List.map_cons, List.map_nil, summary_append]
  cases query with
  | inr secrecy =>
      change (summarize (before.1.transcript.map Entry.erase)).owners = pins result.2.2.beacons
      exact prior.trans (secrecy_pins setup checks wire route representation created credential bounds secrecy before result supported).symm
  | inl query =>
      rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at supported
      obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
      cases equal
      rw [step_advance]
      change advance (summarize (before.1.transcript.map Entry.erase)).owners query reply = pins after.beacons
      rw [prior]
      exact (RegistrationNativeOwnerPinSummaryStep.raw_step setup checks wire route representation created credential query before.2 reply after reached).symm

/-- Arbitrary native runs from the actual empty local roster preserve the entire public pin-summary equality. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (empty : before.beacons = []) (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Holds result.2.1.transcript result.2.2.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential))
    (fun current => Holds current.1.transcript current.2.beacons)
    (fun query current prior next reached => step_holds setup checks wire route representation created credential bounds query current prior next reached)
    _ (RegistrationNativeLedger.empty, before) _ result supported
  simp only [Holds, RegistrationNativeLedger.empty, List.map_nil, summarize,
    PqxdhDeploymentTranscript.Summary.empty, List.foldl_nil, empty, pins]

/-- Generated native startup derives exact original-summary-to-current-owner bindings internally. -/
theorem initialized_summary (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    (summarize result.2.1.ledger.transcript).owners = pins result.2.2.beacons := by
  have actual := run_holds setup checks wire route representation initial.created initial.credential bounds mode work initial.state
    (RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial started) result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire initial.created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) mode work initial.state result supported
  rw [projected]
  exact actual

/-- Original OWNER designation's selected public binding belongs to the actual final native owner at that same index. -/
theorem initialized_owner (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (index : Nat) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : U64)
    (found : (summarize result.2.1.ledger.transcript).owners[index]? = some (pin, keyId)) :
    ∃ owner, result.2.2.beacons[index]? = some owner ∧ owner.pin.binding = ⟨pin, keyId⟩ := by
  rw [initialized_summary setup checks wire route representation ensureInit identityIndex serverKeyId initial started bounds mode work result supported,
    pins, List.getElem?_map] at found
  obtain ⟨owner, selected, binding⟩ := Option.map_eq_some_iff.mp found
  refine ⟨owner, selected, ?_⟩
  have identity := congrArg Prod.fst binding
  have assigned := congrArg Prod.snd binding
  cases actual : owner.pin.binding
  simp only [actual] at identity assigned
  cases identity
  cases assigned
  rfl

end BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.step_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.step_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.run_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.initialized_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.initialized_summary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.initialized_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummary.initialized_owner
