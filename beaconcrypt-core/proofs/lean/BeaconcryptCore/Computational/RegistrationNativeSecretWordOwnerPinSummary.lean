-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! The actual Word source realizes the original public owner pin-summary from the empty roster. Every complete original ledger step preserves the literal configured bindings, including private secrecy draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentTranscript (summarize step)
open RegistrationNativeInterface (Entry)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordOwnerPins (key)
open RegistrationNativeOwnerPinSummaryStep (advance)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
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


variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl

private theorem secrecy_pins (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range (.inr secrecy) × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl (.inr secrecy)).run before)) :
    result.2.2.1.beacons.map key = before.2.1.beacons.map key := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨current, reached, rfl⟩ := supported
  exact RegistrationNativeSecretWordOwnerPinRaw.quiet setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey _
    (RegistrationNativeOwnerPinSummaryCore.secrecy_quiet setup.source.crypto wire serverKeyId bounds secrecy before.1) before.2 current reached

def Holds (transcript : List Entry) (owners : RegistrationNativePublicOwners.State source) : Prop :=
  (summarize (transcript.map Entry.erase)).owners = owners.map key

/-- Every actual complete original ledger call implements the exact configured-pin summary update. -/
theorem full (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source) (prior : Holds before.1.transcript before.2.1.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl query).run before)) :
    Holds result.2.1.transcript result.2.2.1.beacons := by
  have trace := RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result supported
  change (summarize (result.2.1.transcript.map Entry.erase)).owners = result.2.2.1.beacons.map key
  rw [trace, List.map_append, List.map_cons, List.map_nil, summary_append]
  cases query with
  | inr secrecy =>
      change (summarize (before.1.transcript.map Entry.erase)).owners = result.2.2.1.beacons.map key
      exact prior.trans (secrecy_pins setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds secrecy before result supported).symm
  | inl query =>
      rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at supported
      obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
      cases equal
      rw [step_advance]
      change advance (summarize (before.1.transcript.map Entry.erase)).owners query reply = after.1.beacons.map key
      rw [prior]
      exact (RegistrationNativeSecretWordOwnerPinRaw.step setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query before.2 reply after reached).symm

/-- The complete original Word execution derives its original public pin-summary from the actual empty owner roster. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (empty : before.1.beacons = []) (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typedImpl mode work before)) :
    (summarize result.2.1.ledger.transcript).owners = result.2.2.1.beacons.map key := by
  have actual : Holds result.2.1.transcript result.2.2.1.beacons := by
    apply OracleComp.simulateQ_run_preserves_inv_of_query
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl)
      (fun current => Holds current.1.transcript current.2.1.beacons)
      (fun query current prior next reached => full setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query current prior next reached)
      _ (RegistrationNativeLedger.empty, before) _ result supported
    simp only [Holds, RegistrationNativeLedger.empty, List.map_nil, summarize,
      PqxdhDeploymentTranscript.Summary.empty, List.foldl_nil, empty]
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typedImpl mode work before result supported
  rw [projected]
  exact actual
end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary.run
