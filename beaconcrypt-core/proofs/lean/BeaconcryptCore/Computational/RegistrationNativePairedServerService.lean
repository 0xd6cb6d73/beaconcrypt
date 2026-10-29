-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativePairedChoice
import BeaconcryptCore.Computational.RegistrationBoundGate

/-! A native Server material service runs the actual current-pin/application/allocator gate before asking its paired key service. Protected replies run the real raw-record/sign/encode/publication controllers with a hidden installation reference; ordinary side replies retain their exact real output and known installation. The public hidden continuation receives only material44 and a slot. The private108/public44 service equality is proved from the concrete whole-kernel erasure, not supplied as a game premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedServerService
open PqxdhRecordLiftInterface
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat} {Encoded : Type}

abbrev Result (Encoded : Type) := RegistrationHiddenInstall.Result Encoded
abbrev Common (n : Nat) := RegistrationHiddenInstall.Spec n
abbrev PrivateSpec (n : Nat) := (Message →ₒ Option (PrivateChoice n)) + Common n
abbrev PublicSpec (n : Nat) := (Message →ₒ Option (Choice n)) + Common n

def privateCommon : QueryImpl (Common n) (OracleComp (PrivateSpec n)) :=
  fun query => (PrivateSpec n).query (.inr query)

def publicCommon : QueryImpl (Common n) (OracleComp (PublicSpec n)) :=
  fun query => (PublicSpec n).query (.inr query)

def erase : QueryImpl (PublicSpec n) (OracleComp (PrivateSpec n))
  | .inl message => Option.map publicChoice <$> (PrivateSpec n).query (.inl message)
  | .inr query => (PrivateSpec n).query (.inr query)

private def continueWith {Input : Type} (action : RustM Input)
    (next : Input → OracleComp (EnvEffects n) (RustM (Result Encoded))) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

private def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp (EnvEffects n) (RustM (Result Encoded))) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Ordinary source sessions transfer the actual native kernel through the native peer-insertion capability. -/
def knownInstall (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  continueResult (peer.begin_peer_insert control published) fun pending =>
    continueWith pending.request fun keyId =>
      continueWith pending.into_parts fun parts => do
        let inserted ← (EnvEffects n).query
          (.inr (.installServer keyId (PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet)))
        pure (parts.2.finish inserted)

def knownAfter (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) := continueResult published (knownInstall control)

/-- The ordinary branch makes exactly the native owned-peer insertion request, preserving all binding fields and its actual concrete kernel. -/
theorem knownInstall_native (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (pending : peer.PeerInsert Encoded)
    (prepared : peer.begin_peer_insert control published = .ok (.Ok pending)) :
    knownInstall (n := n) control published = (do
      let inserted ← (EnvEffects n).query (.inr (.installServer pending.peer.binding.assigned_key_id
        (PeerBinding.ofSession pending.peer.binding) (.known pending.peer.ratchet)))
      pure ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
        peer.PublicationFinish Encoded).finish inserted)) := by
  simp only [knownInstall, prepared, continueResult,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_request,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_parts, continueWith]

def knownStage (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) : OracleComp (Common n) (RustM (Result Encoded)) := do
  let published ← simulateQ RegistrationHiddenInstall.publicationLift
    (RegistrationBoundPublication.program encode initial output)
  simulateQ RegistrationHiddenInstall.effectLift (knownAfter control published)

def hiddenStage (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) : OracleComp (Common n) (RustM (Result Encoded)) := do
  let published ← simulateQ RegistrationHiddenInstall.publicationLift
    (RegistrationBoundPublication.thin encode initial reference.material)
  simulateQ RegistrationHiddenInstall.effectLift (RegistrationHiddenInstall.after control reference.slot published)

def privateBranch (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) :
    PrivateChoice n → OracleComp (Common n) (RustM (Result Encoded))
  | .known output => knownStage encode control initial output
  | .hidden slot output => RegistrationHiddenInstall.stage encode control slot initial output

def publicBranch (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) :
    Choice n → OracleComp (Common n) (RustM (Result Encoded))
  | .known output => knownStage encode control initial output
  | .hidden reference => hiddenStage encode control initial reference

/-- Exact primitive effects, ML signatures, dynamic encoding, populated binding and insertion decisions are preserved while the hidden seed leaves the public continuation. -/
theorem branch_split (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (choice : PrivateChoice n) :
    publicBranch encode control initial (publicChoice choice) = privateBranch encode control initial choice := by
  cases choice with
  | known output => rfl
  | hidden slot output =>
    change hiddenStage encode control initial ⟨slot, (PqxdhDeploymentHiddenLayout.splitOutput output).1⟩ =
      RegistrationHiddenInstall.stage encode control slot initial output
    have same := RegistrationHiddenInstall.stage_split encode control slot initial
      (PqxdhDeploymentHiddenLayout.splitOutput output).1 (PqxdhDeploymentHiddenLayout.splitOutput output).2
    simpa only [PqxdhDeploymentHiddenLayout.join_split, hiddenStage] using same.symm

theorem common_program {Value : Type} (work : OracleComp (Common n) Value) :
    simulateQ erase (simulateQ publicCommon work) = simulateQ privateCommon work := by
  rw [← QueryImpl.simulateQ_compose]
  have step : erase ∘ₛ publicCommon = (privateCommon : QueryImpl (Common n) (OracleComp (PrivateSpec n))) := by
    funext query
    simp only [QueryImpl.compose, publicCommon, simulateQ_spec_query, erase, privateCommon]
  rw [step]

def privateAdmitted (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message) :
    OracleComp (PrivateSpec n) (RustM (Result Encoded)) := do
  let selected ← (PrivateSpec n).query (.inl message)
  match selected with
  | none => pure (.ok (.Err control))
  | some choice => simulateQ privateCommon (privateBranch encode control initial choice)

def publicAdmitted (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message) :
    OracleComp (PublicSpec n) (RustM (Result Encoded)) := do
  let selected ← (PublicSpec n).query (.inl message)
  match selected with
  | none => pure (.ok (.Err control))
  | some choice => simulateQ publicCommon (publicBranch encode control initial choice)

theorem admitted_split (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message) :
    simulateQ (erase (n := n)) (publicAdmitted encode control initial message) =
      privateAdmitted encode control initial message := by
  simp only [publicAdmitted, privateAdmitted, simulateQ_bind, simulateQ_spec_query, erase, bind_map_left]
  apply bind_congr
  intro choice
  cases choice with
  | none => simp only [Option.map_none, simulateQ_pure]
  | some choice => simp only [Option.map_some, common_program, branch_split]

/-- Both services run this actual root-free native gate before material demand. -/
def gated {I : Type} {spec : OracleSpec I}
    (admitted : RegistrationBoundKeySchedule.PublicInitial → OracleComp spec (RustM (Result Encoded)))
    (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (agreement : RegistrationBoundGate.PublicAgreement) (application : Slice U8) :
    OracleComp spec (RustM (Result Encoded)) :=
  match RegistrationBoundGate.gate control pin availability agreement application with
  | .ok (.Ok initial) => admitted initial
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Actual rejection makes no material query. On success, the complete native service equals its seed-free public continuation. -/
theorem gated_split (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (agreement : RegistrationBoundGate.PublicAgreement) (application : Slice U8) (message : Message) :
    simulateQ (erase (n := n)) (gated (fun initial => publicAdmitted encode control initial message)
      control pin availability agreement application) =
      gated (fun initial => privateAdmitted encode control initial message)
        control pin availability agreement application := by
  unfold gated
  cases RegistrationBoundGate.gate control pin availability agreement application with
  | fail error => simpa only using simulateQ_pure erase (.fail error : RustM (Result Encoded))
  | div => simpa only using simulateQ_pure erase (.div : RustM (Result Encoded))
  | ok result => cases result with
    | Err previous => simpa only using simulateQ_pure erase (.ok (.Err previous) : RustM (Result Encoded))
    | Ok initial => exact admitted_split encode control initial message

end BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerService.knownInstall_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerService.knownInstall_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerService.branch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerService.branch_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerService.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerService.common_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerService.admitted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerService.admitted_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedServerService.gated_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedServerService.gated_split
