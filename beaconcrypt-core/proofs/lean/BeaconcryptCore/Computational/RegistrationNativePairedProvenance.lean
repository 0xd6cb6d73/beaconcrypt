-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! An actual paired material continuation can install only its own role. Every hidden installation uses exactly the slot returned by that same material demand; known choices emit no hidden installation. These footprints hold on the full open publication, signing, encoding and Beacon opening ASTs, including all their failure continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedProvenance
open PqxdhRecordLiftInterface (Role Slot EnvEffects KernelRef)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeHiddenAllocationCore (simulation)
variable {n : Nat} {Value Encoded : Type}

def Kernel (choice : Choice n) : KernelRef n → Prop
  | .known _ => True
  | .hidden slot => ∃ reference, choice = .hidden reference ∧ slot = reference.slot

def Effect (role : Role) (choice : Choice n) : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ kernel) => role = .server ∧ Kernel choice kernel
  | .inr (.installBeacon _ _ kernel) => role = .beacon ∧ Kernel choice kernel
  | _ => True

def Allowed (role : Role) (choice : Choice n) : (Common n).Domain → Prop
  | .inl _ => True
  | .inr query => Effect role choice query

private theorem all_true {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem publication (role : Role) (choice : Choice n) (work : OracleComp RegistrationBoundPublication.Spec Value) :
    AllQueriesSatisfy (simulateQ RegistrationHiddenInstall.publicationLift work) (Allowed role choice) := by
  apply simulation _ (fun _ => True) _ _ work (all_true work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem raw (role : Role) (choice : Choice n) (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    AllQueriesSatisfy (simulateQ RegistrationNativePairedBeaconService.rawLift work) (Allowed role choice) := by
  apply simulation _ (fun _ => True) _ _ work (all_true work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem effects (role : Role) (choice : Choice n) (work : OracleComp (EnvEffects n) Value)
    (valid : AllQueriesSatisfy work (Effect role choice)) :
    AllQueriesSatisfy (simulateQ RegistrationHiddenInstall.effectLift work) (Allowed role choice) := by
  apply simulation _ _ _ _ work valid
  intro query allowed
  exact (allQueriesSatisfy_query_iff _ _).mpr allowed

private theorem server_known (choice : Choice n) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownInstall (n := n) control published) (Effect .server choice) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
            | ok parts =>
                simp only [RegistrationNativePairedServerService.knownInstall, prepared]
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (Effect .server choice)
                exact ⟨⟨rfl, trivial⟩, fun _ => trivial⟩

private theorem server_hidden (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationHiddenInstall.install control reference.slot published) (Effect .server (.hidden reference)) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationHiddenInstall.install, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
            | ok parts =>
                simp only [RegistrationHiddenInstall.install, prepared]
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.hidden reference.slot))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) (Effect .server (.hidden reference))
                exact ⟨⟨rfl, reference, rfl, rfl⟩, fun _ => trivial⟩

private theorem server_known_after (choice : Choice n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownAfter (n := n) control published) (Effect .server choice) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_known choice control published

private theorem server_hidden_after (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationHiddenInstall.after control reference.slot published) (Effect .server (.hidden reference)) := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_hidden reference control published

/-- The literal actual Server continuation uses the hidden slot returned by its own paired demand and cannot install the Beacon role. -/
theorem server_branch (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (choice : Choice n) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.publicBranch encode control initial choice) (Allowed .server choice) := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.knownStage]
      apply allQueriesSatisfy_bind (publication .server (.known output) _)
      intro published
      exact effects .server (.known output) _ (server_known_after (.known output) control published)
  | hidden reference =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.hiddenStage]
      apply allQueriesSatisfy_bind (publication .server (.hidden reference) _)
      intro published
      exact effects .server (.hidden reference) _ (server_hidden_after reference control published)

private theorem beacon_after (choice : Choice n) (owner : Nat) (sender : U64)
    (selectKernel : registration.CompletedBeacon → KernelRef n)
    (valid : ∀ completed, Kernel choice (selectKernel completed)) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.after owner sender selectKernel result) (Effect .beacon choice) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err aborted => trivial
    | Ok completed => exact ⟨⟨rfl, valid completed⟩, fun _ => trivial⟩

/-- The literal actual Beacon continuation uses the hidden slot returned by its own paired demand and cannot install the Server role. -/
theorem beacon_branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (choice : Choice n) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice) (Allowed .beacon choice) := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.knownStage]
      apply allQueriesSatisfy_bind (raw .beacon (.known output) _)
      intro result
      exact effects .beacon (.known output) _
        (beacon_after (.known output) owner sender (fun completed => .known completed.kernel) (fun _ => trivial) result)
  | hidden reference =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.hiddenStage,
        RegistrationNativePairedBeaconService.privateHiddenStage]
      apply allQueriesSatisfy_bind (raw .beacon (.hidden reference) _)
      intro result
      exact effects .beacon (.hidden reference) _
        (beacon_after (.hidden reference) owner sender (fun _ => .hidden reference.slot) (fun _ => ⟨reference, rfl, rfl⟩) result)

end BeaconcryptCore.Computational.RegistrationNativePairedProvenance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedProvenance.server_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedProvenance.server_branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedProvenance.beacon_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedProvenance.beacon_branch
