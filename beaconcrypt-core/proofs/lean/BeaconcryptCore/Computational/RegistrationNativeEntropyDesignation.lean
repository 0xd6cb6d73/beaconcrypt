-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyRestore
import BeaconcryptCore.Computational.RegistrationNativeEvents
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents

/-! Transport decoding leaves original CE designation and secrecy-session checks unchanged. This uses actual registration projections and counters, not a replacement eligibility predicate. The named native APP event transfers with its literal original fresh-message list and the complete private Mode O transcript. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation
open RegistrationNativeEntropyTrace (strip findSome_strip countP_strip summarize_strip)
open PqxdhDeploymentInterface (Entry Handle Budget)
open PqxdhServerAuthExperiment (Codec)
variable {Reader Response Value NativeState : Type}

/-- The first actual published bundle is unchanged by transport decoding. -/
theorem bundle_strip (transcript : List Entry) (owner : Nat) :
    PqxdhDeploymentTranscript.bundleOf (strip transcript) owner =
      PqxdhDeploymentTranscript.bundleOf transcript owner := by
  unfold PqxdhDeploymentTranscript.bundleOf
  apply findSome_strip
  intro key message reply
  rfl

/-- The original successful finish bytes are unchanged. -/
theorem finish_strip (transcript : List Entry) (owner : Nat) :
    PqxdhDeploymentTranscript.finishOf (strip transcript) owner =
      PqxdhDeploymentTranscript.finishOf transcript owner := by
  unfold PqxdhDeploymentTranscript.finishOf
  apply findSome_strip
  intro key message reply
  rfl

/-- Successful session lookup keeps the original accepted input bytes. -/
theorem accept_strip (transcript : List Entry) (session : Nat) :
    PqxdhDeploymentTranscript.acceptOf (strip transcript) session =
      PqxdhDeploymentTranscript.acceptOf transcript session := by
  unfold PqxdhDeploymentTranscript.acceptOf
  apply findSome_strip
  intro key message reply
  rfl

/-- Successful build lookup retains the complete original response. -/
theorem build_strip (transcript : List Entry) (session : Nat) :
    PqxdhDeploymentTranscript.buildOf (strip transcript) session =
      PqxdhDeploymentTranscript.buildOf transcript session := by
  unfold PqxdhDeploymentTranscript.buildOf
  apply findSome_strip
  intro key message reply
  rfl

/-- Peer-to-session links retain their exact public key identifier and full response. -/
theorem link_strip (transcript : List Entry) (keyId : U64) :
    PqxdhDeploymentTranscript.linkOf (strip transcript) keyId =
      PqxdhDeploymentTranscript.linkOf transcript keyId := by
  unfold PqxdhDeploymentTranscript.linkOf
  apply findSome_strip
  intro key message reply
  rfl

/-- Transport does not create accept attempts or change their original ordinal. -/
theorem acceptCount_strip (transcript : List Entry) :
    PqxdhDeploymentTranscript.acceptCount (strip transcript) =
      PqxdhDeploymentTranscript.acceptCount transcript := by
  unfold PqxdhDeploymentTranscript.acceptCount
  apply countP_strip
  intro key message reply
  rfl

/-- Broad original verified-key designation is unchanged for both protocol roles, including changed accepted packets. -/
theorem designate_strip (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (transcript : List Entry) :
    PqxdhDeploymentTranscript.designate crypto codec serverKid (strip transcript) =
      PqxdhDeploymentTranscript.designate crypto codec serverKid transcript := by
  classical
  have published : ∀ accepted pqKey owner,
      decide (PqxdhDeploymentTranscript.Publishes codec (strip transcript) accepted pqKey owner) =
        decide (PqxdhDeploymentTranscript.Publishes codec transcript accepted pqKey owner) := by
    intro accepted pqKey owner
    apply decide_eq_decide.mpr
    simp only [PqxdhDeploymentTranscript.Publishes, bundle_strip]
  have linked : ∀ ciphertext identity pqKey session,
      decide (PqxdhDeploymentTranscript.Linked crypto codec (strip transcript) ciphertext identity pqKey session) =
        decide (PqxdhDeploymentTranscript.Linked crypto codec transcript ciphertext identity pqKey session) := by
    intro ciphertext identity pqKey session
    apply decide_eq_decide.mpr
    simp only [PqxdhDeploymentTranscript.Linked, build_strip, accept_strip]
  funext handle
  cases handle <;> simp only [PqxdhDeploymentTranscript.designate, PqxdhDeploymentTranscript.phase,
    summarize_strip, bundle_strip, finish_strip, accept_strip, link_strip,
    acceptCount_strip, published, linked]
  all_goals rfl

/-- The same original finite accept/create target set is retained, with no additional record or target factor. -/
theorem designateIn_strip (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (budget : Budget) (transcript : List Entry) :
    PqxdhDeploymentTranscript.designateIn crypto codec serverKid budget (strip transcript) =
      PqxdhDeploymentTranscript.designateIn crypto codec serverKid budget transcript := by
  funext handle
  simp only [PqxdhDeploymentTranscript.designateIn, designate_strip]

/-- The literal original secrecy controller makes the same same-session decision after decoding transport. -/
theorem sameSession_strip (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (transcript : List Entry) (first second : Handle) :
    PqxdhDeploymentSecrecy.SameSession crypto codec serverKid (strip transcript) first second ↔
      PqxdhDeploymentSecrecy.SameSession crypto codec serverKid transcript first second := by
  simp only [PqxdhDeploymentSecrecy.SameSession, designate_strip]

/-- The actual broad native APP observation is exactly the original record experiment's APP observation on the transport transcript. -/
theorem app_event (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (value : Value)
    (before : PqxdhDeploymentSecrecy.Ledger) (native : NativeState)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    RegistrationNativeEvents.ceAppEvent crypto wire serverKid budget claim
        (value, (RegistrationNativeEntropyRestore.ledger before, native)) =
      PqxdhDeploymentHeadlineEvents.appEvent crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKid budget claim (value, before, produced) := by
  unfold RegistrationNativeEvents.ceAppEvent RegistrationNativeEvents.CEAppWin
    PqxdhDeploymentHeadlineEvents.appEvent PqxdhDeploymentHeadlineEvents.AppWin
  rw [RegistrationNativeEntropyRestore.ledger_transcript, designateIn_strip]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.bundle_strip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.bundle_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.finish_strip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.finish_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.accept_strip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.accept_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.build_strip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.build_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.link_strip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.link_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.acceptCount_strip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.acceptCount_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.designate_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.designate_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.designateIn_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.designateIn_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.sameSession_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.sameSession_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.app_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation.app_event
