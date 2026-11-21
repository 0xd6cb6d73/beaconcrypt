-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents
/-! Native public origin and binding use the successful session handle returned by designation. The all-raw-attempt ordinal remains a distinct hybrid selector; failed accepts never relabel an actual public partner. Legacy event definitions are retained separately. -/
open OracleComp OracleSpec ENNReal Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeSessionEvents
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Handle Entry Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (acceptOf buildOf designateIn)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction firstHandle receivedHandle publishedHandle firstHandle_isSome firstHandle_some)
variable {Reader Response X : Type}

/-- Public designation names the successful session itself, independently of failed accept-attempt ordinals. -/
def peerOfSession (transcript : List Entry) (session : Nat) : Option Std.U64 :=
  (buildOf transcript session).map (·.keyId)

section Origin
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

def cpart (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) : Handle → Option Handle
  | .peer _ => some (.owner g.2.val)
  | .owner _ => (peerOfSession transcript g.1.val).map .peer

/-- `ForgedAtCE` (design-v2 section 4.2): the entry, with prefix `before` in the final transcript `transcript`, is an accepted raw receive in the direction on a handle designated `g`, whose decoded frame the CE counterpart did not publish before. -/
def ForgedAtCE (direction : Direction) (g : Fin budget.accept × Fin budget.capacity)
    (transcript before : List Entry) (entry : Entry) : Prop :=
  ∃ receiver raw decrypted handle frame, entry.received = some (receiver, raw, .Some decrypted) ∧
    receivingHandle route receiver raw = some handle ∧ direction.Receives handle ∧
    designateIn crypto codec serverKid budget transcript handle = some g ∧ codec.frameRead raw = some frame ∧
    ∀ counterpart, cpart budget g transcript handle = some counterpart → ¬PublishedBefore codec before counterpart frame

/-- The entry fails origin in the direction for some target. -/
def FailsAt (direction : Direction) (transcript before : List Entry) (entry : Entry) : Prop :=
  ∃ g, ForgedAtCE crypto codec serverKid budget route direction g transcript before entry

/-- `OriginFailure` (design-v2 section 4.2): some entry of the final transcript fails origin in the direction. -/
def OriginFailure (direction : Direction) (observed : Observed X) : Prop :=
  ∃ before entry after, observed.2.1.transcript = before ++ entry :: after ∧
    FailsAt crypto codec serverKid budget route direction observed.2.1.transcript before entry

open Classical in
/-- The CE-OR event as a Boolean of the observation. -/
noncomputable def originEvent (direction : Direction) (observed : Observed X) : Bool :=
  decide (OriginFailure crypto codec serverKid budget route direction observed)

/-- `orClaim` (design-v2 section 4.2): the receiving handle of the first entry that fails origin in the direction. -/
noncomputable def orClaim (direction : Direction) (observed : Observed X) : Option Handle :=
  firstHandle (FailsAt crypto codec serverKid budget route direction observed.2.1.transcript) (receivedHandle route)
    observed.2.1.transcript

/-- An origin failure names a designated claim: the first failing entry's receiving handle designates a target. -/
theorem origin_named (direction : Direction) (observed : Observed X)
    (failed : originEvent crypto codec serverKid budget route direction observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (orClaim crypto codec serverKid budget route direction) observed).isSome := by
  classical
  unfold originEvent at failed
  obtain ⟨before, entry, after, split, g, witness⟩ := of_decide_eq_true failed
  obtain ⟨receiver, raw, decrypted, handle, frame, received, routed, _, designated, _, _⟩ := id witness
  have named : (receivedHandle route entry).isSome := by
    simp [receivedHandle, received, routed]
  obtain ⟨claimed, found⟩ := Option.isSome_iff_exists.mp (firstHandle_isSome
    (FailsAt crypto codec serverKid budget route direction observed.2.1.transcript) (receivedHandle route) _ before entry
    after split ⟨g, witness⟩ named)
  obtain ⟨before', entry', after', split', ⟨g', receiver', raw', decrypted', handle', frame', received', routed', _,
    designated', _, _⟩, handled⟩ := firstHandle_some
      (FailsAt crypto codec serverKid budget route direction observed.2.1.transcript) (receivedHandle route) _ claimed
      found
  simp only [receivedHandle, received', Option.bind_some, routed', Option.some.injEq] at handled
  subst handled
  unfold PqxdhDeploymentKemTransfer.target orClaim
  rw [found]
  simp [designated']

end Origin

section Uks
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- `CEPartners` (design-v2 section 4.3): the two handles are the designated partners of `g = (i, k)`: owner `k` and the Server peer built by the target's session, in either order. -/
def CEPartners (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) (first second : Handle) : Prop :=
  (first = .owner g.2.val ∧ some second = (peerOfSession transcript g.1.val).map .peer) ∨
    (second = .owner g.2.val ∧ some first = (peerOfSession transcript g.1.val).map .peer)

/-- The receiver side of CE-UKS (design-v2 section 4.3, side `.recv`, the CE form of b2s-UKSr): the entry is an accepted raw receive on a Server peer designated `g`, of a decoded frame that some handle returned anywhere in the final transcript, and the two handles are not the CE partners of `g`. -/
def UksReceiverAt (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) (entry : Entry) : Prop :=
  ∃ receiver raw decrypted keyId sender frame, entry.received = some (receiver, raw, .Some decrypted) ∧
    receivingHandle route receiver raw = some (.peer keyId) ∧ codec.frameRead raw = some frame ∧
    PublishedBefore codec transcript sender frame ∧
    designateIn crypto codec serverKid budget transcript (.peer keyId) = some g ∧
    ¬CEPartners budget g transcript (.peer keyId) sender

/-- The receiver-side UKS failure: some entry of the final transcript is a receiver-side UKS witness for some target. -/
def UksReceiverFailure (observed : Observed X) : Prop :=
  ∃ entry ∈ observed.2.1.transcript, ∃ g, UksReceiverAt crypto codec serverKid budget route g observed.2.1.transcript entry

open Classical in
/-- The receiver-side CE-UKS event as a Boolean of the observation. -/
noncomputable def uksReceiverEvent (observed : Observed X) : Bool :=
  decide (UksReceiverFailure crypto codec serverKid budget route observed)

/-- The receiver-side claim: the receiving handle of the first receiver-side witness entry. -/
noncomputable def uksReceiverClaim (observed : Observed X) : Option Handle :=
  firstHandle (fun _ entry => ∃ g, UksReceiverAt crypto codec serverKid budget route g observed.2.1.transcript entry)
    (receivedHandle route) observed.2.1.transcript

/-- The sender side of CE-UKS (design-v2 section 4.3, side `.send`): the entry returned, on an owner designated `g`, a record whose decoded frame some raw receive of the final transcript accepted on a handle that is not the owner's CE partner. -/
def UksSenderAt (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) (entry : Entry) : Prop :=
  ∃ owner encrypted frame, entry.published = some (.owner owner, encrypted) ∧
    codec.frameRead encrypted.ciphertext = some frame ∧
    designateIn crypto codec serverKid budget transcript (.owner owner) = some g ∧
    ∃ other ∈ transcript, ∃ receiver raw decrypted receiving, other.received = some (receiver, raw, .Some decrypted) ∧
      receivingHandle route receiver raw = some receiving ∧ codec.frameRead raw = some frame ∧
      ¬CEPartners budget g transcript receiving (.owner owner)

/-- The sender-side UKS failure: some entry of the final transcript is a sender-side UKS witness for some target. -/
def UksSenderFailure (observed : Observed X) : Prop :=
  ∃ entry ∈ observed.2.1.transcript, ∃ g, UksSenderAt crypto codec serverKid budget route g observed.2.1.transcript entry

open Classical in
/-- The sender-side CE-UKS event as a Boolean of the observation. -/
noncomputable def uksSenderEvent (observed : Observed X) : Bool :=
  decide (UksSenderFailure crypto codec serverKid budget route observed)

/-- The sender-side claim: the sending handle of the first sender-side witness entry. -/
noncomputable def uksSenderClaim (observed : Observed X) : Option Handle :=
  firstHandle (fun _ entry => ∃ g, UksSenderAt crypto codec serverKid budget route g observed.2.1.transcript entry)
    publishedHandle observed.2.1.transcript

/-- A receiver-side UKS failure names a designated claim. -/
theorem uksReceiver_named (observed : Observed X)
    (failed : uksReceiverEvent crypto codec serverKid budget route observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (uksReceiverClaim crypto codec serverKid budget route) observed).isSome := by
  classical
  unfold uksReceiverEvent at failed
  obtain ⟨entry, member, g, witness⟩ := of_decide_eq_true failed
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨receiver, raw, _, _, _, _, received, routed, _, _, _, _⟩ := id witness
  have named : (receivedHandle route entry).isSome := by
    simp [receivedHandle, received, routed]
  obtain ⟨claimed, found⟩ := Option.isSome_iff_exists.mp (firstHandle_isSome
    (fun _ entry => ∃ g, UksReceiverAt crypto codec serverKid budget route g observed.2.1.transcript entry)
    (receivedHandle route) _ before entry after split ⟨g, witness⟩ named)
  obtain ⟨_, chosen, _, _, ⟨g', receiver', raw', decrypted', keyId', sender', frame', received', routed', _, _,
    designated', _⟩, handled⟩ := firstHandle_some _ (receivedHandle route) _ claimed found
  simp only [receivedHandle, received', Option.bind_some, routed', Option.some.injEq] at handled
  subst handled
  unfold PqxdhDeploymentKemTransfer.target uksReceiverClaim
  rw [found]
  simp [designated']

/-- A sender-side UKS failure names a designated claim. -/
theorem uksSender_named (observed : Observed X)
    (failed : uksSenderEvent crypto codec serverKid budget route observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (uksSenderClaim crypto codec serverKid budget route) observed).isSome := by
  classical
  unfold uksSenderEvent at failed
  obtain ⟨entry, member, g, witness⟩ := of_decide_eq_true failed
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨owner, encrypted, _, published, _, _, _⟩ := id witness
  have named : (publishedHandle entry).isSome := by
    simp [publishedHandle, published]
  obtain ⟨claimed, found⟩ := Option.isSome_iff_exists.mp (firstHandle_isSome
    (fun _ entry => ∃ g, UksSenderAt crypto codec serverKid budget route g observed.2.1.transcript entry)
    publishedHandle _ before entry after split ⟨g, witness⟩ named)
  obtain ⟨_, chosen, _, _, ⟨g', owner', encrypted', frame', published', _, designated', _⟩, handled⟩ :=
    firstHandle_some _ publishedHandle _ claimed found
  simp only [publishedHandle, published', Option.map_some, Option.some.injEq] at handled
  subst handled
  unfold PqxdhDeploymentKemTransfer.target uksSenderClaim
  rw [found]
  simp [designated']

end Uks

/-- Where a legacy raw-attempt coordinate happens to equal its successful session handle, the public partner lookups agree exactly. -/
theorem peer_compat (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry)
    (same : PqxdhDeploymentIdealTrace.sessionAt transcript g.1.val=some g.1.val) :
    PqxdhDeploymentIdealTrace.peerOf (Target.ofCE budget g) transcript=peerOfSession transcript g.1.val := by
  simp only [PqxdhDeploymentIdealTrace.peerOf,Target.ofCE,same,Option.bind_some,peerOfSession]

/-- The legacy counterpart is recovered on the explicit coordinate-alignment domain only. -/
theorem counterpart_compat (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry)
    (same : PqxdhDeploymentIdealTrace.sessionAt transcript g.1.val=some g.1.val) :
    cpart budget g transcript=PqxdhDeploymentHeadlineEvents.cpart budget g transcript := by
  funext handle
  cases handle with
  | peer keyId=>rfl
  | owner index=>simp only [cpart,PqxdhDeploymentHeadlineEvents.cpart,peer_compat budget g transcript same]

/-- The legacy partnership relation is recovered when its raw-attempt selector names the designated successful session. -/
theorem partners_compat (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry)
    (same : PqxdhDeploymentIdealTrace.sessionAt transcript g.1.val=some g.1.val) (first second : Handle) :
    CEPartners budget g transcript first second ↔ PqxdhDeploymentHeadlineEvents.CEPartners budget g transcript first second := by
  simp only [CEPartners,PqxdhDeploymentHeadlineEvents.CEPartners,peer_compat budget g transcript same]

def shifted (bad good : Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response) : List Entry :=
  [⟨.inl (.inr (.accept bad)),none⟩,⟨.inl (.inr (.accept good)),some 0⟩,
   ⟨.inl (.inr (.build 0 none)),some response⟩]

/-- Failed accepts shift raw ordinals without changing successful session handles or their actual built peer. This is a pure transcript witness, not a supplied initialized source run. -/
theorem shifted_lookup (bad good : Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response) :
    acceptOf (shifted bad good response) 0=some good ∧ buildOf (shifted bad good response) 0=some response ∧
      peerOfSession (shifted bad good response) 0=some response.keyId ∧
      PqxdhDeploymentIdealTrace.sessionAt (shifted bad good response) 0=none := by
  simp [shifted,acceptOf,buildOf,peerOfSession,PqxdhDeploymentIdealTrace.sessionAt,PqxdhDeploymentIdealTrace.acceptReplies]

/-- The corrected public partners retain the genuine built peer after a failed accept, while the legacy ordinal lookup rejects it. -/
theorem shifted_partners (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (zero : g.1.val=0)
    (bad good : Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response) :
    CEPartners budget g (shifted bad good response) (.owner g.2.val) (.peer response.keyId) ∧
      ¬PqxdhDeploymentHeadlineEvents.CEPartners budget g (shifted bad good response) (.owner g.2.val) (.peer response.keyId) := by
  simp [CEPartners,peerOfSession,PqxdhDeploymentHeadlineEvents.CEPartners,PqxdhDeploymentIdealTrace.peerOf,
    Target.ofCE,zero,PqxdhDeploymentIdealTrace.sessionAt,PqxdhDeploymentIdealTrace.acceptReplies,shifted,buildOf]

end BeaconcryptCore.Computational.RegistrationNativeSessionEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.origin_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.origin_named

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.uksReceiver_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.uksReceiver_named

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.uksSender_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.uksSender_named

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.peer_compat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.peer_compat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.counterpart_compat' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.counterpart_compat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.partners_compat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.partners_compat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.shifted_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.shifted_lookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionEvents.shifted_partners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionEvents.shifted_partners
