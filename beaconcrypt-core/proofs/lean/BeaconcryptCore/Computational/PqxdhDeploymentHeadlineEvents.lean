-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain

/-!
# The public events of the CE-12 headlines (CE-12 P1, design-v2 sections 4.2-4.5)

The events and claims of the classical headlines on the deployment experiment's observation (`PqxdhDeploymentKemTransfer.Observed`: the adversary's output, the ledger with the transcript, the test session and the fresh messages, and the produced frames). They read the observation only, so they are public in the sense of plan section 9 (the hidden bit and the fresh messages are the experiment's own ledger values). Designation is the budgeted public designation `PqxdhDeploymentTranscript.designateIn` on the final transcript; a target is `g : Fin qAccept × Fin (qCreate + 1)` and `t_g = Target.ofCE budget g`.

- First-entry claims (`firstFrom`, `firstHandle`): the handle of the first transcript entry satisfying a predicate of the entry and its prefix (`firstHandle_some`, `firstHandle_isSome`).
- CE-OR (design-v2 section 4.2): `cpart` (the CE counterpart of a handle designated `g`: owner `k` for a Server peer, the target's Server peer for an owner), `ForgedAtCE` (an accepted raw receive in a direction on a handle designated `g` whose decoded frame no CE counterpart published before), `FailsAt`, `OriginFailure` and the claim `orClaim` (the receiving handle of the first failing entry).
- CE-UKS (design-v2 section 4.3): `CEPartners` (the designated partners of `g`), the receiver side `UksReceiverAt` (an accepted raw receive on a Server peer designated `g`, of a decoded frame that a handle other than its CE partner returned anywhere in the transcript; the CE form of b2s-UKSr) with `uksReceiverClaim`, and the sender side `UksSenderAt` (an owner designated `g` returned a frame that a handle other than its CE partner accepted) with `uksSenderClaim`.
- CE-APP (design-v2 section 4.4): `AppWin` (the adversary's claimed fresh message, sent on a designated handle, equals its guess), `AppWinPeer` (the same on a Server peer) and the claim `appHandle`.
- CE-LOR (design-v2 section 4.5): `LorElig` (a test session exists, a public filter `F` on the mode-P transcript view holds, the first admitted test entry's handle designates `g`, and every admitted test entry's handle designates `g`), `LorWin` (eligible and the guess equals the test bit), and the claim `PqxdhRecordLiftIdeal.firstTest`; `LorEligPeer` and `LorWinPeer` add that every admitted test handle is a Server peer.

Each event comes with its Boolean form (classical decision). No probability and no security claim is made here.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Handle Entry Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (peerOf)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore firstTest AdmittedTest)

variable {Reader Response X : Type}

/-! ### First-entry claims -/

section First

open Classical in
/-- The handle of the first entry of `rest` (with `before` already seen) that satisfies `P` on its prefix and has a handle. -/
noncomputable def firstFrom (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle) :
    List Entry → List Entry → Option Handle
  | _, [] => none
  | before, entry :: rest =>
      if P before entry ∧ (handleOf entry).isSome then handleOf entry else firstFrom P handleOf (before ++ [entry]) rest

/-- The handle of the first transcript entry that satisfies `P` on its prefix and has a handle. -/
noncomputable def firstHandle (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle)
    (transcript : List Entry) : Option Handle :=
  firstFrom P handleOf [] transcript

/-- A first-entry claim names an entry that satisfies the predicate on its prefix and has the claimed handle. -/
theorem firstFrom_some (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle) :
    ∀ (rest before : List Entry) (handle : Handle), firstFrom P handleOf before rest = some handle →
      ∃ pre entry post, rest = pre ++ entry :: post ∧ P (before ++ pre) entry ∧
        handleOf entry = some handle
  | [], _, _, found => by simp [firstFrom] at found
  | entry :: rest, before, handle, found => by
      classical
      unfold firstFrom at found
      split at found
      · rename_i holds
        exact ⟨[], entry, rest, rfl, by simpa using holds.1, found⟩
      · obtain ⟨pre, chosen, post, split, holds, named⟩ :=
          firstFrom_some P handleOf rest (before ++ [entry]) handle found
        refine ⟨entry :: pre, chosen, post, by rw [split]; rfl, ?_, named⟩
        simpa [List.append_assoc] using holds

/-- If some entry satisfies the predicate on its prefix and has a handle, the first-entry claim names a handle. -/
theorem firstFrom_isSome (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle) :
    ∀ (rest before pre : List Entry) (entry : Entry) (post : List Entry), rest = pre ++ entry :: post →
      P (before ++ pre) entry → (handleOf entry).isSome → (firstFrom P handleOf before rest).isSome
  | [], _, pre, _, _, split, _, _ => by cases pre <;> simp at split
  | first :: rest, before, pre, entry, post, split, holds, named => by
      classical
      unfold firstFrom
      split
      · rename_i found
        exact found.2
      · rename_i missed
        cases pre with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            obtain ⟨rfl, rfl⟩ := split
            exact absurd ⟨by simpa using holds, named⟩ missed
        | cons head pre =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, rfl⟩ := split
            exact firstFrom_isSome P handleOf _ (before ++ [first]) pre entry post rfl
              (by simpa [List.append_assoc] using holds) named

/-- `firstHandle` names an entry of the transcript that satisfies the predicate on its prefix and has the claimed handle. -/
theorem firstHandle_some (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle)
    (transcript : List Entry) (handle : Handle) (found : firstHandle P handleOf transcript = some handle) :
    ∃ before entry after, transcript = before ++ entry :: after ∧ P before entry ∧ handleOf entry = some handle := by
  simpa using firstFrom_some P handleOf transcript [] handle found

/-- If an entry of the transcript satisfies the predicate on its prefix and has a handle, `firstHandle` names a handle. -/
theorem firstHandle_isSome (P : List Entry → Entry → Prop) (handleOf : Entry → Option Handle)
    (transcript before : List Entry) (entry : Entry) (after : List Entry) (split : transcript = before ++ entry :: after)
    (holds : P before entry) (named : (handleOf entry).isSome) : (firstHandle P handleOf transcript).isSome :=
  firstFrom_isSome P handleOf transcript [] before entry after split (by simpa using holds) named

/-- The receiving handle of an entry's raw record attempt. -/
def receivedHandle (route : RawCtxServerRouting.SenderDecoder) (entry : Entry) : Option Handle :=
  entry.received.bind fun attempt => receivingHandle route attempt.1 attempt.2.1

/-- The handle on which an entry returned a record ciphertext. -/
def publishedHandle (entry : Entry) : Option Handle :=
  entry.published.map Prod.fst

end First

/-! ### CE-OR -/

section Origin
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The direction of an origin event: b2s when the receiving handle is a Server peer (a Server raw receive), s2b when it is a Beacon owner. -/
inductive Direction where
  | b2s
  | s2b
  deriving DecidableEq

/-- A handle receives in a direction: a Server peer for b2s, an owner for s2b. -/
def Direction.Receives : Direction → Handle → Prop
  | .b2s, .peer _ => True
  | .s2b, .owner _ => True
  | _, _ => False

/-- `cpart` (design-v2 section 4.2): the CE counterpart of a handle designated `g = (i, k)`: owner `k` for a Server peer, and the Server peer built by the target's session (`PqxdhDeploymentIdealTrace.peerOf`) for an owner. -/
def cpart (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) : Handle → Option Handle
  | .peer _ => some (.owner g.2.val)
  | .owner _ => (peerOf (Target.ofCE budget g) transcript).map .peer

/-- `ForgedAtCE` (design-v2 section 4.2): the entry, with pre `before` in the final transcript `transcript`, is an accepted raw receive in the direction on a handle designated `g`, whose decoded frame the CE counterpart did not publish before. -/
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

/-! ### CE-UKS -/

section Uks
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- `CEPartners` (design-v2 section 4.3): the two handles are the designated partners of `g = (i, k)`: owner `k` and the Server peer built by the target's session, in either order. -/
def CEPartners (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) (first second : Handle) : Prop :=
  (first = .owner g.2.val ∧ some second = (peerOf (Target.ofCE budget g) transcript).map .peer) ∨
    (second = .owner g.2.val ∧ some first = (peerOf (Target.ofCE budget g) transcript).map .peer)

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

/-! ### CE-APP -/

section App
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (appClaim : X → Option (Nat × Pqxdh.Bytes))

/-- `AppWin` (design-v2 section 4.4): the adversary's output claims index `i` and guess `m`, the `i`-th admitted fresh message was sent on a designated handle, and it equals the guess. -/
def AppWin (observed : Observed X) : Prop :=
  ∃ index guess entry, appClaim observed.1 = some (index, guess) ∧ observed.2.1.fresh[index]? = some entry ∧
    (designateIn crypto codec serverKid budget observed.2.1.transcript entry.handle).isSome ∧ entry.message = guess

/-- `AppWin` on a Server peer (design-v2 section 4.4, `ce_app_server`). -/
def AppWinPeer (observed : Observed X) : Prop :=
  ∃ index guess entry keyId, appClaim observed.1 = some (index, guess) ∧ observed.2.1.fresh[index]? = some entry ∧
    entry.handle = .peer keyId ∧
    (designateIn crypto codec serverKid budget observed.2.1.transcript entry.handle).isSome ∧ entry.message = guess

open Classical in
/-- The CE-APP event as a Boolean of the observation. -/
noncomputable def appEvent (observed : Observed X) : Bool :=
  decide (AppWin crypto codec serverKid budget appClaim observed)

open Classical in
/-- The Server-side CE-APP event as a Boolean of the observation. -/
noncomputable def appPeerEvent (observed : Observed X) : Bool :=
  decide (AppWinPeer crypto codec serverKid budget appClaim observed)

/-- `appHandle` (design-v2 section 4.4): the handle of the claimed fresh message. -/
def appHandle (observed : Observed X) : Option Handle :=
  (appClaim observed.1).bind fun claimed => (observed.2.1.fresh[claimed.1]?).map PqxdhDeploymentSecrecy.FreshEntry.handle

/-- A CE-APP win names a designated claim. -/
theorem app_named (observed : Observed X) (won : appEvent crypto codec serverKid budget appClaim observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget (appHandle appClaim) observed).isSome := by
  classical
  unfold appEvent at won
  obtain ⟨index, guess, entry, claimed, found, designated, _⟩ := of_decide_eq_true won
  simpa [PqxdhDeploymentKemTransfer.target, appHandle, claimed, found] using designated

/-- A Server-side CE-APP win names a designated claim. -/
theorem appPeer_named (observed : Observed X)
    (won : appPeerEvent crypto codec serverKid budget appClaim observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget (appHandle appClaim) observed).isSome := by
  classical
  unfold appPeerEvent at won
  obtain ⟨index, guess, entry, _, claimed, found, _, designated, _⟩ := of_decide_eq_true won
  simpa [PqxdhDeploymentKemTransfer.target, appHandle, claimed, found] using designated

end App

/-! ### CE-LOR -/

section Lor
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)

/-- `LorElig` (design-v2 section 4.5): a test session exists, the public filter holds on the mode-P transcript view, the first admitted test entry's handle designates `g`, and every admitted test entry's handle designates `g` (admission recomputed from the transcript pre, `PqxdhRecordLiftIdeal.AdmittedTest`). -/
def LorElig (g : Fin budget.accept × Fin budget.capacity) (observed : Observed X) : Prop :=
  observed.2.1.test.isSome ∧ filter (observed.2.1.transcript.map (Entry.view .P)) = true ∧
    (∃ first, firstTest observed.2.1.transcript = some first ∧
      designateIn crypto codec serverKid budget observed.2.1.transcript first = some g) ∧
    ∀ before entry after handle left right, observed.2.1.transcript = before ++ entry :: after →
      entry.query = .inr (.test handle left right) → AdmittedTest crypto codec serverKid before handle left right →
        designateIn crypto codec serverKid budget observed.2.1.transcript handle = some g

/-- `LorWin` (design-v2 section 4.5): eligible, and the adversary's guess equals the test bit. -/
def LorWin (g : Fin budget.accept × Fin budget.capacity) (observed : Observed X) : Prop :=
  LorElig crypto codec serverKid budget filter g observed ∧
    observed.2.1.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1)

/-- Every admitted test entry's handle is a Server peer (design-v2 section 4.5, `ce_lor_server`). -/
def PeerTests (observed : Observed X) : Prop :=
  ∀ before entry after handle left right, observed.2.1.transcript = before ++ entry :: after →
    entry.query = .inr (.test handle left right) → AdmittedTest crypto codec serverKid before handle left right →
      ∃ keyId, handle = .peer keyId

open Classical in
/-- The CE-LOR eligibility as a Boolean of the observation: eligible for some target. -/
noncomputable def lorEligEvent (observed : Observed X) : Bool :=
  decide (∃ g, LorElig crypto codec serverKid budget filter g observed)

open Classical in
/-- The CE-LOR win as a Boolean of the observation: winning for some target. -/
noncomputable def lorWinEvent (observed : Observed X) : Bool :=
  decide (∃ g, LorWin crypto codec serverKid budget guess filter g observed)

open Classical in
/-- The Server-side CE-LOR eligibility: eligible for some target with every admitted test on a Server peer. -/
noncomputable def lorEligPeerEvent (observed : Observed X) : Bool :=
  decide ((∃ g, LorElig crypto codec serverKid budget filter g observed) ∧ PeerTests crypto codec serverKid observed)

open Classical in
/-- The Server-side CE-LOR win: winning for some target with every admitted test on a Server peer. -/
noncomputable def lorWinPeerEvent (observed : Observed X) : Bool :=
  decide ((∃ g, LorWin crypto codec serverKid budget guess filter g observed) ∧
    PeerTests crypto codec serverKid observed)

/-- The CE-LOR claim: the handle of the first admitted test entry. -/
noncomputable def lorClaim (observed : Observed X) : Option Handle :=
  firstTest observed.2.1.transcript

/-- Eligibility is anchored on the first admitted test entry (design-v2 section 4.5): its target is the claim's designation, so the eligibility sets of distinct targets are disjoint. -/
theorem lorElig_target (g : Fin budget.accept × Fin budget.capacity) (observed : Observed X)
    (eligible : LorElig crypto codec serverKid budget filter g observed) :
    PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed = some g := by
  obtain ⟨_, _, ⟨first, found, designated⟩, _⟩ := eligible
  simp [PqxdhDeploymentKemTransfer.target, lorClaim, found, designated]

end Lor

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstFrom_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstFrom_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstFrom_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstFrom_isSome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstHandle_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstHandle_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstHandle_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.firstHandle_isSome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.origin_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.origin_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.uksReceiver_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.uksReceiver_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.uksSender_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.uksSender_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.app_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.app_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.appPeer_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.appPeer_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.lorElig_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents.lorElig_target
