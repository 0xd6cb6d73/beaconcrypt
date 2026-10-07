-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentInterface
import BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures

/-! Public functions of the transcript of the common deployment experiment (CE-1). Every function here reads only transcript entries, that is, adversary queries with their replies; none reads a secret, a root, a partner or a native ghost. `summarize` folds the transcript into the created owner bindings in creation order, the public lifecycle phase of every owner handle (Fresh after a successful create, InitSent after a successful bundle in Fresh, Established after a successful finish in InitSent, Aborted after a rejected finish in InitSent, unchanged otherwise) and the owners with a rejected bundle call in Fresh. `owner k` is the handle created `k`-th. `NoBundleFailure` says that no bundle call made in Fresh was rejected. `designate` maps a record handle to at most one target `(session, KEM creation index)` by comparing keys, not signed fields: a Server peer goes to the session whose build returned its key ID and the smallest owner whose published bundle carries the accepted identity field and, in its PQ field, the PQ key that the source attached verification of the accept bytes yields; an established Beacon pinned to the protected key ID goes to the smallest session whose build response carries its finish ciphertext and its pin as Server identity and whose accept bytes verify to the PQ key read from the Beacon's published bundle. Codec readers, the raw candidate of `PqxdhRegistrationJointRawSignatures`, the public attached verification of `Pqxdh.Crypto` and the PQ-message parser are applied to public bytes only; the published PQ key is read without a signature check. Because keys are compared, an accept that carries an honest owner's identity and published PQ key under a different valid signature is designated like the owner's own bytes (`designate_peer_complete`, `designate_owner_complete`). The transcript stores mode O replies, but every function here reads only queries and the replies of create, bundle, accept, build and finish commands, never a raw-receive reply, so each depends only on the mode P view of the transcript (`summarize_view`, `phase_view`, `designate_view`) and is public in mode P as well. That these public functions agree with the native state is a separate obligation (CE-5); no security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentTranscript
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (Entry Handle Command Query FullSpec Budget parsePin)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple Ed25519PublicKey splitAttachedSignature parsePqMessage)
variable {Reader Response : Type}

/-- The public lifecycle phase of an owner handle. -/
inductive PublicPhase where
  | absent
  | fresh
  | initSent
  | established
  | aborted
  deriving DecidableEq

/-- The public summary of a transcript: the pin and key ID of every created owner in creation order, the public phase of every owner handle, and the owner handles with a rejected bundle call made in Fresh. -/
structure Summary where
  owners : List (Word32 × Std.U64)
  phases : Nat → PublicPhase
  failures : Nat → Bool

/-- The summary of the empty transcript. -/
def Summary.empty : Summary := ⟨[], fun _ => .absent, fun _ => false⟩

/-- Update the summary with one command and its reply. -/
def stepCommand (summary : Summary) : (command : Command) → PqxdhDeploymentInterface.CommandSpec command → Summary
  | .create pin keyId, some index =>
      match parsePin pin with
      | some word =>
          { summary with
            owners := summary.owners ++ [(word, keyId)]
            phases := Function.update summary.phases index .fresh }
      | none => summary
  | .create _ _, none => summary
  | .bundle owner, some _ =>
      if summary.phases owner = .fresh then { summary with phases := Function.update summary.phases owner .initSent }
      else summary
  | .bundle owner, none =>
      if summary.phases owner = .fresh then { summary with failures := Function.update summary.failures owner true }
      else summary
  | .finish owner _, some _ =>
      if summary.phases owner = .initSent then
        { summary with phases := Function.update summary.phases owner .established }
      else summary
  | .finish owner _, none =>
      if summary.phases owner = .initSent then { summary with phases := Function.update summary.phases owner .aborted }
      else summary
  | .accept _, _ => summary
  | .build _ _, _ => summary
  | .hmac _ _, _ => summary
  | .hash _, _ => summary
  | .serverSend _ _, _ => summary
  | .serverRaw _, _ => summary
  | .beaconSend _ _, _ => summary
  | .beaconRaw _ _, _ => summary

/-- Update the summary with one transcript entry: only commands change it, and only create, bundle and finish. -/
def step (summary : Summary) (entry : Entry) : Summary :=
  match entry with
  | ⟨.inl (.inr command), reply⟩ => stepCommand summary command reply
  | ⟨.inl (.inl _), _⟩ => summary
  | ⟨.inr _, _⟩ => summary

/-- The summary of a transcript, oldest entry first. -/
def summarize (transcript : List Entry) : Summary := transcript.foldl step Summary.empty

/-- The public phase of an owner handle. -/
def phase (transcript : List Entry) (owner : Nat) : PublicPhase := (summarize transcript).phases owner

/-- The handle created `k`-th, that is, the owner whose `create` drew KEM creation index `k`. -/
def owner (transcript : List Entry) (k : Nat) : Option Nat :=
  if k < (summarize transcript).owners.length then some k else none

/-- No bundle call on this owner made while it was Fresh was rejected. -/
def NoBundleFailureAt (transcript : List Entry) (owner : Nat) : Prop := (summarize transcript).failures owner = false

/-- No bundle call made in Fresh was rejected, for any owner. -/
def NoBundleFailure (transcript : List Entry) : Prop := ∀ owner, NoBundleFailureAt transcript owner

/-- The bytes of the first successful bundle of an owner. -/
def bundleOf (transcript : List Entry) (owner : Nat) : Option Pqxdh.Bytes :=
  transcript.findSome? fun entry => match entry with
    | ⟨.inl (.inr (.bundle index)), some bytes⟩ => if index = owner then some bytes else none
    | _ => none

/-- The input of the first successful finish of an owner. -/
def finishOf (transcript : List Entry) (owner : Nat) : Option Pqxdh.Bytes :=
  transcript.findSome? fun entry => match entry with
    | ⟨.inl (.inr (.finish index raw)), some _⟩ => if index = owner then some raw else none
    | _ => none

/-- The raw bytes of the accept that returned a session handle. -/
def acceptOf (transcript : List Entry) (session : Nat) : Option Pqxdh.Bytes :=
  transcript.findSome? fun entry => match entry with
    | ⟨.inl (.inr (.accept raw)), some handle⟩ => if handle = session then some raw else none
    | _ => none

/-- The response of the first successful build of a session handle. -/
def buildOf (transcript : List Entry) (session : Nat) : Option PqxdhServerRegistrationPublication.Response :=
  transcript.findSome? fun entry => match entry with
    | ⟨.inl (.inr (.build index _)), some response⟩ => if index = session then some response else none
    | _ => none

/-- The session and response of the first successful build that returned a key ID. -/
def linkOf (transcript : List Entry) (keyId : Std.U64) : Option (Nat × PqxdhServerRegistrationPublication.Response) :=
  transcript.findSome? fun entry => match entry with
    | ⟨.inl (.inr (.build session _)), some response⟩ =>
        if response.keyId = keyId then some (session, response) else none
    | _ => none

/-- The number of accept attempts, which bounds every session handle. -/
def acceptCount (transcript : List Entry) : Nat :=
  transcript.countP fun entry => match entry.query with
    | .inl (.inr (.accept _)) => true
    | _ => false

/-- The raw Phase 1 candidate read from public bytes. -/
def candidateOf (codec : Codec Reader Response) (bytes : Pqxdh.Bytes) : Option Phase1Candidate :=
  PqxdhRegistrationJointRawSignatures.candidate codec bytes

/-- The identity key and key tuple of a raw Phase 1 candidate under the source attached verification and parsing of `crypto` (`PqxdhJointPhase1Reports.sourceAccept`): the parsed identity key and the prekey, one-time and PQ keys parsed from the three verified messages. Whenever the native verification prefix `RawSignatures.verified` succeeds on accept bytes, this yields its identity and keys (`RawSignatures.verified_origin`). Only public bytes and the public verification function are used. -/
def acceptedKeys (crypto : Pqxdh.Crypto) (candidate : Phase1Candidate) : Option (Ed25519PublicKey × Phase1KeyTuple) :=
  PqxdhJointPhase1Reports.sourceAccept (fun publicKey => crypto.verify publicKey.toList) candidate

/-- The PQ key a published Phase 1 candidate carries: the message of its attached PQ field, parsed as a PQ message. No signature is checked. -/
def publishedPq (candidate : Phase1Candidate) : Option PqxdhKemIndCca.MlKem768PublicKey :=
  (splitAttachedSignature candidate.pqKey).bind fun split => parsePqMessage split.2

/-- Owner `k` published a bundle carrying the identity field of an accepted candidate and, in its PQ field, the PQ key `pqKey`. -/
def Publishes (codec : Codec Reader Response) (transcript : List Entry) (accepted : Phase1Candidate)
    (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (k : Nat) : Prop :=
  ∃ published, (bundleOf transcript k).bind (candidateOf codec) = some published ∧
    published.identityKey = accepted.identityKey ∧ publishedPq published = some pqKey

/-- Session `session` is linked to an established owner: its build response carries the owner's finish ciphertext and the owner's pin as Server identity, and its accept bytes verify to the owner's published PQ key `pqKey`. -/
def Linked (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry) (ciphertext : Ciphertext)
    (pin : Word32) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat) : Prop :=
  ∃ response accepted keys, buildOf transcript session = some response ∧
    (codec.read2 response.serialized).bind codec.ciphertext = some ciphertext ∧
    (codec.read2 response.serialized).bind codec.serverIdentity = some pin ∧
    (acceptOf transcript session).bind (candidateOf codec) = some accepted ∧
    acceptedKeys crypto accepted = some keys ∧ keys.2.pqKey = pqKey

open Classical in
/-- Target designation of a record handle. A Server peer `keyId` designates `(i, k)` when session `i` built it, its accept bytes give candidate `c` that verifies to keys `v`, and `k` is the smallest created owner whose published bundle carries `c`'s identity field and the PQ key of `v`. An owner `c` designates `(i, c)` when it is Established, its key ID is the protected `serverKid`, its finish input gives a ciphertext, its bundle gives a published PQ key, and `i` is the smallest session handle linked to it. Everything else is ineligible. -/
noncomputable def designate (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (transcript : List Entry) : Handle → Option (Nat × Nat)
  | .peer keyId => do
      let link ← linkOf transcript keyId
      let raw ← acceptOf transcript link.1
      let accepted ← candidateOf codec raw
      let keys ← acceptedKeys crypto accepted
      let k ← (List.range (summarize transcript).owners.length).find? fun k =>
        decide (Publishes codec transcript accepted keys.2.pqKey k)
      pure (link.1, k)
  | .owner index =>
      if phase transcript index = .established then do
        let binding ← (summarize transcript).owners[index]?
        if binding.2 = serverKid then do
          let raw ← finishOf transcript index
          let ciphertext ← (codec.read2 raw).bind codec.ciphertext
          let published ← (bundleOf transcript index).bind (candidateOf codec)
          let pqKey ← publishedPq published
          let session ← (List.range (acceptCount transcript)).find? fun session =>
            decide (Linked crypto codec transcript ciphertext binding.1 pqKey session)
          pure (session, index)
        else none
      else none

/-- Designation into the finite target domain of a budget: `none` for an ineligible handle or a pair outside `Fin qAccept × Fin (count + 1)`. -/
noncomputable def designateIn (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (budget : Budget) (transcript : List Entry) (handle : Handle) : Option (Fin budget.accept × Fin budget.capacity) :=
  (designate crypto codec serverKid transcript handle).bind fun target =>
    if first : target.1 < budget.accept then
      if second : target.2 < budget.capacity then some (⟨target.1, first⟩, ⟨target.2, second⟩) else none
    else none

/-- The summary is computed entry by entry. -/
theorem summarize_append (transcript : List Entry) (entry : Entry) :
    summarize (transcript ++ [entry]) = step (summarize transcript) entry := by
  simp only [summarize, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- An entry that is not a create, bundle or finish command leaves the summary unchanged. -/
theorem step_other (summary : Summary) (entry : Entry)
    (other : ∀ pin keyId reply, entry ≠ ⟨.inl (.inr (.create pin keyId)), reply⟩)
    (notBundle : ∀ owner reply, entry ≠ ⟨.inl (.inr (.bundle owner)), reply⟩)
    (notFinish : ∀ owner raw reply, entry ≠ ⟨.inl (.inr (.finish owner raw)), reply⟩) :
    step summary entry = summary := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | create pin keyId => exact absurd rfl (other pin keyId reply)
    | bundle owner => exact absurd rfl (notBundle owner reply)
    | finish owner raw => exact absurd rfl (notFinish owner raw reply)
    | _ => rfl
  · rfl

/-- A designated Server peer was built by the designated session, whose accept bytes give a candidate that verifies to a key tuple whose PQ key owner `k`, created before the end of the transcript, published together with the candidate's identity field. -/
theorem designate_peer (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid keyId : Std.U64)
    (transcript : List Entry) (session k : Nat)
    (designated : designate crypto codec serverKid transcript (.peer keyId) = some (session, k)) :
    ∃ response raw accepted keys, linkOf transcript keyId = some (session, response) ∧
      acceptOf transcript session = some raw ∧ candidateOf codec raw = some accepted ∧
      acceptedKeys crypto accepted = some keys ∧ k < (summarize transcript).owners.length ∧
      Publishes codec transcript accepted keys.2.pqKey k := by
  simp only [designate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at designated
  obtain ⟨⟨linked, response⟩, linkFound, raw, rawFound, accepted, acceptedFound, keys, keysFound, chosen, chosenFound,
    same⟩ := designated
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have member := List.mem_of_find?_eq_some chosenFound
  have holds := List.find?_some chosenFound
  simp only [decide_eq_true_eq] at holds
  exact ⟨response, raw, accepted, keys, linkFound, rawFound, acceptedFound, keysFound, List.mem_range.mp member, holds⟩

/-- A designated owner is Established, pinned to the protected key ID, designates its own creation index, and the designated session is a linked accept attempt. -/
theorem designate_owner (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (transcript : List Entry) (index session k : Nat)
    (designated : designate crypto codec serverKid transcript (.owner index) = some (session, k)) :
    k = index ∧ phase transcript index = .established ∧
      ∃ pin raw ciphertext published pqKey, (summarize transcript).owners[index]? = some (pin, serverKid) ∧
        finishOf transcript index = some raw ∧ (codec.read2 raw).bind codec.ciphertext = some ciphertext ∧
        (bundleOf transcript index).bind (candidateOf codec) = some published ∧ publishedPq published = some pqKey ∧
        session < acceptCount transcript ∧ Linked crypto codec transcript ciphertext pin pqKey session := by
  by_cases established : phase transcript index = .established
  · simp only [designate, established, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at designated
    obtain ⟨⟨pin, kid⟩, bindingFound, designated⟩ := designated
    by_cases pinned : kid = serverKid
    · simp only [pinned, ite_true, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at designated
      obtain ⟨raw, rawFound, ciphertext, ciphertextFound, published, publishedFound, pqKey, pqKeyFound, chosen,
        chosenFound, rfl, rfl⟩ := designated
      have member := List.mem_of_find?_eq_some chosenFound
      have holds := List.find?_some chosenFound
      simp only [decide_eq_true_eq] at holds
      subst pinned
      exact ⟨rfl, established, pin, raw, ciphertext, published, pqKey, bindingFound, rawFound,
        Option.bind_eq_some_iff.mpr ciphertextFound, Option.bind_eq_some_iff.mpr publishedFound, pqKeyFound,
        List.mem_range.mp member, holds⟩
    · simp only [pinned, ite_false, reduceCtorEq] at designated
  · simp only [designate, established, ite_false, reduceCtorEq] at designated

/-- Completeness on the Server side: a Server peer is designated whenever the session that built it has accept bytes whose candidate verifies to keys whose PQ key some created owner published together with the candidate's identity field. The designation then names that session and the smallest such owner. -/
theorem designate_peer_complete (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid keyId : Std.U64)
    (transcript : List Entry) (session : Nat) (response : PqxdhServerRegistrationPublication.Response) (raw : Pqxdh.Bytes)
    (accepted : Phase1Candidate) (keys : Ed25519PublicKey × Phase1KeyTuple) (k : Nat)
    (linked : linkOf transcript keyId = some (session, response)) (rawFound : acceptOf transcript session = some raw)
    (candidateFound : candidateOf codec raw = some accepted) (keysFound : acceptedKeys crypto accepted = some keys)
    (created : k < (summarize transcript).owners.length) (publishes : Publishes codec transcript accepted keys.2.pqKey k) :
    ∃ first, first ≤ k ∧ designate crypto codec serverKid transcript (.peer keyId) = some (session, first) := by
  classical
  have found : ((List.range (summarize transcript).owners.length).find? fun k =>
      decide (Publishes codec transcript accepted keys.2.pqKey k)).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.mpr created, decide_eq_true publishes⟩
  obtain ⟨first, firstFound⟩ := Option.isSome_iff_exists.mp found
  refine ⟨first, ?_, ?_⟩
  · obtain ⟨_, _, minimal⟩ := List.find?_range_eq_some.mp firstFound
    by_contra later
    have rejected := minimal k (Nat.lt_of_not_le later)
    simp [publishes] at rejected
  · simp only [designate, linked, rawFound, candidateFound, keysFound, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
    rw [firstFound]
    rfl

/-- Completeness on the Beacon side: an Established owner pinned to the protected key ID, with a finish ciphertext and a published PQ key, is designated whenever some accept attempt is linked to it. The designation then names the smallest such session and the owner's own creation index. -/
theorem designate_owner_complete (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (transcript : List Entry) (index : Nat) (pin : Word32) (raw : Pqxdh.Bytes) (ciphertext : Ciphertext)
    (published : Phase1Candidate) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat)
    (established : phase transcript index = .established)
    (binding : (summarize transcript).owners[index]? = some (pin, serverKid))
    (rawFound : finishOf transcript index = some raw)
    (ciphertextFound : (codec.read2 raw).bind codec.ciphertext = some ciphertext)
    (publishedFound : (bundleOf transcript index).bind (candidateOf codec) = some published)
    (pqKeyFound : publishedPq published = some pqKey) (bounded : session < acceptCount transcript)
    (linked : Linked crypto codec transcript ciphertext pin pqKey session) :
    ∃ first, first ≤ session ∧ designate crypto codec serverKid transcript (.owner index) = some (first, index) := by
  classical
  have found : ((List.range (acceptCount transcript)).find? fun session =>
      decide (Linked crypto codec transcript ciphertext pin pqKey session)).isSome := by
    rw [List.find?_isSome]
    exact ⟨session, List.mem_range.mpr bounded, decide_eq_true linked⟩
  obtain ⟨first, firstFound⟩ := Option.isSome_iff_exists.mp found
  refine ⟨first, ?_, ?_⟩
  · obtain ⟨_, _, minimal⟩ := List.find?_range_eq_some.mp firstFound
    by_contra later
    have rejected := minimal session (Nat.lt_of_not_le later)
    simp [linked] at rejected
  · simp only [designate, established, binding, rawFound, ciphertextFound, publishedFound, pqKeyFound, ite_true,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [firstFound]
    rfl

/-- Two transcripts with the same mode P view: the same queries in the same order, with the same replies except that a raw receive is seen only through its success bit. -/
def SameView (first second : List Entry) : Prop :=
  first.map (Entry.view .P) = second.map (Entry.view .P)

/-- A function of transcript entries that ignores the replies of raw receives takes equal values on entries with the same mode P view. -/
theorem view_respects {β : Type} (f : Entry → β)
    (serverRaw : ∀ raw reply reply', f ⟨.inl (.inr (.serverRaw raw)), reply⟩ = f ⟨.inl (.inr (.serverRaw raw)), reply'⟩)
    (beaconRaw : ∀ owner raw reply reply',
      f ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩ = f ⟨.inl (.inr (.beaconRaw owner raw)), reply'⟩)
    (first second : Entry) (same : first.view .P = second.view .P) : f first = f second := by
  rcases first with ⟨query, reply⟩
  rcases second with ⟨query', reply'⟩
  simp only [Entry.view, PqxdhDeploymentInterface.PublicEntry.mk.injEq] at same
  obtain ⟨rfl, same⟩ := same
  have replies := eq_of_heq same
  rcases query with (coin | command) | secrecy
  · have equal : reply = reply' := replies
    rw [equal]
  · cases command with
    | serverRaw raw => exact serverRaw raw reply reply'
    | beaconRaw owner raw => exact beaconRaw owner raw reply reply'
    | _ =>
        have equal : reply = reply' := replies
        rw [equal]
  · have equal : reply = reply' := replies
    rw [equal]

/-- A search over transcript entries by a function that ignores raw-receive replies depends only on the mode P view. -/
theorem findSome_view {β : Type} (f : Entry → Option β) (respects : ∀ first second : Entry,
    first.view .P = second.view .P → f first = f second) :
    ∀ first second : List Entry, SameView first second → first.findSome? f = second.findSome? f
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [SameView] at same
  | _ :: _, [], same => by simp [SameView] at same
  | entry :: rest, other :: rest', same => by
      simp only [SameView, List.map_cons, List.cons.injEq] at same
      simp only [List.findSome?_cons, respects entry other same.1, findSome_view f respects rest rest' same.2]

/-- The transcript summary depends only on the mode P view. -/
theorem summarize_view (first second : List Entry) (same : SameView first second) :
    summarize first = summarize second := by
  have fold : ∀ (first second : List Entry), SameView first second → ∀ summary : Summary,
      first.foldl step summary = second.foldl step summary := by
    intro first
    induction first with
    | nil =>
        intro second same summary
        cases second with
        | nil => rfl
        | cons _ _ => simp [SameView] at same
    | cons entry rest ih =>
        intro second same summary
        cases second with
        | nil => simp [SameView] at same
        | cons other rest' =>
            simp only [SameView, List.map_cons, List.cons.injEq] at same
            simp only [List.foldl_cons]
            rw [view_respects (step summary) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) entry other same.1]
            exact ih rest' same.2 _
  exact fold first second same Summary.empty

/-- The public phase, the owner numbering and `NoBundleFailure` depend only on the mode P view. -/
theorem phase_view (first second : List Entry) (same : SameView first second) :
    phase first = phase second ∧ owner first = owner second ∧ (NoBundleFailure first ↔ NoBundleFailure second) := by
  have summary := summarize_view first second same
  refine ⟨?_, ?_, ?_⟩
  · funext index
    simp only [phase, summary]
  · funext k
    simp only [owner, summary]
  · simp only [NoBundleFailure, NoBundleFailureAt, summary]

/-- The designation and its restriction to a budget's target domain depend only on the mode P view: raw-receive plaintexts never influence which target a handle names. -/
theorem designate_view (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (first second : List Entry) (same : SameView first second) :
    designate crypto codec serverKid first = designate crypto codec serverKid second ∧
      ∀ budget : Budget, designateIn crypto codec serverKid budget first = designateIn crypto codec serverKid budget second := by
  have summary := summarize_view first second same
  have bundles : bundleOf first = bundleOf second := funext fun _ =>
    findSome_view _ (view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have finishes : finishOf first = finishOf second := funext fun _ =>
    findSome_view _ (view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have accepts : acceptOf first = acceptOf second := funext fun _ =>
    findSome_view _ (view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have builds : buildOf first = buildOf second := funext fun _ =>
    findSome_view _ (view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have links : linkOf first = linkOf second := funext fun _ =>
    findSome_view _ (view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have counted : ∀ first second : List Entry, first.map Entry.query = second.map Entry.query →
      acceptCount first = acceptCount second := by
    intro first
    induction first with
    | nil =>
        intro second queries
        cases second with
        | nil => rfl
        | cons _ _ => simp at queries
    | cons entry rest ih =>
        intro second queries
        cases second with
        | nil => simp at queries
        | cons other rest' =>
            simp only [List.map_cons, List.cons.injEq] at queries
            have tail := ih rest' queries.2
            simp only [acceptCount, List.countP_cons] at tail ⊢
            rw [queries.1, tail]
  have count : acceptCount first = acceptCount second := by
    apply counted
    have mapped := congrArg (List.map PqxdhDeploymentInterface.PublicEntry.query) same
    simpa [SameView, List.map_map, Function.comp_def, Entry.view] using mapped
  have publishes : Publishes codec first = Publishes codec second := by
    funext accepted pqKey k
    rw [Publishes, Publishes, bundles]
  have linked : Linked crypto codec first = Linked crypto codec second := by
    funext ciphertext pin pqKey session
    rw [Linked, Linked, builds, accepts]
  have designated : designate crypto codec serverKid first = designate crypto codec serverKid second := by
    funext handle
    cases handle with
    | peer keyId =>
        simp only [designate]
        rw [links, accepts, publishes, summary]
    | owner index =>
        have phases : phase first = phase second := (phase_view first second same).1
        simp only [designate]
        rw [phases, summary, finishes, bundles, count, linked]
  refine ⟨designated, fun budget => ?_⟩
  funext handle
  unfold designateIn
  rw [designated]

end BeaconcryptCore.Computational.PqxdhDeploymentTranscript

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.summarize_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.summarize_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.step_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.step_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_peer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_peer_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_peer_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_owner_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_owner_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.view_respects' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.view_respects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.findSome_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.findSome_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.summarize_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.summarize_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.phase_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.phase_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentTranscript.designate_view
