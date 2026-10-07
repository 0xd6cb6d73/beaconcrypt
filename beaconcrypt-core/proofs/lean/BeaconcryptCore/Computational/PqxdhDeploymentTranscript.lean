-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentInterface
import BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures

/-! Public functions of the transcript of the common deployment experiment (CE-1). Every function here reads only transcript entries, that is, adversary queries with their replies; none reads a secret, a root, a partner or a native ghost. `summarize` folds the transcript into the created owner bindings in creation order, the public lifecycle phase of every owner handle (Fresh after a successful create, InitSent after a successful bundle in Fresh, Established after a successful finish in InitSent, Aborted after a rejected finish in InitSent, unchanged otherwise) and the owners with a rejected bundle call in Fresh. `owner k` is the handle created `k`-th. `NoBundleFailure` says that no bundle call made in Fresh was rejected. `designate` maps a record handle to at most one target `(session, KEM creation index)`: a Server peer to the session whose build returned its key ID and the smallest owner whose published bundle carries the accepted identity and PQ fields; an established Beacon pinned to the protected key ID to the smallest session whose build response carries its finish ciphertext and its pin as Server identity and whose accepted PQ field is the Beacon's published one. Codec readers and the raw candidate of `PqxdhRegistrationJointRawSignatures` are applied to public bytes only. That these public functions agree with the native state is a separate obligation (CE-5); no security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentTranscript
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (Entry Handle Command Query FullSpec Budget parsePin)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhEd25519EufCma (Phase1Candidate)
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

/-- Owner `k` published a bundle carrying the identity and PQ fields of an accepted candidate. -/
def Publishes (codec : Codec Reader Response) (transcript : List Entry) (accepted : Phase1Candidate) (k : Nat) : Prop :=
  ∃ published, (bundleOf transcript k).bind (candidateOf codec) = some published ∧
    published.identityKey = accepted.identityKey ∧ published.pqKey = accepted.pqKey

/-- Session `session` is linked to an established owner: its build response carries the owner's finish ciphertext and the owner's pin as Server identity, and its accepted PQ field is the owner's published PQ field. -/
def Linked (codec : Codec Reader Response) (transcript : List Entry) (ciphertext : Ciphertext) (pin : Word32)
    (published : Phase1Candidate) (session : Nat) : Prop :=
  ∃ response accepted, buildOf transcript session = some response ∧
    (codec.read2 response.serialized).bind codec.ciphertext = some ciphertext ∧
    (codec.read2 response.serialized).bind codec.serverIdentity = some pin ∧
    (acceptOf transcript session).bind (candidateOf codec) = some accepted ∧ accepted.pqKey = published.pqKey

open Classical in
/-- Target designation of a record handle. A Server peer `keyId` designates `(i, k)` when session `i` built it, its accept bytes give candidate `c`, and `k` is the smallest created owner whose published bundle carries `c`'s identity and PQ fields. An owner `c` designates `(i, c)` when it is Established, its key ID is the protected `serverKid`, its finish input gives a ciphertext, its bundle gives a published candidate, and `i` is the smallest session handle linked to it. Everything else is ineligible. -/
noncomputable def designate (codec : Codec Reader Response) (serverKid : Std.U64) (transcript : List Entry) :
    Handle → Option (Nat × Nat)
  | .peer keyId => do
      let link ← linkOf transcript keyId
      let raw ← acceptOf transcript link.1
      let accepted ← candidateOf codec raw
      let k ← (List.range (summarize transcript).owners.length).find? fun k =>
        decide (Publishes codec transcript accepted k)
      pure (link.1, k)
  | .owner index =>
      if phase transcript index = .established then do
        let binding ← (summarize transcript).owners[index]?
        if binding.2 = serverKid then do
          let raw ← finishOf transcript index
          let ciphertext ← (codec.read2 raw).bind codec.ciphertext
          let published ← (bundleOf transcript index).bind (candidateOf codec)
          let session ← (List.range (acceptCount transcript)).find? fun session =>
            decide (Linked codec transcript ciphertext binding.1 published session)
          pure (session, index)
        else none
      else none

/-- Designation into the finite target domain of a budget: `none` for an ineligible handle or a pair outside `Fin qAccept × Fin (count + 1)`. -/
noncomputable def designateIn (codec : Codec Reader Response) (serverKid : Std.U64) (budget : Budget)
    (transcript : List Entry) (handle : Handle) : Option (Fin budget.accept × Fin budget.capacity) :=
  (designate codec serverKid transcript handle).bind fun target =>
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

/-- A designated Server peer was built by the designated session, whose accept bytes give a candidate that owner `k`, created before the end of the transcript, published. -/
theorem designate_peer (codec : Codec Reader Response) (serverKid keyId : Std.U64) (transcript : List Entry)
    (session k : Nat) (designated : designate codec serverKid transcript (.peer keyId) = some (session, k)) :
    ∃ response raw accepted, linkOf transcript keyId = some (session, response) ∧
      acceptOf transcript session = some raw ∧ candidateOf codec raw = some accepted ∧
      k < (summarize transcript).owners.length ∧ Publishes codec transcript accepted k := by
  simp only [designate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at designated
  obtain ⟨⟨linked, response⟩, linkFound, raw, rawFound, accepted, acceptedFound, chosen, chosenFound, same⟩ := designated
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have member := List.mem_of_find?_eq_some chosenFound
  have holds := List.find?_some chosenFound
  simp only [decide_eq_true_eq] at holds
  exact ⟨response, raw, accepted, linkFound, rawFound, acceptedFound, List.mem_range.mp member, holds⟩

/-- A designated owner is Established, pinned to the protected key ID, designates its own creation index, and the designated session is a linked accept attempt. -/
theorem designate_owner (codec : Codec Reader Response) (serverKid : Std.U64) (transcript : List Entry)
    (index session k : Nat) (designated : designate codec serverKid transcript (.owner index) = some (session, k)) :
    k = index ∧ phase transcript index = .established ∧
      ∃ pin raw ciphertext published, (summarize transcript).owners[index]? = some (pin, serverKid) ∧
        finishOf transcript index = some raw ∧ (codec.read2 raw).bind codec.ciphertext = some ciphertext ∧
        (bundleOf transcript index).bind (candidateOf codec) = some published ∧
        session < acceptCount transcript ∧ Linked codec transcript ciphertext pin published session := by
  by_cases established : phase transcript index = .established
  · simp only [designate, established, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at designated
    obtain ⟨⟨pin, kid⟩, bindingFound, designated⟩ := designated
    by_cases pinned : kid = serverKid
    · simp only [pinned, ite_true, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at designated
      obtain ⟨raw, rawFound, ciphertext, ciphertextFound, published, publishedFound, chosen, chosenFound, rfl, rfl⟩ :=
        designated
      have member := List.mem_of_find?_eq_some chosenFound
      have holds := List.find?_some chosenFound
      simp only [decide_eq_true_eq] at holds
      subst pinned
      exact ⟨rfl, established, pin, raw, ciphertext, published, bindingFound, rawFound,
        Option.bind_eq_some_iff.mpr ciphertextFound, Option.bind_eq_some_iff.mpr publishedFound,
        List.mem_range.mp member, holds⟩
    · simp only [pinned, ite_false, reduceCtorEq] at designated
  · simp only [designate, established, ite_false, reduceCtorEq] at designated

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
