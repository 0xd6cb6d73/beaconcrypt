-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingLedger
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache
import BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache

/-! Exact cross-handle record binding implies a retained commitment conflict. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsBindingLedger PqxdhRecordFactsBindingKnown
open PqxdhRecordFactsBindingCache PqxdhRecordFactsOriginReplay
open PqxdhRecordFactsOriginAccepted PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsPrivateCacheSourceDraw (HashInput)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Receiver)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Target classification depends only on the queried address, before its digest is sampled. -/
def privateInput : HashInput n → Bool
  | .inl _ => true
  | .inr _ => false

/-- A conflict visible in retained seal histories and the unchanged shared ROM, without referring to erased private caches. -/
def DigestConflict (secret : CtxPrivate n) : Prop :=
  (∃ first second : Label n, first ≠ second ∧
    ∃ left ∈ (secret.keys first).1.successfulSeals,
    ∃ right ∈ (secret.keys second).1.successfulSeals, left.record.commit = right.record.commit) ∨
  (∃ label, ∃ entry ∈ (secret.keys label).1.successfulSeals,
    ∃ bytes, secret.base.primitive.2 ((), bytes) = some entry.record.commit)

/-- Actual cache representation turns a retained conflict into a distinct-input collision with at least one private address. -/
theorem conflict_collision (secret : CtxPrivate n) (cached : AllCached secret)
    (conflict : DigestConflict secret) :
    PqxdhRecordFactsCollisionCache.Collision privateInput (PqxdhRecordFactsDigestCache.cacheOf secret) := by
  rcases conflict with ⟨first, second, different, left, atLeft, right, atRight, equal⟩ |
    ⟨label, entry, present, bytes, shared⟩
  · refine ⟨.inl (first, outerSuffix left.input.nonce left.input.context left.record.tag),
      .inl (second, outerSuffix right.input.nonce right.input.context right.record.tag),
      left.record.commit, ?_, Or.inl rfl, cached first left atLeft, ?_⟩
    · intro same
      exact different (congrArg Prod.fst (Sum.inl.inj same))
    · exact equal.symm ▸ cached second right atRight
  · exact ⟨.inl (label, outerSuffix entry.input.nonce entry.input.context entry.record.tag),
      .inr bytes, entry.record.commit, by simp, Or.inl rfl, cached label entry present, shared⟩

/-- Two actual source records with the same complete frame either name partner handles or force a retained commitment conflict. -/
theorem records_conflict (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (first second : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (encrypted : RawCtxSourceSend.Encrypted) (frame : RawCtxReceive.DecodedFrame)
    (accepted : Accepted codec control secret first raw opened)
    (published : Published codec control secret second encrypted)
    (receivedFrame : codec.frameRead raw = some frame)
    (publishedFrame : codec.frameRead encrypted.ciphertext = some frame)
    (knownReceived : PqxdhRecordLiftFlat.KnownAt control first → SharedRecord codec secret raw)
    (knownPublished : PqxdhRecordLiftFlat.KnownAt control second → SharedRecord codec secret encrypted.ciphertext)
    (hidden : (handleSlot control first).isSome ∨ (handleSlot control second).isSome)
    (unrelated : ¬Partners (handleSlot control) first second) : DigestConflict secret := by
  rcases accepted with knownFirst | ⟨left, leftSlot, leftDirection, leftFrame, leftDecoded, leftEntry, leftPresent, leftMatch, _⟩
  · rcases published with knownSecond | ⟨right, rightOwner, rightFrame, rightDecoded, rightEntry, rightPresent, rightMatch⟩
    · simp [known_no_slot control first knownFirst, known_no_slot control second knownSecond] at hidden
    · obtain ⟨sharedFrame, sharedDecoded, shared⟩ := knownReceived knownFirst
      exact Or.inr ⟨right, rightEntry, rightPresent, matches_shared frame rightEntry
        ((Option.some.inj (rightDecoded.symm.trans publishedFrame)) ▸ rightMatch) _
        ((Option.some.inj (sharedDecoded.symm.trans receivedFrame)) ▸ shared)⟩
  · rcases published with knownSecond | ⟨right, rightOwner, rightFrame, rightDecoded, rightEntry, rightPresent, rightMatch⟩
    · obtain ⟨sharedFrame, sharedDecoded, shared⟩ := knownPublished knownSecond
      exact Or.inr ⟨left, leftEntry, leftPresent, matches_shared frame leftEntry
        ((Option.some.inj (leftDecoded.symm.trans receivedFrame)) ▸ leftMatch) _
        ((Option.some.inj (sharedDecoded.symm.trans publishedFrame)) ▸ shared)⟩
    · exact Or.inl ⟨left, right,
        (fun equal => unrelated ⟨left.slot, leftSlot,
          counterpart_of_opposite control left second first (equal.symm ▸ rightOwner) leftDirection⟩),
        leftEntry, leftPresent, rightEntry, rightPresent,
        matches_commit frame leftEntry rightEntry
          ((Option.some.inj (leftDecoded.symm.trans receivedFrame)) ▸ leftMatch)
          ((Option.some.inj (rightDecoded.symm.trans publishedFrame)) ▸ rightMatch)⟩

/-- The frozen global cross-accept event reduces to retained evidence, including publication anywhere in the complete transcript. -/
theorem cross_accept_conflict (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (view : View n E X)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (slots : view.slots = handleSlot control)
    (ledger : ∀ value ∈ view.result, LedgerEvidence codec route control secret value.2.1.transcript)
    (crossed : CrossAccept codec route view) : DigestConflict secret := by
  obtain ⟨value, resultPresent, entry, entryPresent, receiver, raw, opened, first, second, frame,
    received, routed, decoded, ⟨encrypted, published, publishedFrame⟩, hidden, unrelated⟩ := crossed
  obtain ⟨sentEntry, sentPresent, sentRecord⟩ := List.mem_filterMap.mp published
  exact records_conflict codec control secret first second raw opened encrypted frame
    ((ledger value resultPresent).accepted entry entryPresent receiver raw opened first received routed)
    ((ledger value resultPresent).published sentEntry sentPresent second encrypted sentRecord)
    decoded publishedFrame
    ((ledger value resultPresent).knownReceived entry entryPresent receiver raw opened first received routed)
    ((ledger value resultPresent).knownPublished sentEntry sentPresent second encrypted sentRecord)
    (slots ▸ hidden) (slots ▸ unrelated)

/-- The conflict event uses only complete retained seal histories and the actual shared hash cache. -/
theorem conflict_retained (before after : CtxPrivate n)
    (shared : before.base.primitive.2 = after.base.primitive.2)
    (seals : ∀ label, (before.keys label).1.successfulSeals = (after.keys label).1.successfulSeals) :
    DigestConflict before ↔ DigestConflict after := by
  simp only [DigestConflict, shared, seals]

/-- The exact counter/cache-erasure observation preserves the binding conflict in both directions. -/
theorem conflict_observe (before after : CtxPrivate n)
    (retained : PqxdhRecordFactsPrivateCacheWorld.observe before =
      PqxdhRecordFactsPrivateCacheFamily.observeFamily after) :
    DigestConflict before ↔ DigestConflict after := by
  exact conflict_retained before after
    (congrArg (fun base => base.primitive.2) (congrArg Prod.fst retained))
    (fun label => congrArg (fun localState => localState.successfulSeals)
      (congrFun (congrArg Prod.snd retained) label))

open Classical in
/-- The retained commitment conflict as a Boolean event. -/
noncomputable def conflictEvent (secret : CtxPrivate n) : Bool := decide (DigestConflict secret)

/-- The complete actual source run and cache-erased run have identical conflict-event distributions. Original source work remains accounted separately. -/
theorem run_conflict_observation (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : ∀ label, modes label ≠ .real) :
    LazyOracleDiscard.LawEq
      ((fun result => conflictEvent result.2) <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary)
      ((fun result => conflictEvent result.2) <$>
        PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary) := by
  have same := (PqxdhRecordFactsPrivateCacheWorld.run_observation modes replace setup codec route env serverKid bounds mode adversary ideal).map
    (fun result : Client n E X × (PqxdhRecordLiftProtocol.Private n × (Label n → PqxdhRecordFactsPrivateCache.Local)) =>
      conflictEvent ⟨result.2.1, fun label => (result.2.2 label, ∅)⟩)
  simp only [Functor.map_map] at same
  convert same using 1 <;> congr 1

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_collision

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.records_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.records_conflict

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.cross_accept_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.cross_accept_conflict

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_retained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_observe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.conflict_observe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.run_conflict_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent.run_conflict_observation

