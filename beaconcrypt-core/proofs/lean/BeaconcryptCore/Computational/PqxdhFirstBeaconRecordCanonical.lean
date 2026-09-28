import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx
import BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent
import BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop
import BeaconcryptCore.Computational.PqxdhInitialKernelConstruction
import BeaconcryptCore.Computational.RawCtxSourcePublication

/-!
# Canonical first-record forgery event

`PqxdhFirstBeaconRecordIntegrity.forgeryPost` counts an accepted first record as forged when its decoded frame differs from the decodings of the bytes returned by earlier sends. With the production Cap'n Proto codec this can count a genuine record as forged. The reader rejects messages of more than `2^23` words, and the writer puts a long Data field in a second segment, so for payloads of 67108825 to 67108832 bytes the reader rejects the writer's own bytes while it accepts a one-segment encoding of the same frame. An adversary that re-encodes Beacon `b`'s genuine first record in one segment and delivers it therefore produces a counted record that the CTX observer does not count. The read-back codec premise that an earlier version of the gap proof used to exclude this case (every frame that the reader returns is written to bytes that the reader decodes back to that frame) is false in production.

This module replaces the comparison. `CanonicalForged` counts an accepted sequence-one Server raw receive at the registered peer when the environment's record writer, applied to the decoded frame, does not give the bytes of any sequence-one record returned by an earlier send (`FirstWritten`). A re-encoding decodes to the same frame, and the writer maps that frame to the bytes that the send returned, so it is not counted: `reencoded_not_counted` states this for any frame with a `FirstWritten` witness, and `sent_reencoding_not_counted` obtains the witness, under the writer premise below, from an earlier send whose reply carries the writer's bytes for the frame and its sequence, which is the shape of every selected send reply (`produced_frame`). `canonicalPost` logs the post exactly like `forgeryPost`; logging adds no request, so the original query certificate transfers unchanged (`canonical_query_bound`, `canonicalCertificate`). A single accepted entry with no earlier send is a canonical forgery (`canonical_forged_single`), so the event is not vacuous.

Chain. The C4 and C5 steps `pending_ideal_le`, `compiled_ctx_bound`, `fullClient_uses` and `prelude_hash` hold for every post. Only the steps that name `forgeryPost` are proved again for `canonicalPost`: the certificate, the pending bound (`canonical_pending_le`), the actual-game bound (`canonical_forgery_le`), the post budget (`canonical_total`) and the CTX bound with the gap game (`canonical_integrity_ctx`).

Gap. The invariant of that earlier gap proof is copied and adapted: observer lemmas, the transcript invariant `Inv` along the compiled post (`inv_post`), the proved first-slot fact `first_slot_hidden` and `suffix_won`. Outside the initial half alias, an accepted canonical forgery that the observer does not win matches a selected seal. Every selected seal is transcribed: the writer either rejects the seal's frame or an earlier send returned the writer's bytes for it. In the second case `FirstWritten` holds and the record is not a canonical forgery. The first case is excluded by the writer premise below, so `gap_le` bounds the gap game by the alias probability `2^-256`.

Premise. `ReadWritable writer read` says that the record writer returns bytes for every frame that the record reader returns; the proof uses it only for the sequence-one frames of accepted Server raw receives. It relates two environment functions and involves no probability, adversary or secret. Unlike the read-back premise, it does not ask the reader to accept the writer's bytes, so the 64 MiB counterexample does not touch it. Production satisfies it by inspection of the capnp 0.26.2 source, which is not proved in Lean: a Cap'n Proto Data field returned by the reader has at most `2^29 - 1` bytes, because the list pointer stores the element count in 29 bits (with the default reader options, which reject messages of more than `2^23` words, it is even shorter than `2^26` bytes), and the writer of `seal_frame` has no error return below that size: `set_cipher_text` only asserts that the Data field is shorter than `2^29` bytes, and `serialize::write_message` into a `Vec<u8>` fails only when `write_all` fails, which it does not for a vector. For Data of `2^29` bytes or more the writer panics, and it aborts when allocation fails; neither case is modeled and neither is needed, because the writer contract `RawCtxSourcePublication.WritesOn` constrains the model writer only below `2^29` bytes and `ReadWritable` concerns only frames that the reader returns. In Lean the two production facts are contracts: `read_writable` derives the premise from `WritesOn` and the reader bound `ReadBounded`, and `frame_decode_bounded` gives `ReadBounded` for the protocol decoder `RawCtxFrameDecoding.decode` over a reader whose Data getter respects the 29-bit limit, which is a hypothesis on the reader. A statistical charge for the excluded case (a seal whose writer failed, so its record never reached the adversary) is not proved here: the compiled client receives that record from the challenger and discards it, and bounding the chance that the adversary reproduces its 64-byte commitment needs an independence argument over the whole compiled post that the library does not provide.

Result. `first_beacon_record_integrity_canonical` has the left side of `first_beacon_forgery_le` with the canonical proxy and bounds it by the first-record target loss, the completed-branch root loss, the CTX loss `ctxLoss`, `2^-256` twice (once in the compiled bound and once in the gap bound) and the restricted stop game `stopGame`. Its premises are those of `PqxdhFirstBeaconRecordCtx.first_beacon_record_integrity` and `ReadWritable env.recordWriter env.decode`.

Limits. Only the first record (sequence one) of Beacon `b` at the Server peer registered by the first Server builder is covered. As in C4, a record whose writer bytes equal those of an earlier sequence-one send of any Server or Beacon is not counted; for a writer that maps different frames to different bytes this is exactly the set of frames written by earlier sends. The `stopGame` term remains; `PqxdhFirstRecordStopBound.stopGame_le` moves it to `sourceStopGame`, which is bounded separately. Public HKDF remains the real fixed-source function; the candidate keys used by `first_slot_hidden` are proof-internal interpretations and add no oracle or game. Snapshots, persistence and restoration are excluded, as in the imported modules.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical

section Observer
open RawCtxSelectedAuthenticationObserver AdaptiveCtxReceive CtxRomAuth
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)

/-- One observer step never removes a won attempt. -/
theorem won_step (decode : RawDecoder) (query : Spec.Domain) (reply : Spec.Range query) (state : State)
    (winning : won decode state = true) : won decode (step query reply state) = true := by
  rcases query with ((coin | (hash | input)) | raw) | known
  all_goals first
    | exact winning
    | (cases reply <;> exact winning)
    | (change (accepted decode _ || won decode state) = true; rw [winning, Bool.or_true])

/-- The observed challenger never removes a won attempt. -/
theorem observed_won (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result) (start : State × SourceState) (winning : won decode start.1 = true)
    (result : Result × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run start)) :
    won decode result.2.1 = true := by
  refine simulateQ_run_preservesInv (observed true decode c key) (fun state => won decode state.1 = true)
    (fun query state inv result reached => ?_) client start winning result supported
  simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨actual, _, rfl⟩ := reached
  exact won_step decode query actual.1 state.1 inv

/-- A client without selected seal requests leaves the observer's seal history unchanged. -/
theorem observed_seals (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result)
    (noSeal : client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (start : State × SourceState) (result : Result × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run start)) :
    result.2.1.seals = start.1.seals := by
  induction client using OracleComp.inductionOn generalizing start with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst supported
    rfl
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at noSeal
    have excluded : ¬ AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query := by
      rcases noSeal.1 with excluded | impossible
      · exact excluded
      · exact absurd impossible (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, rest⟩ := supported
    have tail := ih middle.1 (by simpa only [excluded, ite_false] using noSeal.2 middle.1) middle.2 rest
    rw [tail]
    simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
    obtain ⟨actual, _, rfl⟩ := reached
    rcases query with ((coin | (hash | input)) | raw) | known
    all_goals first
      | rfl
      | exact absurd trivial excluded

/-- An observed run's reply and observer state are a supported run of the executable monitor. -/
theorem observed_monitor (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result) (start : State × SourceState) (result : Result × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run start)) :
    (result.1, result.2.1) ∈ support (monitor client start.1) := by
  rw [← monitored_program true decode c key client start, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  apply support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) (monitor client start.1) start.2
  rw [StateT.run'_eq, support_map]
  exact ⟨actual, reached, rfl⟩

/-- An observed run's reply and component state are a supported run of the unobserved challenger. -/
theorem observed_component (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result) (start : State × SourceState) (result : Result × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run start)) :
    (result.1, result.2.2) ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run start.2) := by
  rw [← monitored_program true decode c key client start, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  have erased : (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run start.2 =
      (fun value => (value.1.1, value.2)) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) (monitor client start.1)).run start.2 := by
    conv_lhs => rw [← monitor_erase client start.1]
    rw [simulateQ_map, StateT.run_map]
  rw [erased, support_map]
  exact ⟨actual, reached, rfl⟩

/-- A component state that differs only in its cache and public log keeps the observer's seal history when both are consistent. -/
theorem clean_seals (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (before after : State × SourceState)
    (goodBefore : RawCtxSelectedPlaintextOrigins.Good decode c key before)
    (goodAfter : RawCtxSelectedPlaintextOrigins.Good decode c key after)
    (clean : PqxdhFirstBeaconRecordCtx.Clean before.2 after.2) : after.1.seals = before.1.seals := by
  obtain ⟨shared, same⟩ := clean
  rw [goodAfter.1, goodBefore.1, same]
  rfl

/-- An observed run's reply is a supported reply of the client itself. -/
theorem observed_syntactic (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result) (start : State × SourceState) (result : Result × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run start)) : result.1 ∈ support client := by
  apply support_simulateQ_run'_subset (observed true decode c key) client start
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- The reply marginal of an observed run is the reply marginal of the unobserved challenger run. -/
theorem observed_fst (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (client : OracleComp Spec Result) (start : State × SourceState) :
    Prod.fst <$> (simulateQ (observed true decode c key) client).run start =
      Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run start.2 := by
  rw [← monitored_program true decode c key client start, Functor.map_map]
  conv_rhs => rw [← monitor_erase client start.1]
  rw [simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The gap game is the observed run of the client with the event that the client returned `true` and the observer did not win. -/
theorem gap_observed (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    PqxdhFirstBeaconRecordCtx.gapGame decode c client = (do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (observed true decode c key) client).run (initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
      pure (result.1 && !won decode result.2.1)) := by
  unfold PqxdhFirstBeaconRecordCtx.gapGame
  refine bind_congr fun key => ?_
  rw [← monitored_program true decode c key client (initialState, AdaptiveCtxDynamicKnownKeys.initialSource), bind_map_left]
  rfl

end Observer


section Event
open PqxdhFirstBeaconRecordIntegrity CtxRomAuth
variable {ι : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Some successful send in `log` returned a sequence-one record whose bytes are the record writer's bytes for `frame`. -/
def FirstWritten (writer : RawCtxMixedShared.Writer) (log : List (Entry baseSpec S B)) (frame : RawCtxReceive.DecodedFrame) : Prop :=
  ∃ entry ∈ log, ∃ encrypted, sent entry = some encrypted ∧ encrypted.sequence.val = 1 ∧ writer frame = some encrypted.ciphertext

/-- Canonical forgery: some Server raw receive at `index`, routed to `kid`, accepted a sequence-one record, and the record writer applied to its decoded frame gives the bytes of no sequence-one record returned by an earlier send. -/
def CanonicalForged (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (kid : Std.U64) (log : List (Entry baseSpec S B)) : Prop :=
  ∃ before entry after raw decrypted, log = before ++ entry :: after ∧
    serverOpen entry = some (index, raw, .Some decrypted) ∧ route raw = some kid ∧ decrypted.sequence.val = 1 ∧
    ∀ frame, decode raw = some frame → ¬FirstWritten writer before frame

/-- The canonical forgery event for the registration reply: its key identifier names the Server peer; an unsuccessful registration has no forgery. -/
def ReplyCanonicalForged (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (log : List (Entry baseSpec S B)) : Prop :=
  match reply with
  | .ok (some response) => CanonicalForged index route decode writer response.keyId log
  | _ => False

/-- The logged post bit of the canonical proxy: the adversary's own bit and the canonical forgery event. -/
noncomputable def canonicalBit (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (result : Bool × List (Entry baseSpec S B)) : Bool :=
  result.1 && @decide (ReplyCanonicalForged index route decode writer reply result.2) (Classical.propDecidable _)

/-- A written-send witness survives appending entries to the transcript. -/
theorem firstWritten_append (writer : RawCtxMixedShared.Writer) (log more : List (Entry baseSpec S B))
    (frame : RawCtxReceive.DecodedFrame) (witness : FirstWritten writer log frame) : FirstWritten writer (log ++ more) frame := by
  obtain ⟨entry, present, encrypted, sentEntry, sequence, written⟩ := witness
  exact ⟨entry, List.mem_append_left _ present, encrypted, sentEntry, sequence, written⟩

/-- A canonical forgery in a transcript with one appended entry is a forgery of the prefix or is witnessed by the appended entry itself. -/
theorem canonical_forged_append (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (kid : Std.U64) (log : List (Entry baseSpec S B)) (last : Entry baseSpec S B)
    (forged : CanonicalForged index route decode writer kid (log ++ [last])) :
    CanonicalForged index route decode writer kid log ∨ ∃ raw decrypted, serverOpen last = some (index, raw, .Some decrypted) ∧
      route raw = some kid ∧ decrypted.sequence.val = 1 ∧ ∀ frame, decode raw = some frame → ¬FirstWritten writer log frame := by
  obtain ⟨before, entry, after, raw, decrypted, split, opened, routed, sequence, fresh⟩ := forged
  rcases split_append log [last] before after entry split with ⟨middle, rfl, _⟩ | ⟨middle, single, rfl⟩
  · exact Or.inl ⟨before, entry, middle, raw, decrypted, rfl, opened, routed, sequence, fresh⟩
  · cases middle with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at single
      obtain ⟨rfl, rfl⟩ := single
      exact Or.inr ⟨raw, decrypted, opened, routed, sequence, by simpa only [List.append_nil] using fresh⟩
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at single
      exact absurd single.2.symm (by simp)

/-- Non-vacuity: a transcript whose only entry is an accepted sequence-one Server raw receive at `index` routed to `kid` is a canonical forgery. -/
theorem canonical_forged_single (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (kid : Std.U64) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (routed : route raw = some kid) (sequence : decrypted.sequence.val = 1) :
    CanonicalForged index route decode writer kid [serverRawEntry (baseSpec := baseSpec) (B := B) index raw (.Some decrypted)] :=
  ⟨[], _, [], raw, decrypted, rfl, rfl, routed, sequence, fun _ _ ⟨_, present, _⟩ => by simp at present⟩

/-- Re-encodings are not counted: a Server raw receive whose decoded frame the writer maps to the bytes of a sequence-one record returned by an earlier send (for example a different encoding of that record) neither creates nor removes a canonical forgery when appended. -/
theorem reencoded_not_counted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (writer : RawCtxMixedShared.Writer) (kid : Std.U64) (log : List (Entry baseSpec S B)) (raw : Pqxdh.Bytes)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (frame : RawCtxReceive.DecodedFrame) (decoded : decode raw = some frame)
    (written : FirstWritten writer log frame) :
    CanonicalForged index route decode writer kid (log ++ [serverRawEntry index raw reply]) ↔
      CanonicalForged index route decode writer kid log := by
  constructor
  · intro forged
    rcases canonical_forged_append index route decode writer kid log _ forged with old | ⟨raw', decrypted, opened, _, _, fresh⟩
    · exact old
    · simp only [serverRawEntry, serverOpen, Option.some.injEq, Prod.mk.injEq] at opened
      obtain ⟨_, rfl, _⟩ := opened
      exact absurd written (fresh frame decoded)
  · rintro ⟨before, entry, after, raw', decrypted, split, opened, routed, sequence, fresh⟩
    exact ⟨before, entry, after ++ [serverRawEntry index raw reply], raw', decrypted, by rw [split]; simp, opened, routed, sequence,
      fresh⟩

/-- A selected seal is transcribed when every frame carrying its sequence, sender and record encoding is either rejected by the writer or was returned, with the writer's bytes and that sequence, by a send in the transcript. -/
def Transcribed (writer : RawCtxMixedShared.Writer) (log : List (Entry baseSpec S B)) (sealed : CtxSuccessfulSeal) : Prop :=
  ∀ frame : RawCtxReceive.DecodedFrame, frame.sequence.val = sealed.input.context.ad.seq →
    frame.sender.val = sealed.input.context.ad.sid → frame.payload = sealed.record.encode →
      writer frame = none ∨ ∃ entry ∈ log, ∃ encrypted, sent entry = some encrypted ∧
        encrypted.sequence = frame.sequence ∧ writer frame = some encrypted.ciphertext

/-- Transcription survives appending entries to the transcript. -/
theorem transcribed_append (writer : RawCtxMixedShared.Writer) (log more : List (Entry baseSpec S B))
    (sealed : CtxSuccessfulSeal) (transcribed : Transcribed writer log sealed) : Transcribed writer (log ++ more) sealed := by
  intro frame sequence sender payload
  rcases transcribed frame sequence sender payload with failed | ⟨entry, present, encrypted, sentEntry, same, written⟩
  · exact Or.inl failed
  · exact Or.inr ⟨entry, List.mem_append_left _ present, encrypted, sentEntry, same, written⟩

end Event

section Post
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
open PqxdhFirstBeaconRecordIntegrity

/-- The canonical forgery proxy: run `post0` while logging its transcript and output its bit together with the canonical Server-peer first-record forgery event. -/
noncomputable def canonicalPost : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1) :=
  fun selection reply => canonicalBit env.index env.route env.decode env.recordWriter reply <$> logged (post0 selection reply) []

/-- The canonical proxy makes exactly the requests of `post0`, so it keeps every post query budget. -/
theorem canonical_query_bound (selection : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (predicate : (PostSpec baseSpec S (B + 1)).Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (canonicalPost env program post0 selection reply).IsQueryBoundP predicate bound ↔
      (post0 selection reply).IsQueryBoundP predicate bound := by
  simp only [canonicalPost, isQueryBoundP_map_iff]
  exact logged_queries predicate (post0 selection reply) [] bound

/-- The original certificate transported to the canonical proxy: only the post budget refers to the post, and it is unchanged. -/
def canonicalCertificate (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post0) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (canonicalPost env program post0) :=
  { c with
    postBound := by
      intro selection reply kind
      exact (canonical_query_bound env program post0 selection reply _ _).mpr (c.postBound selection reply kind) }

end Post

section Premise
open PqxdhFirstBeaconRecordIntegrity CtxRomAuth
variable {ι : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Writer premise: the record writer returns bytes for every frame that the record reader returns. -/
def ReadWritable (writer : RawCtxMixedShared.Writer) (read : RawCtxReceive.FrameDecoder) : Prop :=
  ∀ bytes frame, read bytes = some frame → ∃ out, writer frame = some out

/-- The reader returns only frames whose payload is shorter than the Cap'n Proto Data-list limit `2^29`. -/
def ReadBounded (read : RawCtxReceive.FrameDecoder) : Prop :=
  ∀ bytes frame, read bytes = some frame → frame.payload.length < RawCtxSourcePublication.dataLimit

/-- The writer premise follows from the library's writer contract `WritesOn` (the in-memory writer returns its encoding for every payload shorter than `2^29` bytes) and the Data-list bound of the reader. -/
theorem read_writable (writer : RawCtxMixedShared.Writer) (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes)
    (writes : RawCtxSourcePublication.WritesOn writer encode) (read : RawCtxReceive.FrameDecoder) (bounded : ReadBounded read) :
    ReadWritable writer read :=
  fun bytes frame decoded => ⟨encode frame, writes frame (bounded bytes frame decoded)⟩

/-- The protocol frame decoder over a Cap'n Proto reader whose Data getter returns fewer than `2^29` bytes returns only bounded frames. -/
theorem frame_decode_bounded {Message Root : Type} (reader : RawCtxFrameDecoding.Reader Message Root)
    (limit : ∀ root payload, reader.payload root = some payload → payload.length < RawCtxSourcePublication.dataLimit) :
    ReadBounded (RawCtxFrameDecoding.decode reader) := by
  intro bytes frame decoded
  simp only [RawCtxFrameDecoding.decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨root, _, payload, found, same⟩ := decoded
  rw [← Option.some.inj same]
  exact limit root payload found

/-- An accepted frame with the sequence, sender and record encoding of a transcribed seal and with sequence one was written, with the writer's bytes, by a sequence-one send of the transcript, given the writer premise. -/
theorem matched_written (writer : RawCtxMixedShared.Writer) (read : RawCtxReceive.FrameDecoder) (writable : ReadWritable writer read)
    (log : List (Entry baseSpec S B)) (sealed : CtxSuccessfulSeal) (transcribed : Transcribed writer log sealed)
    (bytes : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (decoded : read bytes = some frame)
    (sequence : frame.sequence.val = sealed.input.context.ad.seq) (sender : frame.sender.val = sealed.input.context.ad.sid)
    (payload : frame.payload = sealed.record.encode) (one : frame.sequence.val = 1) :
    FirstWritten writer log frame := by
  obtain ⟨out, written⟩ := writable bytes frame decoded
  rcases transcribed frame sequence sender payload with failed | ⟨entry, present, encrypted, sentEntry, same, returned⟩
  · rw [written] at failed
    cases failed
  · exact ⟨entry, present, encrypted, sentEntry, by rw [same, one], returned⟩

/-- Re-encodings of sent records are not counted: if an entry of `log` is a send whose reply carries the writer's bytes for `frame` together with `frame`'s sequence (the shape of every selected send reply, `produced_frame`) and `frame` has sequence one, then, given the writer premise, appending a Server raw receive of any bytes that decode to `frame` neither creates nor removes a canonical forgery. -/
theorem sent_reencoding_not_counted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (writer : RawCtxMixedShared.Writer) (writable : ReadWritable writer decode)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) (entry : Entry baseSpec S B) (present : entry ∈ log)
    (frame : RawCtxReceive.DecodedFrame) (keyId : Std.U64)
    (returned : sent entry = (writer frame).map (fun out => ⟨out, keyId, frame.sequence⟩)) (one : frame.sequence.val = 1)
    (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted) (decoded : decode raw = some frame) :
    CanonicalForged index route decode writer kid (log ++ [serverRawEntry index raw reply]) ↔
      CanonicalForged index route decode writer kid log := by
  obtain ⟨out, written⟩ := writable raw frame decoded
  refine reencoded_not_counted index route decode writer kid log raw reply frame decoded
    ⟨entry, present, ⟨out, keyId, frame.sequence⟩, ?_, one, written⟩
  rw [returned, written]
  rfl

end Premise


/-- Mapping a state program applies the map to the returned value only. -/
theorem state_map_apply {X Y σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = (fun result => (f result.1, result.2)) <$> work.run state
  rw [StateT.run_map]

/-- A state-program bind applied to a state runs the head and continues from its state. -/
theorem state_bind_apply {X Y σ : Type} {m : Type → Type} [Monad m]
    (head : StateT σ m X) (tail : X → StateT σ m Y) (state : σ) :
    (head >>= tail) state = (head state >>= fun result => tail result.1 result.2) := rfl

section Steps
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedAuthenticationObserver
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (key : CtxRomAuth.CtxKey)

local notation "observer" => observed true (RawCtxUniversalDecoder.decoder read) source.crypto key
local notation "compiled" => PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target
  nonce next sender route read

/-- An evaluated family request is the observed family service followed by publication in the role front. -/
theorem family_support (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState)
    (result : Option ((RawCtxProtocolRoles.SourceSpec S B).Range request) ×
      (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((compiled (.inl (.inl (.inl request)))).run) (state, component))) :
    ∃ reply after, (reply, after) ∈ support ((simulateQ observer (RawCtxSelectedFamilyCompiler.family source writer prior parent
        target nonce next sender route read request state.1.roles.1)).run component) ∧
      result = ((RawCtxSelectedFamilyLiveCompiler.publish state.1.roles reply).1,
        (({ state.1 with roles := (RawCtxSelectedFamilyLiveCompiler.publish state.1.roles reply).2 }, state.2), after)) := by
  simp only [evaluate, PqxdhSelectedPostCompiler.impl, RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk, StateT.run,
    simulateQ_map, Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, reached, rfl⟩ := supported
  rw [state_map_apply, support_map] at reached
  obtain ⟨inner, found, rfl⟩ := reached
  exact ⟨inner.1, inner.2, found, rfl⟩

/-- An evaluated reveal request makes no component call and keeps the role family. -/
theorem reveal_support (request : (RawCtxProtocolReveals.RevealSpec S B).Domain)
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState)
    (result : Option ((RawCtxProtocolReveals.RevealSpec S B).Range request) ×
      (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((compiled (.inl (.inl (.inr request)))).run) (state, component))) :
    result.2.1.1.roles.1 = state.1.roles.1 ∧ result.2.1.2 = state.2 ∧ result.2.2 = component := by
  simp only [evaluate, PqxdhSelectedPostCompiler.impl, RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk, StateT.run,
    simulateQ_pure, map_pure] at supported
  subst supported
  exact ⟨rfl, rfl, rfl⟩

/-- An evaluated selector request is the observed forwarded callback on the source-local state; the front is unchanged. -/
theorem selector_support (request : extra.Domain)
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState)
    (result : Option (extra.Range request) ×
      (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((compiled (.inl (.inr request))).run) (state, component))) :
    ∃ inner after, (inner, after) ∈ support ((simulateQ observer ((PqxdhSelectedCallbackCompiler.lower pre application initial
        selector aux (.inl (.inr (.inr (.inr (.inl request)))))).run state.2)).run component) ∧
      result = (some inner.1, ((state.1, inner.2), after)) := by
  simp only [evaluate, PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, simulateQ_map, support_map,
    Set.mem_image] at supported
  obtain ⟨middle, reached, rfl⟩ := supported
  rw [state_map_apply, support_map] at reached
  obtain ⟨inner, found, rfl⟩ := reached
  exact ⟨inner.1, inner.2, found, rfl⟩

/-- An evaluated attempted finish is the observed compiled Beacon owner on the source-local state, installed at its Beacon index. -/
theorem finish_support (index : Fin B) (raw : Pqxdh.Bytes)
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState)
    (result : Option (Option Pqxdh.Bytes) × (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((compiled (.inr (.finish index raw))).run) (state, component))) :
    ∃ inner after, (inner, after) ∈ support ((simulateQ observer ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre
        application initial selector aux prior parent target nonce next read)
          (PqxdhSelectedInitialOwnerCompiler.owner raw (state.1.roles.1.2 index))).run state.2)).run component) ∧
      result = (some inner.1.1, ((PqxdhSelectedPostCompiler.install index state.1 inner.1.2, inner.2), after)) := by
  simp only [evaluate, PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, simulateQ_map, support_map,
    ] at supported
  obtain ⟨middle, reached, rfl⟩ := supported
  rw [state_map_apply, support_map] at reached
  obtain ⟨inner, found, rfl⟩ := reached
  exact ⟨inner.1, inner.2, found, rfl⟩

end Steps

section Accept
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKey RawCtxSelectedAuthenticationObserver
open PqxdhFirstBeaconRecordIntegrity RawCtxSelectedPlaintextOrigins
variable {ι M P I D K : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The kernel opens some sequence-one record with known material: its complete receive derivation for sequence one reaches an opening whose material slot is a known value rather than the selected hidden slot. -/
def FirstKnown (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) : Prop :=
  ∃ (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (pending : RawCtxSelectedReceiveReceipt.Pending)
    (material : RatchetMaterial), sequence.val = 1 ∧
    RawCtxSelectedReceiveReceipt.terminal prior parent target nonce next
      (RawCtxInterpretedReceive.normalBegin kernel sequence context) = .opening pending ∧
    RawCtxInterpretedArguments.openArguments pending = some ⟨.known material, sequence, context⟩

/-- An accepted sequence-one Server raw receive at a peer whose first message is not opened with known material, whose decoded frame the writer maps to no earlier sequence-one send's bytes, wins the ordinary observer, provided every earlier selected seal is transcribed and the writer premise holds. -/
theorem server_accept_wins (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (writable : ReadWritable writer read) (index : Fin S) (kid : Std.U64) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (before after : State) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inl ⟨index, .inr bytes⟩) roles) before))
    (routed : route bytes = some kid) (one : decrypted.sequence.val = 1)
    (hidden : ∀ peer, (roles.1 index).server.peers kid = some peer → ¬ FirstKnown prior parent target nonce next peer.kernel)
    (log : List (Entry baseSpec S B)) (transcribed : ∀ sealed ∈ before.seals, Transcribed writer log sealed)
    (correct : ∀ attempt ∈ after.attempts, AttemptCorrect (RawCtxUniversalDecoder.decoder read) attempt)
    (fresh : ∀ frame, read bytes = some frame → ¬FirstWritten writer log frame) :
    won (RawCtxUniversalDecoder.decoder read) after = true := by
  obtain ⟨finalServer, accepted, _⟩ := RawCtxSelectedRoleReceipt.family_server_accepts source writer prior parent target nonce
    next sender route read index bytes roles finalRoles before after decrypted supported
  obtain ⟨kid', ad, peer, finalOwner, routed', _, peerFound, raw, _⟩ := RawCtxSelectedRoleReceipt.server_accepts source writer
    prior parent target nonce next sender route read bytes (roles.1 index) finalServer before after decrypted accepted
  obtain rfl : kid' = kid := Option.some.inj (routed'.symm.trans routed)
  obtain ⟨frame, kernel, _, decoded, _, received, _⟩ := RawCtxSelectedReceiveReceipt.raw_accepts prior parent target nonce next
    read bytes _ finalOwner before after decrypted raw
  obtain ⟨_, _, plaintext, _, _, value, _, _⟩ := RawCtxSelectedReceiveReceipt.receive_branch prior parent target nonce next read
    frame.sender _ frame.sequence _ before after kernel decrypted received
  have fields : decrypted = ⟨plaintext, frame.sender, frame.sequence⟩ := value
  rcases RawCtxSelectedAcceptanceOrigins.raw_cases prior parent target nonce next read bytes _ finalOwner before after decrypted raw with
    known | winning | matching
  · obtain ⟨frame', pending, material, decoded', reached, getter⟩ := known
    obtain rfl : frame' = frame := Option.some.inj (decoded'.symm.trans decoded)
    refine absurd ⟨frame'.sequence, _, pending, material, ?_, reached, getter⟩ (hidden peer peerFound)
    rw [← one, fields]
  · exact winning
  · obtain ⟨entry, member, _, _, sequence, sender, frame', decoded', payload⟩ :=
      matching_plaintext prior parent target nonce next read bytes _ decrypted before after matching correct
    obtain rfl : frame' = frame := Option.some.inj (decoded'.symm.trans decoded)
    rw [fields] at sequence sender one
    exact absurd (matched_written writer read writable log entry (transcribed entry member) bytes frame' decoded' sequence sender
      payload one) (fresh frame' decoded')

/-- A selected production has one sealed frame: every frame with the seal's sequence, sender and record encoding is that frame, and the send result carries the writer's optional bytes for it with the frame's sequence. -/
theorem produced_frame (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (result : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted)) (sealed : CtxRomAuth.CtxSuccessfulSeal)
    (produced : RawCtxSelectedProductionOrigins.Produced writer prior parent target nonce next kernel context result sealed) :
    ∃ (written : RawCtxReceive.DecodedFrame) (keyId : Std.U64) (advanced : RawCtxSelectedMessageReveals.Kernel),
      (∀ frame : RawCtxReceive.DecodedFrame, frame.sequence.val = sealed.input.context.ad.seq →
        frame.sender.val = sealed.input.context.ad.sid → frame.payload = sealed.record.encode → frame = written) ∧
      result = some (advanced, (writer written).map (fun out => ⟨out, keyId, written.sequence⟩)) := by
  obtain ⟨pending, _, actualNonce, width, record, _, rfl, rfl⟩ := produced
  refine ⟨_, _, _, fun frame sequence sender payload => ?_, rfl⟩
  rcases frame with ⟨frameSequence, frameSender, framePayload⟩
  simp only [RawCtxSelectedMessageSealing.selectedInput] at sequence sender payload
  simp only [RawCtxInterpretedSend.ready, RawCtxReceive.DecodedFrame.mk.injEq]
  exact ⟨UScalar.eq_of_val_eq sequence, UScalar.eq_of_val_eq sender, payload⟩

/-- A seal whose sealed frame's writer result is returned by the appended entry is transcribed. -/
theorem transcribed_sent (writer : RawCtxMixedShared.Writer) (log : List (Entry baseSpec S B)) (last : Entry baseSpec S B)
    (sealed : CtxRomAuth.CtxSuccessfulSeal) (written : RawCtxReceive.DecodedFrame) (keyId : Std.U64)
    (unique : ∀ frame : RawCtxReceive.DecodedFrame, frame.sequence.val = sealed.input.context.ad.seq →
      frame.sender.val = sealed.input.context.ad.sid → frame.payload = sealed.record.encode → frame = written)
    (returned : sent last = (writer written).map (fun out => ⟨out, keyId, written.sequence⟩)) :
    Transcribed writer (log ++ [last]) sealed := by
  intro frame sequence sender payload
  obtain rfl := unique frame sequence sender payload
  cases found : writer frame with
  | none => exact Or.inl rfl
  | some out =>
    refine Or.inr ⟨last, List.mem_append_right _ (List.mem_singleton_self last), ⟨out, keyId, frame.sequence⟩, ?_, rfl, rfl⟩
    rw [returned, found]
    rfl

/-- Every selected seal after one family request is transcribed in the transcript extended by that request and its reply: earlier seals keep their witness, and a new seal is produced by a Server or Beacon send whose reply carries the writer's bytes for the sealed frame. -/
theorem family_transcribed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (reply : (RawCtxProtocolRoles.SourceSpec S B).Range request) (before after : State)
    (supported : (some (reply, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request roles) before))
    (log : List (Entry baseSpec S B)) (transcribed : ∀ sealed ∈ before.seals, Transcribed writer log sealed) :
    ∀ sealed ∈ after.seals, Transcribed writer (log ++ [⟨.inl (.inl (.inl request)), reply⟩]) sealed := by
  intro sealed member
  rcases RawCtxSelectedProductionOrigins.family_produced source writer prior parent target nonce next sender route read request
    roles before after _ supported sealed member with old | ⟨produced, _⟩
  · exact transcribed_append writer log _ sealed (transcribed sealed old)
  rcases request with ⟨index, (⟨plaintext, kid⟩ | raw)⟩ | (⟨index, (plaintext | raw)⟩ | publicQuery)
  · obtain ⟨actual, serverProduced, published⟩ := produced
    unfold RawCtxSelectedProductionOrigins.ServerProduced at serverProduced
    split at serverProduced
    · exact False.elim serverProduced
    split at serverProduced
    · exact False.elim serverProduced
    obtain ⟨owned, ⟨_, sendResult, sendProduced, ownedEq⟩, actualEq⟩ := serverProduced
    obtain ⟨written, keyId, advanced, unique, resultEq⟩ := produced_frame writer prior parent target nonce next _ _ _ sealed
      sendProduced
    subst actualEq ownedEq resultEq
    simp only [Option.map_some] at published
    exact transcribed_sent writer log _ sealed written keyId unique (congrArg Prod.fst (Option.some.inj published))
  · exact False.elim produced
  · obtain ⟨actual, beaconProduced, published⟩ := produced
    unfold RawCtxSelectedProductionOrigins.BeaconProduced at beaconProduced
    split at beaconProduced
    · obtain ⟨owned, ⟨_, sendResult, sendProduced, ownedEq⟩, actualEq⟩ := beaconProduced
      obtain ⟨written, keyId, advanced, unique, resultEq⟩ := produced_frame writer prior parent target nonce next _ _ _ sealed
        sendProduced
      subst actualEq ownedEq resultEq
      simp only [Option.map_some] at published
      exact transcribed_sent writer log _ sealed written keyId unique (congrArg Prod.fst (Option.some.inj published))
    all_goals exact False.elim beaconProduced
  · exact False.elim produced
  · exact False.elim produced

end Accept

section Invariant
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedAuthenticationObserver
open PqxdhFirstBeaconRecordIntegrity RawCtxSelectedPlaintextOrigins
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)
variable {ι I D K X Response Shared A N C M P : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (kid : Std.U64)

/-- One owner operation (a send or a raw receive by the selected-message owner compiler, on any owner view of the kernel) moves `kernel` to `moved`. -/
def Moves (kernel moved : RawCtxSelectedMessageReveals.Kernel) : Prop :=
  ∃ (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner finalOwner : RawCtxChainOwner.State
    RawCtxSelectedMessageReveals.Kernel P) (reply : RawCtxMixedOwner.SourceSpec.Range query),
    owner.kernel = kernel ∧ some (reply, finalOwner) ∈ support (RawCtxSelectedOwnerCompiler.owner source writer prior parent
      target nonce next read sender query owner) ∧ finalOwner.kernel = moved

/-- The kernels reachable from `initial` by owner operations. -/
inductive Reach (initial : RawCtxSelectedMessageReveals.Kernel) : RawCtxSelectedMessageReveals.Kernel → Prop
  | base : Reach initial initial
  | step {kernel moved : RawCtxSelectedMessageReveals.Kernel} : Reach initial kernel →
      Moves (P := P) source writer prior parent target nonce next read kernel moved → Reach initial moved

/-- A family request either keeps the Server peer `kid` at `index` (absent peers stay absent) or moves its kernel by one owner operation. -/
theorem family_peer_step {I D K : Type} (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (reply : (RawCtxProtocolRoles.SourceSpec S B).Range request) (before after : State)
    (supported : (some (reply, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request roles) before))
    (found : RawCtxGenericRoleStorage.Peer RawCtxSelectedMessageReveals.Kernel P)
    (foundAfter : (finalRoles.1 index).server.peers kid = some found) :
    ∃ earlier, (roles.1 index).server.peers kid = some earlier ∧
      (found.kernel = earlier.kernel ∨ Moves (P := P) source writer prior parent target nonce next read earlier.kernel found.kernel) := by
  have syntactic : some (reply, finalRoles) ∈ support (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next
      sender route read request roles) := by
    rw [← monitor_erase (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
      request roles) before, support_map]
    exact ⟨_, supported, rfl⟩
  rw [RawCtxSelectedFamilyCompiler.family_cases] at syntactic
  rcases request with ⟨position, serverRequest⟩ | (⟨position, beaconRequest⟩ | publicRequest)
  · simp only [support_map, Set.mem_image] at syntactic
    obtain ⟨outcome, reached, published⟩ := syntactic
    rcases outcome with _ | ⟨serverReply, server⟩
    · cases published
    simp only [Option.map_some, Option.some.injEq] at published
    obtain ⟨_, rfl⟩ := published
    dsimp only at foundAfter
    by_cases same : position = index
    swap
    · rw [Function.update_of_ne (Ne.symm same) ] at foundAfter
      exact ⟨found, foundAfter, Or.inl rfl⟩
    have same' : index = position := same.symm
    subst same'
    rw [Function.update_self] at foundAfter
    have putStep : ∀ (target' : Std.U64) (ad : Pqxdh.Bytes) (peer : RawCtxGenericRoleStorage.Peer RawCtxSelectedMessageReveals.Kernel P)
        (sender' : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
        (outcome : Option (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P)),
        (roles.1 index).server.peers target' = some peer →
        outcome ∈ support (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read sender' query
          (RawCtxGenericServer.selectedOwner target' ad peer (roles.1 index).rawAttempts)) →
        ∀ (published : RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P),
        (∃ ownerReply finalOwner, outcome = some (ownerReply, finalOwner) ∧
          published = ⟨RawCtxGenericServer.putPeer (roles.1 index).server target' peer finalOwner.kernel, finalOwner.rawAttempts⟩) →
        published.server.peers kid = some found →
        ∃ earlier, (roles.1 index).server.peers kid = some earlier ∧
          (found.kernel = earlier.kernel ∨ Moves (P := P) source writer prior parent target nonce next read earlier.kernel found.kernel) := by
      rintro target' ad peer sender' query outcome peerFound ownerFound published ⟨ownerReply, finalOwner, rfl, rfl⟩ publishedFound
      simp only [RawCtxGenericServer.putPeer] at publishedFound
      by_cases same : kid = target'
      · subst same
        rw [Function.update_self] at publishedFound
        obtain rfl := Option.some.inj publishedFound
        exact ⟨peer, peerFound, Or.inr ⟨sender', query, _, finalOwner, ownerReply, rfl, ownerFound, rfl⟩⟩
      · rw [Function.update_of_ne same] at publishedFound
        exact ⟨found, publishedFound, Or.inl rfl⟩
    rcases serverRequest with ⟨plaintext, target'⟩ | raw
    · rw [RawCtxSelectedRoleCompiler.server_send_cases] at reached
      cases adFound : RawCtxGenericServer.peerAssociatedData (roles.1 index).server target' with
      | none =>
        simp only [adFound, support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
        rw [show server = roles.1 index from congrArg Prod.snd reached] at foundAfter
        exact ⟨found, foundAfter, Or.inl rfl⟩
      | some ad =>
        cases peerFound : (roles.1 index).server.peers target' with
        | none =>
          simp only [adFound, peerFound, support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
          rw [show server = roles.1 index from congrArg Prod.snd reached] at foundAfter
          exact ⟨found, foundAfter, Or.inl rfl⟩
        | some peer =>
          simp only [adFound, peerFound, support_map, Set.mem_image] at reached
          obtain ⟨outcome, ownerFound, mapped⟩ := reached
          rcases outcome with _ | ⟨ownerReply, finalOwner⟩
          · cases mapped
          simp only [Option.map_some, Option.some.injEq] at mapped
          exact putStep target' ad peer _ _ _ peerFound ownerFound server ⟨ownerReply, finalOwner, rfl, (congrArg Prod.snd mapped).symm⟩ foundAfter
    · rw [RawCtxSelectedRoleCompiler.server_raw_cases] at reached
      cases routed : route raw with
      | none =>
        simp only [routed, support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
        rw [show server = { roles.1 index with rawAttempts := (roles.1 index).rawAttempts + 1 } from
          congrArg Prod.snd reached] at foundAfter
        exact ⟨found, foundAfter, Or.inl rfl⟩
      | some target' =>
        cases adFound : RawCtxGenericServer.peerAssociatedData (roles.1 index).server target' with
        | none =>
          simp only [routed, adFound, support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
          rw [show server = { roles.1 index with rawAttempts := (roles.1 index).rawAttempts + 1 } from
            congrArg Prod.snd reached] at foundAfter
          exact ⟨found, foundAfter, Or.inl rfl⟩
        | some ad =>
          cases peerFound : (roles.1 index).server.peers target' with
          | none =>
            simp only [routed, adFound, peerFound, support_pure, Set.mem_singleton_iff, Option.some.injEq,
              ] at reached
            rw [show server = { roles.1 index with rawAttempts := (roles.1 index).rawAttempts + 1 } from
              congrArg Prod.snd reached] at foundAfter
            exact ⟨found, foundAfter, Or.inl rfl⟩
          | some peer =>
            simp only [routed, adFound, peerFound, support_map, Set.mem_image] at reached
            obtain ⟨outcome, ownerFound, mapped⟩ := reached
            rcases outcome with _ | ⟨ownerReply, finalOwner⟩
            · cases mapped
            simp only [Option.map_some, Option.some.injEq] at mapped
            exact putStep target' ad peer _ _ _ peerFound ownerFound server ⟨ownerReply, finalOwner, rfl, (congrArg Prod.snd mapped).symm⟩
              foundAfter
  · simp only [support_map, Set.mem_image] at syntactic
    obtain ⟨outcome, _, published⟩ := syntactic
    rcases outcome with _ | ⟨beaconReply, beacon⟩
    · cases published
    simp only [Option.map_some, Option.some.injEq] at published
    obtain ⟨_, rfl⟩ := published
    exact ⟨found, foundAfter, Or.inl rfl⟩
  · simp only [support_map, Set.mem_image] at syntactic
    obtain ⟨publicReply, _, published⟩ := syntactic
    simp only [Option.some.injEq, Prod.mk.injEq] at published
    obtain ⟨_, rfl⟩ := published
    exact ⟨found, foundAfter, Or.inl rfl⟩

/-- The post invariant along the transcript `log`: the observer history is consistent (`Good`), a canonical forgery in the transcript is already an observer win, every selected seal is transcribed, and the Server peer `kid` at `index` is reachable from `start`. -/
structure Inv (key : CtxRomAuth.CtxKey) (start : RawCtxSelectedMessageReveals.Kernel) (log : List (Entry baseSpec S B))
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState) : Prop where
  good : Good (RawCtxUniversalDecoder.decoder read) source.crypto key component
  forged : CanonicalForged index route read writer kid log → won (RawCtxUniversalDecoder.decoder read) component.1 = true
  transcribed : ∀ sealed ∈ component.1.seals, Transcribed writer log sealed
  peer : ∀ found, (state.1.roles.1.1 index).server.peers kid = some found →
    Reach (P := P) source writer prior parent target nonce next read start found.kernel

end Invariant

section Preservation
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedAuthenticationObserver
open PqxdhFirstBeaconRecordIntegrity RawCtxSelectedPlaintextOrigins
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)
variable {ι I D K X Response Shared A N C M P : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (kid : Std.U64) (key : CtxRomAuth.CtxKey) (start : RawCtxSelectedMessageReveals.Kernel)

local notation "observer" => observed true (RawCtxUniversalDecoder.decoder read) source.crypto key

/-- A family request with a reply preserves the invariant, given the writer premise and that no kernel reachable by the Server peer opens its first message with known material. -/
theorem inv_family (writable : ReadWritable writer read)
    (hidden : ∀ kernel, Reach (P := P) source writer prior parent target nonce next read start kernel →
      ¬ FirstKnown prior parent target nonce next kernel)
    (request : (RawCtxProtocolRoles.SourceSpec S B).Domain) (log : List (Entry baseSpec S B))
    (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component : State × SourceState)
    (inv : Inv source writer prior parent target nonce next route read index kid key start log state component)
    (reply : (RawCtxProtocolRoles.SourceSpec S B).Range request)
    (finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) (after : State × SourceState)
    (supported : (some (reply, finalRoles), after) ∈ support ((simulateQ observer (RawCtxSelectedFamilyCompiler.family source
      writer prior parent target nonce next sender route read request state.1.roles.1)).run component)) :
    Inv source writer prior parent target nonce next route read index kid key start
      (log ++ [⟨.inl (.inl (.inl request)), reply⟩])
      ({ state.1 with roles := (finalRoles, RawCtxSelectedMessageFamily.tick state.1.roles.2) }, state.2) after := by
  have monitored := observed_monitor _ _ _ _ component _ supported
  have good := schedule_good (RawCtxUniversalDecoder.decoder read) source.crypto key _ component inv.good _ supported
  refine ⟨good, fun forged => ?_, family_transcribed source writer prior parent target nonce next sender route read request
    state.1.roles.1 finalRoles reply component.1 after.1 monitored log inv.transcribed, fun found peerFound => ?_⟩
  · rcases canonical_forged_append index route read writer kid log _ forged with old | ⟨raw, decrypted, opened, routed, one, fresh⟩
    · exact observed_won _ _ _ _ component (inv.forged old) _ supported
    · rcases request with ⟨position, (⟨plaintext, target⟩ | bytes)⟩ | other
      · simp only [serverOpen, reduceCtorEq] at opened
      · simp only [serverOpen, Option.some.injEq, Prod.mk.injEq] at opened
        obtain ⟨rfl, rfl, rfl⟩ := opened
        exact server_accept_wins source writer prior parent target nonce next sender route read writable position kid raw
          state.1.roles.1 finalRoles component.1 after.1 decrypted monitored routed one
          (fun found peerFound => hidden _ (inv.peer found peerFound)) log inv.transcribed good.2.2 fresh
      · simp only [serverOpen, reduceCtorEq] at opened
  · obtain ⟨earlier, earlierFound, same | moved⟩ := family_peer_step source writer prior parent target nonce next sender route read
      index kid request state.1.roles.1 finalRoles reply component.1 after.1 monitored found peerFound
    · rw [same]
      exact inv.peer earlier earlierFound
    · exact Reach.step (inv.peer earlier earlierFound) moved

/-- A step whose transcript entry is not a Server raw receive preserves the invariant when it keeps the observer seals, keeps observer wins, keeps the Server roles and yields a consistent observer. -/
theorem inv_quiet (log : List (Entry baseSpec S B)) (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B)
    (component : State × SourceState)
    (inv : Inv source writer prior parent target nonce next route read index kid key start log state component)
    (last : Entry baseSpec S B) (unopened : serverOpen last = none)
    (state' : PqxdhSelectedPostCompiler.State M P I D K A N C S B) (component' : State × SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) source.crypto key component')
    (seals : component'.1.seals = component.1.seals)
    (winning : won (RawCtxUniversalDecoder.decoder read) component.1 = true →
      won (RawCtxUniversalDecoder.decoder read) component'.1 = true)
    (servers : state'.1.roles.1.1 = state.1.roles.1.1) :
    Inv source writer prior parent target nonce next route read index kid key start (log ++ [last]) state' component' := by
  refine ⟨good, fun forged => ?_, fun sealed member => ?_, fun found peerFound => ?_⟩
  · rcases canonical_forged_append index route read writer kid log last forged with old | ⟨raw, decrypted, opened, _⟩
    · exact winning (inv.forged old)
    · rw [unopened] at opened
      cases opened
  · rw [seals] at member
    exact transcribed_append writer log _ sealed (inv.transcribed sealed member)
  · rw [servers] at peerFound
    exact inv.peer found peerFound

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl (PqxdhPrivateKemSource.SelectorSpec baseSpec) (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

local notation "compiled" => PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target
  nonce next sender route read

/-- Every answered request of the compiled post preserves the invariant, extending the transcript by the request and its reply, given the writer premise and that no kernel reachable by the Server peer opens its first message with known material. -/
theorem inv_step (writable : ReadWritable writer read)
    (hidden : ∀ kernel, Reach (P := P) source writer prior parent target nonce next read start kernel →
      ¬ FirstKnown prior parent target nonce next kernel)
    (query : (PqxdhInitialGenericPost.Spec (PqxdhPrivateKemSource.SelectorSpec baseSpec) S B).Domain)
    (log : List (Entry baseSpec S B)) (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B)
    (component : State × SourceState)
    (inv : Inv source writer prior parent target nonce next route read index kid key start log state component)
    (result : Option ((PqxdhInitialGenericPost.Spec (PqxdhPrivateKemSource.SelectorSpec baseSpec) S B).Range query) ×
      (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((compiled query).run) (state, component)))
    (reply : (PqxdhInitialGenericPost.Spec (PqxdhPrivateKemSource.SelectorSpec baseSpec) S B).Range query)
    (returned : result.1 = some reply) :
    Inv source writer prior parent target nonce next route read index kid key start (log ++ [⟨query, reply⟩])
      result.2.1 result.2.2 := by
  rcases query with ((request | request) | request) | request
  · obtain ⟨familyReply, after, found, rfl⟩ := family_support pre application initial selector aux source writer prior parent
      target nonce next sender route read key request state component result supported
    rcases familyReply with _ | ⟨value, finalRoles⟩
    · cases returned
    · obtain rfl : value = reply := Option.some.inj returned
      exact inv_family source writer prior parent target nonce next sender route read index kid key start writable hidden request
        log state component inv value finalRoles after found
  · obtain ⟨roles, localSame, same⟩ := reveal_support pre application initial selector aux source writer prior parent target nonce
      next sender route read key request state component result supported
    refine inv_quiet source writer prior parent target nonce next route read index kid key start log state component inv
      _ rfl result.2.1 result.2.2 (same ▸ inv.good) (by rw [same]) (by rw [same]; exact id) (congrArg Prod.fst roles)
  · obtain ⟨inner, after, found, rfl⟩ := selector_support pre application initial selector aux source writer prior parent target
      nonce next sender route read key request state component result supported
    exact inv_quiet source writer prior parent target nonce next route read index kid key start log state component inv
      _ rfl _ after (schedule_good _ _ _ _ component inv.good _ found)
      (observed_seals _ _ _ _ (PqxdhFirstRecordNonceStop.external_nonseal pre application initial selector aux _ state.2)
        component _ found)
      (fun winning => observed_won _ _ _ _ component winning _ found) rfl
  · cases request with
    | finish position raw =>
      obtain ⟨inner, after, found, rfl⟩ := finish_support pre application initial selector aux source writer prior parent target
        nonce next sender route read key position raw state component result supported
      exact inv_quiet source writer prior parent target nonce next route read index kid key start log state component inv
        _ rfl _ after (schedule_good _ _ _ _ component inv.good _ found)
        (observed_seals _ _ _ _ (PqxdhFirstRecordNonceStop.finish_nonseal pre application initial selector aux prior parent
          target nonce next read raw _ state.2) component _ found)
        (fun winning => observed_won _ _ _ _ component winning _ found) rfl

/-- The invariant holds at the end of every answered run of the compiled post on a recorded adaptive program, with the recorder's final transcript. -/
theorem inv_post (writable : ReadWritable writer read)
    (hidden : ∀ kernel, Reach (P := P) source writer prior parent target nonce next read start kernel →
      ¬ FirstKnown prior parent target nonce next kernel)
    {Result : Type} (program : OracleComp (PostSpec baseSpec S B) Result)
    (log : List (Entry baseSpec S B)) (state : PqxdhSelectedPostCompiler.State M P I D K A N C S B)
    (component : State × SourceState)
    (inv : Inv source writer prior parent target nonce next route read index kid key start log state component)
    (result : Option (Result × List (Entry baseSpec S B)) ×
      (PqxdhSelectedPostCompiler.State M P I D K A N C S B × (State × SourceState)))
    (supported : result ∈ support (evaluate observer ((simulateQ compiled ((simulateQ recorder program).run log)).run)
      (state, component)))
    (value : Result × List (Entry baseSpec S B)) (returned : result.1 = some value) :
    Inv source writer prior parent target nonce next route read index kid key start value.2 result.2.1 result.2.2 := by
  induction program using OracleComp.inductionOn generalizing log state component result with
  | pure output =>
    simp only [simulateQ_pure, StateT.run_pure, OptionT.run_pure, pure_evaluate] at supported
    change result ∈ support (pure (some (output, log), (state, component)) : ProbComp _) at supported
    rw [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    obtain rfl := Option.some.inj returned
    exact inv
  | query_bind query continuation ih =>
    have recorded : (simulateQ recorder (liftM ((PostSpec baseSpec S B).query query) >>= continuation)).run log =
        (liftM ((PostSpec baseSpec S B).query query) >>= fun reply =>
          (simulateQ recorder (continuation reply)).run (log ++ [⟨query, reply⟩])) := by
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [recorder, StateT.run, bind_assoc, pure_bind]
    rw [recorded, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, bind_evaluate] at supported
    rw [state_bind_apply, mem_support_bind_iff] at supported
    obtain ⟨middle, first, rest⟩ := supported
    rcases answered : middle.1 with _ | reply
    · rw [answered] at rest
      simp only [Option.elim, pure_evaluate] at rest
      change result ∈ support (pure (none, middle.2) : ProbComp _) at rest
      rw [support_pure, Set.mem_singleton_iff] at rest
      rw [rest] at returned
      cases returned
    · rw [answered] at rest
      exact ih reply _ middle.2.1 middle.2.2 (inv_step source writer prior parent target nonce next sender route read index kid
        key start pre application initial selector aux writable hidden query log state component inv middle first reply answered)
        result rest returned

end Preservation

section BuilderPeer
open PqxdhInitialGenericPublication
variable {Kernel Metadata PeerMetadata Consumed L κ : Type} {spec : OracleSpec κ}

/-- The first send of `calls` can move `kernel` to `advanced` for some context and local states. -/
def SendMoves (calls : RawCtxChainOwner.Calls Kernel (StateT L (OracleComp spec))) (kernel advanced : Kernel) : Prop :=
  ∃ context start finish sent, ((advanced, sent), finish) ∈ support ((calls.send kernel context).run start)

/-- A successful registration reply installs its key identifier with a kernel that the first send moved from an initial kernel. -/
def Installs (calls : RawCtxChainOwner.Calls Kernel (StateT L (OracleComp spec))) (initial : RustM Kernel)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata Consumed)) : Prop :=
  ∀ response state, result = ok (some response, state) → ∃ found, state.server.peers response.keyId = some found ∧
    ∃ kernel, initial = ok kernel ∧ SendMoves calls kernel found.kernel

/-- The registration first-send tail installs the advanced kernel at the candidate key identifier. -/
theorem after_installs (calls : RawCtxChainOwner.Calls Kernel (StateT L (OracleComp spec)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT L (OracleComp spec)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (start : L)
    (result : (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata Consumed) × L)
    (supported : result ∈ support ((afterInitialization calls aux candidate authenticated kernel metadata state).run start))
    (response : PqxdhServerRegistrationPublication.Response) (replied : result.1.1 = some response) :
    ∃ found, result.1.2.server.peers response.keyId = some found ∧ SendMoves calls kernel found.kernel := by
  unfold afterInitialization at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨sent, sentFound, erased, _, rest⟩ := supported
  rcases sent with ⟨⟨advanced, encrypted⟩, afterSend⟩
  cases encrypted with
  | none =>
    simp only [StateT.run_pure, mem_support_pure_iff] at rest
    subst rest
    cases replied
  | some encrypted =>
    simp only [StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨serialized, _, rest⟩ := rest
    rcases serialized with ⟨_ | serialized, afterWrite⟩
    · simp only [StateT.run_pure, mem_support_pure_iff] at rest
      subst rest
      cases replied
    · simp only [StateT.run_pure, mem_support_pure_iff] at rest
      subst rest
      obtain rfl := Option.some.inj replied
      exact ⟨⟨candidate.beacon_identity_public_key, advanced, metadata⟩, by simp only [publish, Function.update_self],
        _, start, afterSend, _, sentFound⟩

/-- The registration candidate admission and first-send program installs only first-send moves of the initial kernel. -/
theorem candidate_installs (calls : RawCtxChainOwner.Calls Kernel (StateT L (OracleComp spec)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT L (OracleComp spec)))
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (start : L)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata Consumed) × L)
    (supported : result ∈ support ((PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state).run start)) :
    Installs calls initial result.1 := by
  intro response final replied
  unfold PqxdhInitialGenericBuilder.candidate at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨valid, _, rest⟩ := supported
  have none_case : ∀ {start' : L}, result ∈ support ((pure (ok (none, state)) :
      StateT L (OracleComp spec) (RustM (Option PqxdhServerRegistrationPublication.Response ×
        State Kernel Metadata PeerMetadata Consumed))).run start') → False := by
    intro start' reached
    simp only [StateT.run_pure, mem_support_pure_iff] at reached
    subst reached
    simp at replied
  have stop_case : ∀ {start' : L} (stopped : RustM (Option PqxdhServerRegistrationPublication.Response ×
      State Kernel Metadata PeerMetadata Consumed)), (∀ value, stopped ≠ ok value) → result ∈ support ((pure stopped :
      StateT L (OracleComp spec) _).run start') → False := by
    intro start' stopped notOk reached
    simp only [StateT.run_pure, mem_support_pure_iff] at reached
    subst reached
    exact notOk _ replied
  by_cases checked : (!valid.1) = true
  · rw [ite_eq_left checked] at rest
    exact (none_case rest).elim
  rw [ite_eq_right checked, StateT.run_bind, mem_support_bind_iff] at rest
  obtain ⟨reserved, _, rest⟩ := rest
  by_cases reservedFlag : (!reserved.1) = true
  · rw [ite_eq_left reservedFlag] at rest
    exact (none_case rest).elim
  rw [ite_eq_right reservedFlag] at rest
  cases initial with
  | fail error => exact (stop_case _ (fun _ => by simp) rest).elim
  | div => exact (stop_case _ (fun _ => by simp) rest).elim
  | ok kernel =>
    simp only [PqxdhInitialGenericBuilder.continueRust] at rest
    by_cases empty : List.isEmpty (data.getD PqxdhServerRegistrationPublication.registrationWitness) = true
    · rw [ite_eq_left empty] at rest
      exact (none_case rest).elim
    rw [ite_eq_right empty] at rest
    by_cases bounded : 8 + List.length (data.getD PqxdhServerRegistrationPublication.registrationWitness) ≤ Usize.max
    swap
    · rw [ite_eq_right bounded] at rest
      exact (none_case rest).elim
    rw [ite_eq_left bounded, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨allocated, _, rest⟩ := rest
    by_cases allocatedFlag : (!allocated.1) = true
    · rw [ite_eq_left allocatedFlag] at rest
      exact (none_case rest).elim
    rw [ite_eq_right allocatedFlag] at rest
    cases bound : candidate.key_id_binding with
    | fail error =>
      simp only [bound] at rest
      exact (stop_case _ (fun _ => by simp) rest).elim
    | div =>
      simp only [bound] at rest
      exact (stop_case _ (fun _ => by simp) rest).elim
    | ok binding =>
      simp only [bound] at rest
      rw [StateT.run_map, support_map] at rest
      obtain ⟨tail, tailFound, rfl⟩ := rest
      simp only [RustM.ok.injEq] at replied
      obtain ⟨found, peers, moves⟩ := after_installs calls aux candidate _ kernel metadata state _ tail tailFound response
        (by rw [replied])
      refine ⟨found, ?_, kernel, rfl, moves⟩
      rw [replied] at peers
      exact peers

/-- The Ready registration builder installs only first-send moves of the initial kernel. -/
theorem ready_installs (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (calls : RawCtxChainOwner.Calls Kernel (StateT L (OracleComp spec)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT L (OracleComp spec)))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (start : L)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata PeerMetadata Consumed) × L)
    (supported : result ∈ support ((PqxdhInitialGenericBuilder.readyBuild source calls aux initial binding ready metadata
      state).run start)) :
    Installs calls initial result.1 := by
  intro response final replied
  have stop_case : ∀ (stopped : RustM (Option PqxdhServerRegistrationPublication.Response ×
      State Kernel Metadata PeerMetadata Consumed)), (stopped ≠ ok (some response, final)) → result ∈ support ((pure stopped :
      StateT L (OracleComp spec) _).run start) → False := by
    intro stopped notOk reached
    simp only [StateT.run_pure, mem_support_pure_iff] at reached
    subst reached
    exact notOk replied
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild at supported
  cases following : pqxdh.server_next_key_id state.control with
  | fail error =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    exact (stop_case _ (by simp) supported).elim
  | div =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    exact (stop_case _ (by simp) supported).elim
  | ok next =>
    simp only [following, PqxdhInitialGenericBuilder.continueRust] at supported
    rcases next with next | error
    swap
    · exact (stop_case _ (by simp) supported).elim
    simp only at supported
    generalize PqxdhRegistrationInputs.prepare _ _ _ _ = prepared at supported
    rcases prepared with (candidate | error) | error | _
    · exact candidate_installs calls aux initial candidate _ metadata state start result supported response final replied
    · exact (stop_case _ (by simp) supported).elim
    · exact (stop_case _ (by simp) supported).elim
    · exact (stop_case _ (by simp) supported).elim

end BuilderPeer

section Built
open PqxdhNativeSharedPrefix PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64)

/-- A first-send move of the compiled Server builder is the kernel of a compiled selected send outcome, or the unchanged kernel when that send stops. -/
theorem compiled_moves (kernel advanced : RawCtxSelectedMessageReveals.Kernel)
    (moves : SendMoves (PqxdhFirstBeaconRecordCtx.compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce
      next) kernel advanced) :
    ∃ context, ∃ outcome ∈ support (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context),
      (outcome.getD (kernel, none)).1 = advanced := by
  obtain ⟨context, start, finish, sent, found⟩ := moves
  simp only [PqxdhFirstBeaconRecordCtx.compiledCalls, StateT.run, support_map, Set.mem_image] at found
  obtain ⟨outcome, reached, same⟩ := found
  exact ⟨context, outcome, reached, congrArg (fun value => value.1.1) same⟩

/-- A successful compiled first Server builder installs the replied key identifier at the Server `index` with a kernel reached by one compiled send from the initial kernel. -/
theorem build_installs (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (start : Local A N C)
    (result : (RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhSelectedPostCompiler.Front M P I D K S B) ×
      Local A N C)
    (supported : result ∈ support (((PqxdhFirstBeaconRecordCtx.compiledBuild pre application initial selector aux source writer
      prior parent target nonce next sender initialKernel index metadata ready).run front).run start))
    (response : PqxdhServerRegistrationPublication.Response) (replied : result.1.1 = ok (some response)) :
    ∃ found, (result.1.2.roles.1.1 index).server.peers response.keyId = some found ∧ ∃ kernel, initialKernel = ok kernel ∧
      ∃ context, ∃ outcome ∈ support (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context),
        (outcome.getD (kernel, none)).1 = found.kernel := by
  simp only [PqxdhFirstBeaconRecordCtx.compiledBuild, StateT.run] at supported
  rw [state_map_apply, support_map] at supported
  obtain ⟨built, reached, rfl⟩ := supported
  dsimp only at replied ⊢
  rcases outcome : built.1 with value | error | _
  · rw [outcome] at replied
    simp only [PqxdhSelectedFirstRecord.reinstallServer, RustM.ok.injEq] at replied ⊢
    obtain ⟨found, peers, kernel, initialized, moves⟩ := ready_installs source _ _ initialKernel _ ready metadata _ start built reached
      response value.2 (by rw [outcome, ← replied])
    obtain ⟨context, sent, sentFound, same⟩ := compiled_moves source writer prior parent target nonce next kernel found.kernel moves
    refine ⟨found, ?_, kernel, initialized, context, sent, sentFound, same⟩
    simp only [PqxdhSelectedFirstRecord.installServer, Function.update_self]
    exact peers
  · rw [outcome] at replied
    simp [PqxdhSelectedFirstRecord.reinstallServer] at replied
  · rw [outcome] at replied
    simp [PqxdhSelectedFirstRecord.reinstallServer] at replied

/-- When every first send of the initial kernel is known, an observed run of the compiled first Server builder keeps a consistent observer and adds no selected seal. -/
theorem built_clean (key : CtxRomAuth.CtxKey) (read : RawCtxReceive.FrameDecoder)
    (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (start : Local A N C)
    (known : ∀ kernel, initialKernel = .ok kernel → ∀ context,
      PqxdhFirstBeaconRecordCtx.KnownSend prior parent target nonce next kernel context)
    (component : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder read) source.crypto key component)
    (built : ((RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhSelectedPostCompiler.Front M P I D K S B) ×
      Local A N C) × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : built ∈ support ((simulateQ (RawCtxSelectedAuthenticationObserver.observed true
      (RawCtxUniversalDecoder.decoder read) source.crypto key) (((PqxdhFirstBeaconRecordCtx.compiledBuild pre application initial
        selector aux source writer prior parent target nonce next sender initialKernel index metadata ready).run front).run
          start)).run component)) :
    RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder read) source.crypto key built.2 ∧
      built.2.1.seals = component.1.seals := by
  have goodBuilt := RawCtxSelectedPlaintextOrigins.schedule_good _ _ _ _ component good built supported
  refine ⟨goodBuilt, clean_seals _ _ _ component built.2 good goodBuilt ?_⟩
  have related := PqxdhFirstBeaconRecordCtx.build_rel pre application initial selector aux source writer prior parent key target
    nonce next read sender initialKernel index metadata ready front known
  refine (related (start, component.2)).2 (PqxdhSelectedStateInterpreter.pair (built.1, built.2.2)) ?_
  simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image]
  exact ⟨_, observed_component _ _ _ _ component built supported, rfl⟩

end Built

section SlotReach
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxSelectedMessageKey
open RawCtxSelectedReceiveReceipt RawCtxMaterialInterpretation
variable (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (key : RootOutput)

/-- The fixed concrete interpreter of the selected derivation with the hidden message key realized by `key`. -/
noncomputable def slotExecute : KdfInterpreter :=
  RawCtxFunctionalFamily.execute (RawCtxSelectedParentPrivatePatch.privatePatch prior target (RawCtxSelectedMessageKdf.response key nonce next))

/-- The concrete interpreter decodes to the selected derivation with its material interpreted by `key`. -/
theorem slot_decode (request : SymmetricRatchetKdfRequest) :
    RawCtxInterpretedReceive.decodeResponse (slotExecute prior target nonce next key request) =
      ((RawCtxSelectedSendCompiler.deriveValue prior none target nonce next request).1,
        interpret key (RawCtxSelectedSendCompiler.deriveValue prior none target nonce next request).2) :=
  RawCtxSelectedMessageKdf.step_exact prior key target nonce next request

/-- A recording opening callback: it returns `reply` and stores the native opening request it received. -/
def recordOpen (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    ReceiveOpen RawCtxWholeOwner.OpenContext →
      StateT (Option (ReceiveOpen RawCtxWholeOwner.OpenContext)) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted) :=
  fun pending _ => pure (reply, some pending)

/-- Selected-material receive callbacks matching `recordOpen` through the interpretation by `key`. -/
noncomputable def slotLabels (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Slot RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (Option (ReceiveOpen RawCtxWholeOwner.OpenContext)) ProbComp)
  | .inl request => pure (RawCtxSelectedSendCompiler.deriveValue prior none target nonce next request)
  | .inr pending => recordOpen reply (RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending))

/-- The concrete receive of the interpreted kernel is the interpreted selected-material receive. -/
theorem slot_native (reply : core.option.Option RawCtxWholeOwner.Decrypted) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxMaterialPositions.bareReceiveImpl (slotExecute prior target nonce next key) (recordOpen reply))
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key entry) sequence context) =
      (fun result => (ConcreteRatchetKernel.mk (mapRefined (interpret key) result.1), result.2)) <$>
        simulateQ (slotLabels prior target nonce next key reply) (RawCtxInterpretedReceive.receive entry sequence context) := by
  refine RawCtxInterpretedReceive.receive_interpreted (interpret key) _ _ (fun request => ?_) (fun pending => rfl) entry sequence
    context
  change RawCtxInterpretedReceive.decodeResponse <$> (pure (slotExecute prior target nonce next key request) :
      StateT (Option (ReceiveOpen RawCtxWholeOwner.OpenContext)) ProbComp _) =
    (fun reply => (reply.1, interpret key reply.2)) <$> (pure (RawCtxSelectedSendCompiler.deriveValue prior none target nonce next
      request) : StateT (Option (ReceiveOpen RawCtxWholeOwner.OpenContext)) ProbComp _)
  rw [map_pure, map_pure, slot_decode]

/-- Any receive callbacks whose derivation is the selected derivation run the terminal of the receive driver. -/
theorem terminal_any {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Slot RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m)
    (kdf : ∀ request, handler (.inl request) = pure (RawCtxSelectedSendCompiler.deriveValue prior none target nonce next request))
    (effect : SourceEffect) :
    simulateQ handler (RawCtxInterpretedReceive.program effect) =
      match terminal prior none target nonce next effect with
      | .rejected kernel => pure (kernel, .None)
      | .opening pending => RawCtxInterpretedReceive.normalFinish pending <$> handler (.inr pending) := by
  generalize depth : RawCtxInterpretedReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry context => simp only [RawCtxInterpretedReceive.program, terminal, simulateQ_pure]
    | openRequested pending =>
      simp only [RawCtxInterpretedReceive.program, terminal, bind_pure_comp, simulateQ_map, simulateQ_spec_query]
    | kdfRequested pending =>
      simp only [RawCtxInterpretedReceive.program, terminal, simulateQ_bind, simulateQ_spec_query, kdf, pure_bind]
      exact ih _ (depth ▸ RawCtxInterpretedReceive.normalResume_rank pending _) _ rfl

/-- The recording selected-material receive runs its terminal. -/
theorem slot_terminal (reply : core.option.Option RawCtxWholeOwner.Decrypted) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (slotLabels prior target nonce next key reply) (RawCtxInterpretedReceive.receive entry sequence context) =
      match terminal prior none target nonce next (RawCtxInterpretedReceive.normalBegin entry sequence context) with
      | .rejected kernel => pure (kernel, .None)
      | .opening pending => RawCtxInterpretedReceive.normalFinish pending <$> slotLabels prior target nonce next key reply (.inr pending) :=
  terminal_any prior target nonce next _ (fun _ => rfl) _

/-- A compiled selected receive outcome is its terminal rejection or the terminal opening finished with some reply. -/
theorem compiled_receive_cases (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (outcome : RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : outcome ∈ support (RawCtxSelectedReceiveCompiler.receive prior none target nonce next read expected entry sequence
      context)) :
    (∃ kernel, terminal prior none target nonce next (RawCtxInterpretedReceive.normalBegin entry sequence context) = .rejected kernel ∧
      outcome = (kernel, .None)) ∨
    ∃ pending reply, terminal prior none target nonce next (RawCtxInterpretedReceive.normalBegin entry sequence context) =
      .opening pending ∧ outcome = RawCtxInterpretedReceive.normalFinish pending reply := by
  simp only [RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive, ← QueryImpl.simulateQ_compose,
    RawCtxInterpretedReceive.receive] at supported
  change outcome ∈ support (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior none target nonce next read expected)
    (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalBegin entry sequence context))) at supported
  rw [program_terminal] at supported
  cases reached : terminal prior none target nonce next (RawCtxInterpretedReceive.normalBegin entry sequence context) with
  | rejected kernel =>
    rw [reached] at supported
    exact Or.inl ⟨kernel, rfl, (mem_support_pure_iff _ _).mp supported⟩
  | opening pending =>
    rw [reached, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact Or.inr ⟨pending, reply, rfl, rfl⟩

/-- A compiled selected receive keeps the interpreted kernel reachable from its directional origins. -/
theorem receive_reach {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (valid : RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key entry))
    (outcome : RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : outcome ∈ support (RawCtxSelectedReceiveCompiler.receive prior none target nonce next read expected entry sequence
      context)) :
    RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key outcome.1) := by
  have concrete : ∀ (reply : core.option.Option RawCtxWholeOwner.Decrypted)
      (result : (RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
        Option (ReceiveOpen RawCtxWholeOwner.OpenContext)),
      result ∈ support ((simulateQ (slotLabels prior target nonce next key reply)
        (RawCtxInterpretedReceive.receive entry sequence context)).run none) →
      RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
        (RawCtxSelectedMessageReveals.nativeKernel key result.1.1) := by
    intro reply result found
    refine RawCtxFunctionalPositions.receive cr (slotExecute prior target nonce next key) sendOrigin receiveOrigin _ valid sequence
      context (recordOpen reply) none ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), result.2) ?_
    rw [slot_native, StateT.run_map, support_map]
    exact ⟨result, found, rfl⟩
  rcases compiled_receive_cases prior target nonce next read expected entry sequence context outcome supported with
    ⟨kernel, reached, rfl⟩ | ⟨pending, reply, reached, rfl⟩
  · refine concrete .None ((kernel, .None), none) ?_
    rw [slot_terminal, reached]
    simp
  · refine concrete reply (RawCtxInterpretedReceive.normalFinish pending reply,
      some (RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending))) ?_
    rw [slot_terminal, reached, StateT.run_map]
    simp [slotLabels, recordOpen, StateT.run]

/-- A compiled selected send keeps the interpreted kernel reachable from its directional origins; a stopped send keeps the kernel. -/
theorem send_reach {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (entry : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxSourceSend.SealContext)
    (valid : RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key entry))
    (outcome : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : outcome ∈ support (RawCtxSelectedSendCompiler.send source writer prior none target nonce next entry context)) :
    RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key (outcome.getD (entry, none)).1) := by
  obtain ⟨advanced, output, sealed, reach⟩ := sealNext_preserves_reachability cr (slotExecute prior target nonce next key) sendOrigin
    receiveOrigin _ valid context (fun _ _ _ => (core.option.Option.None : core.option.Option Unit))
  have began : begin_send (RawCtxSelectedMessageReveals.nativeKernel key entry) context =
      ok (RawCtxInterpretedSend.nativeStart (RawCtxInterpretedSend.mapStart (interpret key)
        (RawCtxInterpretedSend.normalBegin entry context))) := by
    rw [RawCtxSourceSend.beginSend_exact, RawCtxSelectedMessageReveals.nativeKernel, RawCtxInterpretedSend.normalBegin_native,
      RawCtxInterpretedSend.normalBegin_map]
  rw [RawCtxSelectedSendCompiler.send_cases] at supported
  cases started : RawCtxInterpretedSend.normalBegin entry context with
  | exhausted final ctx =>
    rw [started] at supported began
    rw [mem_support_pure_iff] at supported
    subst supported
    simp only [sealNext, began, RawCtxInterpretedSend.mapStart, RawCtxInterpretedSend.nativeStart, bind_tc_ok] at sealed
    obtain ⟨rfl, _⟩ := Prod.mk.inj (RustM.ok.inj sealed)
    exact reach
  | requested pending =>
    rw [started] at supported began
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨sealedOpt, _, rfl⟩ := supported
    have value : advanced = RawCtxSelectedMessageReveals.nativeKernel key (RawCtxInterpretedSend.ready pending
        (RawCtxSelectedSendCompiler.deriveValue prior none target nonce next pending.request)).advanced := by
      simp only [sealNext, began, RawCtxInterpretedSend.mapStart, RawCtxInterpretedSend.nativeStart, bind_tc_ok,
        RawCtxSourceSend.resumeSend_exact, RawCtxInterpretedSend.ready_native] at sealed
      change SendSeal.finish (RawCtxInterpretedSend.nativeSeal (RawCtxInterpretedSend.ready (RawCtxInterpretedSend.mapKdf
        (interpret key) pending) (RawCtxInterpretedReceive.decodeResponse (slotExecute prior target nonce next key
          pending.request)))) _ = _ at sealed
      rw [slot_decode, RawCtxInterpretedSend.ready_map, RawCtxInterpretedSend.native_finish, RawCtxInterpretedSend.finish_exact]
        at sealed
      obtain ⟨rfl, _⟩ := Prod.mk.inj (RustM.ok.inj sealed)
      rfl
    cases sealedOpt with
    | none => exact valid
    | some encrypted =>
      rw [value] at reach
      exact reach


/-- One owner operation keeps the interpreted kernel reachable from its directional origins. -/
theorem moves_reach {P AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (read : RawCtxReceive.FrameDecoder) (kernel moved : RawCtxSelectedMessageReveals.Kernel)
    (moves : Moves (P := P) source writer prior none target nonce next read kernel moved)
    (valid : RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key kernel)) :
    RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key moved) := by
  obtain ⟨sender, query, owner, finalOwner, reply, rfl, found, rfl⟩ := moves
  rcases query with plaintext | raw
  · rw [RawCtxSelectedOwnerCompiler.send_cases] at found
    split_ifs at found with empty
    · rw [mem_support_pure_iff] at found
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact valid
    · rw [support_map] at found
      obtain ⟨outcome, sent, mapped⟩ := found
      rcases outcome with _ | result
      · cases mapped
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
        obtain ⟨_, rfl⟩ := mapped
        exact send_reach prior target nonce next key cr sendOrigin receiveOrigin source writer _ _ valid (some result) sent
  · rw [RawCtxSelectedOwnerCompiler.raw_cases, support_map] at found
    obtain ⟨result, reached, same⟩ := found
    obtain rfl := Option.some.inj same
    unfold RawCtxSelectedReceiveCompiler.raw RawCtxChainOwner.rawReceive at reached
    simp only [StateT.run] at reached
    have unchanged : ∀ (state : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P),
        state.kernel = owner.kernel → (reply, finalOwner) ∈ support (pure (RawCtxChainOwner.publish state (state.kernel, .None)) :
          OracleComp AdaptiveCtxDynamicKnownKeys.Spec _) →
        RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
          (RawCtxSelectedMessageReveals.nativeKernel key finalOwner.kernel) := by
      intro state same published
      rw [mem_support_pure_iff] at published
      rw [congrArg (fun value => value.2.kernel) published]
      simp only [RawCtxChainOwner.publish]
      rw [same]
      exact valid
    split_ifs at reached with empty
    · exact unchanged owner rfl reached
    split at reached
    · exact unchanged owner rfl reached
    split_ifs at reached with validFrame
    · rw [mem_support_bind_iff] at reached
      obtain ⟨outcome, received, published⟩ := reached
      rw [mem_support_pure_iff] at published
      rw [congrArg (fun value => value.2.kernel) published]
      exact receive_reach prior target nonce next key cr sendOrigin receiveOrigin read _ _ _ _ valid outcome received
    · exact unchanged owner rfl reached

/-- Reachability by owner operations keeps the interpreted kernel reachable from its directional origins. -/
theorem reach_reach {P AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (read : RawCtxReceive.FrameDecoder) (start moved : RawCtxSelectedMessageReveals.Kernel)
    (reach : Reach (P := P) source writer prior none target nonce next read start moved)
    (valid : RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key start)) :
    RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key moved) := by
  induction reach with
  | base => exact valid
  | step _ moves ih => exact moves_reach prior target nonce next key cr sendOrigin receiveOrigin source writer read _ _ moves ih

/-- At a receive origin with the selected target address, the first message key of the concrete interpretation is the selected key realized by `key`. -/
theorem origin_material {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (origin : RatchetChain)
    (address : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest origin) =
      RawCtxSelectedParentPrivatePatch.targetAddress target) :
    Ratchet.msgKeyAt (withInterpreter cr (slotExecute prior target nonce next key)) origin 0 =
      RawCtxFreshChainCut.concreteMaterial (key, nonce) := by
  have decoded := slot_decode prior target nonce next key (RawCtxChainSend.nativeRequest origin)
  simp only [RawCtxSelectedSendCompiler.deriveValue, RawCtxSelectedMessageKdf.step, address, ↓reduceIte, interpret] at decoded
  change (RawCtxInterpretedReceive.decodeResponse (slotExecute prior target nonce next key (RawCtxChainSend.nativeRequest origin))).2 = _
  rw [decoded]


/-- A reached selected-material opening with known material `material` at a positive sequence is, in every reachable concrete interpretation, the concrete message key at that sequence of the receive origin. -/
theorem known_material {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (moved : RawCtxSelectedMessageReveals.Kernel)
    (valid : RoleReachable (withInterpreter cr (slotExecute prior target nonce next key)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key moved))
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (pending : Pending) (material : RatchetMaterial)
    (positive : 0 < sequence.val)
    (reached : terminal prior none target nonce next (RawCtxInterpretedReceive.normalBegin moved sequence context) = .opening pending)
    (arguments : RawCtxInterpretedArguments.openArguments pending = some ⟨.known material, sequence, context⟩) :
    material = Ratchet.msgKeyAt (withInterpreter cr (slotExecute prior target nonce next key)) receiveOrigin (sequence.val - 1) := by
  set execute := slotExecute prior target nonce next key
  set native := RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending)
  have concreteRun : (simulateQ (RawCtxMaterialPositions.bareReceiveImpl execute (recordOpen .None))
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key moved) sequence context)).run none =
      pure ((ConcreteRatchetKernel.mk (mapRefined (interpret key) (RawCtxInterpretedReceive.normalFinish pending
        (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted)).1), .None), some native) := by
    rw [slot_native, StateT.run_map, slot_terminal, reached]
    simp only [slotLabels]
    rw [StateT.run_map]
    simp [recordOpen, StateT.run, native]
    rfl
  have slotMaterial : RawCtxInterpretedOpening.material pending = ok (.Some (Slot.known material)) := by
    unfold RawCtxInterpretedArguments.openArguments at arguments
    have spec := (RawCtxInterpretedArguments.material_total pending).choose_spec
    revert arguments spec
    cases (RawCtxInterpretedArguments.material_total pending).choose with
    | none => intro arguments; cases arguments
    | some selected =>
      intro arguments spec
      simp only [Option.some.injEq, RawCtxInterpretedArguments.Input.mk.injEq] at arguments
      rw [spec, arguments.1]
  have nativeMaterial : ReceiveOpen.material native = ok (.Some material) := by
    simp only [native]
    rw [RawCtxInterpretedOpening.native_material, RawCtxInterpretedOpening.material_map, slotMaterial]
    rfl
  have opened_eq : ∀ (opened : ReceiveOpen RawCtxWholeOwner.OpenContext) (extra : RawCtxMaterialPositions.KdfLog),
      (∀ state history, (simulateQ (RawCtxMaterialPositions.receiveImpl execute (recordOpen .None))
        (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key moved) sequence context)).run (state, history) =
        (do
          let result ← (recordOpen .None opened).run state
          pure (RawCtxOwnerOracle.finish opened result.1, (result.2, history ++ extra)))) → opened = native := by
    intro opened extra run
    have erased := RawCtxMaterialPositions.receive_complete_erase execute (recordOpen .None)
      (RawCtxOwnerOracle.receive (RawCtxSelectedMessageReveals.nativeKernel key moved) sequence context) (none, [])
    rw [run, concreteRun] at erased
    have same := congrArg support erased
    simp [recordOpen, StateT.run] at same
    exact same.2
  have rejected_false : ∀ entry, begin_receive (RawCtxSelectedMessageReveals.nativeKernel key moved) sequence context =
      ok (ReceiveEffect.ReceiveRejected entry context) → False := by
    intro entry rejected
    have began : RawCtxOwnerOracle.begin (RawCtxSelectedMessageReveals.nativeKernel key moved) sequence context =
        .ReceiveRejected entry context :=
      RustM.ok.inj ((RawCtxOwnerOracle.begin_exact _ sequence context).symm.trans rejected)
    rw [RawCtxOwnerOracle.receive, began, RawCtxOwnerOracle.program, simulateQ_pure, StateT.run_pure] at concreteRun
    have same := congrArg support concreteRun
    simp at same
  obtain ⟨send, receive, refines, _⟩ := valid
  by_cases future : receive.n < sequence.val
  · by_cases capacity : (RawCtxSelectedMessageReveals.nativeKernel key moved).refined.control.receive_cache.len.val +
        (sequence.val - receive.n - 1) ≤ 50
    · obtain ⟨opened, _, openedMaterial, run⟩ := RawCtxMaterialPositions.future_positioned_run cr execute receiveOrigin send receive
        _ context sequence refines future capacity (recordOpen .None)
      have same := opened_eq opened _ run
      rw [same, nativeMaterial] at openedMaterial
      exact Option.some.inj (RustM.ok.inj openedMaterial)
    · exact (rejected_false _ (refines.begin_receive_capacity_rejected _ receiveOrigin send receive _ sequence context future
        (by omega))).elim
  · cases stored : List.lookup (sequence.val - 1) receive.skipped with
    | none => exact (rejected_false _ (refines.begin_receive_replay _ receiveOrigin send receive _ sequence context (by omega)
        positive stored)).elim
    | some value =>
      obtain ⟨opened, _, _, openedMaterial, run⟩ := RawCtxMaterialPositions.cached_positioned_run cr execute receiveOrigin send
        receive _ context sequence (sequence.val - 1) value refines (by omega) stored (recordOpen .None)
      have same := opened_eq opened [] (fun state history => by rw [run state history, List.append_nil])
      rw [same, nativeMaterial] at openedMaterial
      exact Option.some.inj (RustM.ok.inj openedMaterial)


/-- Two different selected keys give different concrete message materials for the same nonce. -/
theorem material_keys_ne (nonce : NonceOutput) :
    RawCtxFreshChainCut.concreteMaterial (List.Vector.replicate 32 0, nonce) ≠
      RawCtxFreshChainCut.concreteMaterial (List.Vector.replicate 32 1, nonce) := by
  intro same
  have bytes := congrArg (fun material : RatchetMaterial => (material.key.bytes.val.head?).map
    PqxdhRefinement.absByte) same
  simp [RawCtxFreshChainCut.concreteMaterial, BeaconcryptCore.Refinement.ProtocolComposition.absByte_concreteByte] at bytes

/-- Concretizing the root vector of a chain returns the chain. -/
theorem concrete_rootVector (chain : RatchetChain) :
    RawCtxFreshChainCut.concreteChain (RawCtxSelectedQueryTrace.rootVector chain) = chain := by
  apply BeaconcryptCore.Refinement.RepresentationBridge.absChain_injective
  exact congrArg Subtype.val (RawCtxSelectedQueryTrace.rootVector_concrete (RawCtxSelectedQueryTrace.rootVector chain))


end SlotReach

section Suffix
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth RawCtxSelectedAuthenticationObserver
open RawCtxSelectedPlaintextOrigins
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- First-slot obligation of the extracted Server ratchet for Beacon `b`'s first record: for every initializer block, selected nonce and next chain, no kernel reachable by owner sends and raw receives from a first-send move of the initial Server kernel opens a sequence-one record with known material. It is a deterministic property of the fixed receive/send driver and selected derivation (the initial Server receive chain is the selected root, so its first message key is the hidden slot, which the driver keeps in its receive chain or skipped-key cache until consumed); it involves no adversary, probability or secret. `first_slot_hidden` proves it. -/
def FirstSlotHidden (b : Fin (B + 1)) : Prop :=
  ∀ (block : HmacBlock) (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel),
    initialKernel (RawCtxSelectedInitialConstructor.response64 block) = .ok kernel → ∀ context,
    ∀ outcome ∈ support (RawCtxSelectedSendCompiler.send (env0).source (env0).recordWriter (productionStream (env0).source.crypto)
      none (PqxdhInitialSourceExperiment.root (env0).source zeroRoot (RawCtxSelectedInitialConstructor.response64 block)
        (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) nonce next kernel context),
    ∀ moved, Reach (P := P) (env0).source (env0).recordWriter (productionStream (env0).source.crypto) none
      (PqxdhInitialSourceExperiment.root (env0).source zeroRoot (RawCtxSelectedInitialConstructor.response64 block)
        (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) nonce next (env0).decode (outcome.getD (kernel, none)).1 moved →
    ¬ FirstKnown (productionStream (env0).source.crypto) none (PqxdhInitialSourceExperiment.root (env0).source zeroRoot
      (RawCtxSelectedInitialConstructor.response64 block) (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) nonce next moved

/-- The first-slot fact holds for every Beacon `b`: the Server receive origin of the supplied initializer is the Beacon send chain, which has the selected target address, so every reachable concrete interpretation opens sequence one with the selected key realized by an arbitrary `key`; a known material would equal the concrete material of two different keys. -/
theorem first_slot_hidden (b : Fin (B + 1)) : FirstSlotHidden (P := P) setup env callbacks b := by
  intro block nonce next kernel initialized context outcome sent moved reach known
  obtain ⟨sequence, openContext, pending, material, one, reached, arguments⟩ := known
  unfold PqxdhSelectedFirstRecord.initialKernel at initialized
  cases created : PqxdhInitialReplyErasure.kernelOf false (RawCtxSelectedInitialConstructor.response64 block) with
  | fail error => simp [created] at initialized; cases initialized
  | div => simp [created] at initialized; cases initialized
  | ok server =>
    rw [created] at initialized
    obtain rfl : kernel = PqxdhSelectedMessageBeacon.knownKernel server.refined := (RustM.ok.inj initialized).symm
    obtain ⟨beacon, server', beaconCreated, serverCreated, _, _, chains, _⟩ :=
      PqxdhInitialSuppliedPositions.pair_positioned (env0).source.crypto (RawCtxSelectedInitialConstructor.response64 block)
    obtain rfl : server' = server := RustM.ok.inj (serverCreated.symm.trans created)
    obtain rfl : beacon = PqxdhInitialRootAudit.kernel (zeroRoot, RawCtxSelectedInitialConstructor.response64 block) :=
      RustM.ok.inj (beaconCreated.symm.trans
        (PqxdhInitialKernelConstruction.audited_supplied (zeroRoot, RawCtxSelectedInitialConstructor.response64 block)))
    have address : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest server'.refined.receive_chain) =
        RawCtxSelectedParentPrivatePatch.targetAddress (PqxdhInitialSourceExperiment.root (env0).source zeroRoot
          (RawCtxSelectedInitialConstructor.response64 block) (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) := by
      change _ = RawCtxSelectedPendingCut.requestAddress (RawCtxFreshChainCut.concreteChain (RawCtxSelectedQueryTrace.rootVector
        (PqxdhInitialRootAudit.kernel (zeroRoot, RawCtxSelectedInitialConstructor.response64 block)).refined.send_chain))
      rw [concrete_rootVector, chains]
      rfl
    have forKey : ∀ key : RootOutput, material = RawCtxFreshChainCut.concreteMaterial (key, nonce) := by
      intro key
      have native : RawCtxSelectedMessageReveals.nativeKernel key (PqxdhSelectedMessageBeacon.knownKernel server'.refined) =
          server' := congrArg ConcreteRatchetKernel.mk (PqxdhSelectedMessageBeacon.known_roundtrip key server'.refined)
      have initial := PqxdhInitialKernelConstruction.supplied_reachable
        (withInterpreter (RawCtxPositionedOwner.crypto (env0).source.crypto) (slotExecute (productionStream (env0).source.crypto)
          (PqxdhInitialSourceExperiment.root (env0).source zeroRoot (RawCtxSelectedInitialConstructor.response64 block)
            (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) nonce next key)) false _ server' created
      rw [← native] at initial
      have first := send_reach _ _ _ _ key _ _ _ _ _ _ _ initial outcome sent
      have final := reach_reach _ _ _ _ key _ _ _ _ _ _ _ _ reach first
      rw [known_material _ _ _ _ key _ _ _ _ final sequence openContext pending material (by omega) reached arguments, one]
      exact origin_material _ _ _ _ key _ _ address
    exact material_keys_ne nonce ((forKey _).symm.trans (forKey _))

/-- A pending prepared input carries the environment's Server index. -/
theorem input_index (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (packet : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program)
    (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A)
      (S := S) (B := B) (setup := setup))
    (pending : PqxdhSourceSharedInput.input setup env callbacks program post0 attachedVerify primitives
      baseImpl kem owner number ancestors disclosed packet = .inr input) :
    input.index = (env0).index := by
  unfold PqxdhSourceSharedInput.input PqxdhInitialPreparedSourceInput.input at pending
  split at pending
  · cases pending
  · cases pending
    rfl

/-- Outside the initial half alias, every `true` run of the key-free first-record suffix of the canonical proxy, started from a consistent observer with no selected seal, is an observer win, given the writer premise; the first-slot fact is `first_slot_hidden`. -/
theorem suffix_won (b : Fin (B + 1)) (writable : ReadWritable (env0).recordWriter (env0).decode)
    (key : CtxKey)
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput)
    (separate : ¬ RawCtxSendLineageCollision.InitialAlias sample.2.1) (start : State × SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key start) (empty : start.1.seals = [])
    (result : Bool × (State × SourceState))
    (supported : result ∈ support ((simulateQ (observed true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key)
      (suffix setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)
        sample)).run start))
    (bit : result.1 = true) : won (RawCtxUniversalDecoder.decoder (env0).decode) result.2.1 = true := by
  unfold suffix at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst supported
    cases bit
  rename_i input pending
  unfold firstClient at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨built, builtFound, postResult, postFound, final⟩ := supported
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at final
  subst final
  have answered : postResult.1.1 = some true := of_decide_eq_true bit
  have selected := input_selected setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
    (.beacon b) 1#u64 [] [] sample.1 input pending
  have indexed := input_index setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
    (.beacon b) 1#u64 [] []
    sample.1 input pending
  obtain ⟨selection, posted⟩ := input_post setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (.beacon b) 1#u64 [] [] sample.1 input pending
  rw [selected] at builtFound postFound
  obtain ⟨goodBuilt, sealsBuilt⟩ := built_clean (key := key) (read := (env0).decode)
    (known := fun kernel initialized context => initial_known (env0).source sample.2.1 b sample.2.2.1 sample.2.2.2 separate kernel
      initialized context) (component := start) (good := good) (built := built) (supported := builtFound)
  rw [posted] at postFound
  unfold canonicalPost logged at postFound
  rw [simulateQ_map, OptionT.run_map, StateT.run_map, simulateQ_map, StateT.run_map, support_map] at postFound
  obtain ⟨inner, innerFound, rfl⟩ := postFound
  dsimp only at answered ⊢
  obtain ⟨value, returned, forgedBit⟩ := Option.map_eq_some_iff.mp answered
  have replyForged : ReplyCanonicalForged (env0).index (env0).route (env0).decode (env0).recordWriter built.1.1.1 value.2 := by
    unfold canonicalBit at forgedBit
    exact @of_decide_eq_true _ (Classical.propDecidable _) (Bool.and_eq_true_iff.mp forgedBit).2
  rcases replied : built.1.1.1 with (_ | response) | error | _
  all_goals rw [replied] at replyForged
  all_goals try exact replyForged.elim
  have builtSyntactic := observed_syntactic _ _ _ _ start built builtFound
  obtain ⟨found, peersFound, kernel, initialized, context, outcome, outcomeFound, same⟩ :=
    build_installs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ builtSyntactic response replied
  have hiddenHere := first_slot_hidden setup env callbacks b sample.2.1 sample.2.2.1 sample.2.2.2 kernel initialized context outcome outcomeFound
  rw [same] at hiddenHere
  have initialInv : Inv (baseSpec := baseSpec) (env0).source (env0).recordWriter (productionStream (env0).source.crypto) none
      (PqxdhInitialSourceExperiment.root (env0).source zeroRoot (RawCtxSelectedInitialConstructor.response64 sample.2.1)
        (.beacon b : RawCtxProtocolReveals.Owner S (B + 1))) sample.2.2.1 sample.2.2.2 (env0).route
      (env0).decode input.index response.keyId key found.kernel [] (built.1.1.2, built.1.2) built.2 := by
    refine ⟨goodBuilt, fun forged => ?_, fun sealed member => ?_, fun other otherFound => ?_⟩
    · obtain ⟨before, entry, after, _, _, split, _⟩ := forged
      simp at split
    · rw [sealsBuilt, empty] at member
      cases member
    · rw [peersFound] at otherFound
      cases otherFound
      exact Reach.base
  have final := inv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ writable hiddenHere (post0 selection built.1.1.1) []
    (built.1.1.2, built.1.2) built.2 initialInv (inner.1.1, (inner.1.2, inner.2)) (by
      simp only [PqxdhSelectedStateInterpreter.evaluate, support_map, Set.mem_image]
      exact ⟨inner, innerFound, rfl⟩) value returned
  exact final.forged (by rw [indexed]; exact replyForged)

end Suffix

section Guard

/-- A Boolean continuation that can return `true` only after an outcome satisfying `guard` has `true` mass at most the probability of `guard`. -/
theorem true_le_guard {α : Type} (mx : ProbComp α) (my : α → ProbComp Bool) (guard : α → Prop)
    (quiet : ∀ a ∈ support mx, ¬ guard a → ∀ b ∈ support (my a), b = false) :
    𝒟[mx >>= my] {true} ≤ Pr[guard | mx] := by
  classical
  rw [evalDist_apply_singleton, probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases reached : a ∈ support mx
  · by_cases guarded : guard a
    · rw [ite_eq_left guarded]
      exact mul_le_of_le_one_right' probOutput_le_one
    · rw [ite_eq_right guarded, probOutput_eq_zero_of_not_mem_support (mx := my a) (x := true)
        (fun found => by simpa using quiet a reached guarded true found), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support reached, zero_mul]
    exact bot_le

end Guard

section Gap
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth RawCtxSelectedAuthenticationObserver AdaptiveCtxSharedHash
open RawCtxSelectedPlaintextOrigins
open AdaptiveCtxDynamicKnownKeys (Spec SourceState)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- In the observed run of the forwarded prelude, the two halves of the drawn initializer response are equal with probability at most `2^-256`. -/
theorem prelude_alias (key : CtxKey) :
    Pr[fun result => RawCtxSendLineageCollision.InitialAlias result.1.2.1 |
      (simulateQ (observed true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post))).run
          (initialState, AdaptiveCtxDynamicKnownKeys.initialSource)] ≤ (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  classical
  rw [show (fun result : (Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock ×
      NonceOutput × RootOutput) × (State × SourceState) => RawCtxSendLineageCollision.InitialAlias result.1.2.1) =
      (fun sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock ×
        NonceOutput × RootOutput => RawCtxSendLineageCollision.InitialAlias sample.2.1) ∘ Prod.fst from rfl,
    ← probEvent_map, observed_fst]
  have cached := congrArg (fun work => Prod.fst <$> work) (RawCtxSourceSharedRom.forward_cache true
    (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key
    (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) AdaptiveCtxDynamicKnownKeys.initialSource)
  simp only [Functor.map_map] at cached
  rw [cached, probEvent_map]
  have emptyCache : AdaptiveCtxDynamicKnownKeys.initialSource.cache = ∅ := rfl
  rw [emptyCache]
  have restored := congrArg (fun work => probEvent work fun sample => RawCtxSendLineageCollision.InitialAlias sample.2.1)
    (prelude_source setup env callbacks baseImpl kem attachedVerify primitives program post)
  simp only [probEvent_map] at restored
  refine le_of_eq_of_le (Eq.trans rfl restored) ?_
  refine probEvent_bind_le_of_forall_le fun context _ => ?_
  refine (probEvent_bind_le_probEvent (p := RawCtxSendLineageCollision.InitialAlias) ?_).trans
    RawCtxSendLineageCollision.initial_alias_uniform
  intro initialBlock _ separate
  simp
  intro _ _ _ _ _ _ _ same _ _
  subst same
  exact separate

/-- The gap game of the canonical first-record client is at most `2^-256` under the writer premise: outside the initial half alias every `true` run of the client is an observer win. -/
theorem gap_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))
    (writable : ReadWritable (env0).recordWriter (env0).decode) :
    𝒟[gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (fullClient setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (firstBeacon b))] {true} ≤ (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [gap_observed, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun key _ => ?_
  rw [probEvent_eq_eq_probOutput, ← evalDist_apply_singleton]
  unfold fullClient
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine (true_le_guard _ _ (fun result => RawCtxSendLineageCollision.InitialAlias result.1.2.1) ?_).trans
    (prelude_alias setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) key)
  intro prefixResult reached separate bit found
  have good := schedule_good _ _ _ _ (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) (initial_good _ _ _) prefixResult
    reached
  have empty := observed_seals _ _ _ _ (forward_no_seal _) (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) prefixResult
    reached
  simp only [mem_support_bind_iff, mem_support_pure_iff] at found
  obtain ⟨result, resultFound, rfl⟩ := found
  cases returned : result.1
  · rfl
  · have winning := suffix_won setup env callbacks baseImpl kem attachedVerify primitives program post0 b writable key
      prefixResult.1 separate prefixResult.2 good empty result resultFound returned
    rw [winning]
    rfl

end Gap

section Chain
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The pending mass of the fixed first-record source experiment with the canonical proxy is at most the compiled first-record game, the restricted stop game, the first-record target loss and the completed-branch root loss. -/
theorem canonical_pending_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (target : Target S (B + 1)) (position : target.number.val = 1)
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program (canonicalPost env0 program post0)
          target.owner target.number target.ancestors target.disclosed)] {true}).toReal ≤
    (𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) target]
      {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) target]
      {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets target)
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback := by
  have pending := PqxdhFirstRecordTarget.pending_le env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
    target position (canonicalCertificate env0 baseImpl kem program post0 c) compatible adapter functional hmac correct fallback
    ordinaryFallback
  have ideal := pending_ideal_le setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
    target position
  have ideal_real := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PqxdhFirstRecordTarget.true_ne_top _,
    PqxdhFirstRecordTarget.true_ne_top _⟩) ideal
  rw [ENNReal.toReal_add (PqxdhFirstRecordTarget.true_ne_top _) (PqxdhFirstRecordTarget.true_ne_top _)] at ideal_real
  linarith

/-- The HB-112 actual game with the canonical proxy, minus its constant-`false` continuation, is at most the compiled first-record game, the restricted stop game, the first-record target loss and the completed-branch root loss. -/
theorem canonical_forgery_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    (𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback := by
  have split := PqxdhFirstRecordTarget.target_split env0 baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (.beacon b) 1#u64 [] []
  rw [split, ENNReal.toReal_add (PqxdhFirstRecordTarget.true_ne_top _) (PqxdhFirstRecordTarget.true_ne_top _), add_sub_cancel_left]
  exact canonical_pending_le setup env callbacks baseImpl kem attachedVerify primitives program post0 (firstBeacon b) rfl c
    compatible adapter functional hmac correct fallback ordinaryFallback

/-- The canonical proxy post makes at most the certificate's total post budget of requests. -/
theorem canonical_total (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0) (selection : program.Selection)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    (canonicalPost env0 program post0 selection reply).IsTotalQueryBound
      (postTotal setup env callbacks baseImpl kem program c) :=
  (isQueryBoundP_true_iff _ _).mp ((canonical_query_bound env0 program post0 selection reply (fun _ => True) _).mpr
    ((isQueryBoundP_true_iff _ _).mpr (total_of_kinds PqxdhPhase2SourceSchedulerBounds.classify (post0 selection reply)
      c.postBudget (c.postBound selection reply))))

/-- The CTX step for the canonical proxy: its left side is bounded by the target and completed-branch losses, the CTX loss of the constructed client, `2^-256`, the gap game of the constructed client and the restricted stop game. -/
theorem canonical_integrity_ctx
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program
      (canonicalPost env0 program post0) qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback +
    (ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)
      ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
      (1 + postTotal setup env callbacks baseImpl kem program c)).toReal +
    1 / 2 ^ 256 +
    (𝒟[gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (fullClient setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (firstBeacon b))] {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      (firstBeacon b)] {true}).toReal := by
  have postBound := canonical_total setup env callbacks baseImpl kem program post0 c
  have hashBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (firstBeacon b) HashRoute
    (fun _ _ _ _ query state => external_no_hash _ _ _ _ _ query state) qPrelude
    (prelude_hash setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) qPrelude
      prepareHash) _ postBound
  have sealBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (firstBeacon b) (TargetClass SourceSeal)
    (fun _ _ _ _ query state => external_no_seal _ _ _ _ _ query state) 0 (forward_no_seal _) _ postBound
  have rawBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (firstBeacon b) (TargetClass AdaptiveCtxReceive.IsRawQuery)
    (fun _ _ _ _ query state => PqxdhSelectedInitialOwnerCompiler.external_no_open _ _ _ _ _ query state) 0 (forward_no_open _) _
      postBound
  rw [Nat.zero_add] at sealBound rawBound
  have reduced := canonical_forgery_le setup env callbacks baseImpl kem attachedVerify primitives program post0 b c
    compatible adapter functional hmac correct fallback ordinaryFallback
  have compiled := compiled_ctx_bound setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) b ctxFallback _ _ _ hashBound sealBound rawBound (by omega)
  have aliasFinite : (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have gapFinite := PqxdhFirstRecordTarget.true_ne_top (gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (fullClient setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)))
  have lossFinite := ctxLoss_ne_top setup env callbacks baseImpl kem attachedVerify primitives program
    (canonicalPost env0 program post0) (firstBeacon b) ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
    (1 + postTotal setup env callbacks baseImpl kem program c)
  have real := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨aliasFinite, lossFinite⟩, gapFinite⟩) compiled
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨aliasFinite, lossFinite⟩) gapFinite,
    ENNReal.toReal_add aliasFinite lossFinite] at real
  have half : ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal = 1 / 2 ^ 256 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow]
    norm_num
  rw [half] at real
  linarith

/-- First Beacon record integrity for the canonical forgery event: the HB-112 actual game with the canonical proxy, minus its constant-`false` continuation, is at most the target and completed-branch losses, the CTX loss, `2^-256` twice and the restricted stop game, given the writer premise `ReadWritable`. -/
theorem first_beacon_record_integrity_canonical
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program
      (canonicalPost env0 program post0) qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96)
    (writable : ReadWritable env.recordWriter env.decode) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback +
    (ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)
      ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
      (1 + postTotal setup env callbacks baseImpl kem program c)).toReal +
    1 / 2 ^ 256 + 1 / 2 ^ 256 +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      (firstBeacon b)] {true}).toReal := by
  have base := canonical_integrity_ctx setup env callbacks baseImpl kem attachedVerify primitives program post0 b c
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude prepareHash small
  have gap := gap_le setup env callbacks baseImpl kem attachedVerify primitives program post0 b writable
  have real := ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)) gap
  have half : ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal = 1 / 2 ^ 256 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow]
    norm_num
  rw [half] at real
  linarith

end Chain

end BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.won_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.won_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_won

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_monitor

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_component

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.clean_seals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.clean_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_syntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_syntactic

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.observed_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.gap_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.gap_observed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.firstWritten_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.firstWritten_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forged_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forged_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forged_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forged_single

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reencoded_not_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reencoded_not_counted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.transcribed_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.transcribed_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.read_writable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.read_writable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.frame_decode_bounded' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.frame_decode_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.matched_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.matched_written

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.sent_reencoding_not_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.sent_reencoding_not_counted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.state_map_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.state_map_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.state_bind_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.state_bind_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reveal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reveal_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.selector_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.selector_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.finish_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.finish_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.server_accept_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.server_accept_wins

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.produced_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.produced_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.transcribed_sent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.transcribed_sent

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_transcribed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_transcribed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_peer_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.family_peer_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_family

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.inv_post

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.after_installs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.after_installs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.candidate_installs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.candidate_installs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.ready_installs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.ready_installs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.compiled_moves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.compiled_moves

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.build_installs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.build_installs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.built_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.built_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_decode

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_native

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.terminal_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.terminal_any

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.slot_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.compiled_receive_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.compiled_receive_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.receive_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.receive_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.send_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.send_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.moves_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.moves_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reach_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.reach_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.origin_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.origin_material

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.known_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.known_material

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.material_keys_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.material_keys_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.concrete_rootVector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.concrete_rootVector

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.first_slot_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.first_slot_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.input_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.input_index

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.suffix_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.suffix_won

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.true_le_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.true_le_guard

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.prelude_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.prelude_alias

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.gap_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.gap_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_pending_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_pending_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forgery_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_forgery_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_total

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_integrity_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.canonical_integrity_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.first_beacon_record_integrity_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical.first_beacon_record_integrity_canonical
