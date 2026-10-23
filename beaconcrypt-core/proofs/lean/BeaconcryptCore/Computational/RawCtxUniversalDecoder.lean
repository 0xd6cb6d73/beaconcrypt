import BeaconcryptCore.Computational.RawCtxSelectedMessageOpening

/-!
A fixed ordinary selected-key decoder supports source contexts chosen adaptively by the live owner lookup. Its private reduction framing contains the selected nonce, the exact 281-byte associated data and the original network bytes verbatim. These simulator-known inputs do not include the selected key or a proposed or recovered plaintext. The source performs its normal sender pin, frame validation and ratchet admission before this component callback. The reduction framing is not a production wire format or a network disclosure.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxUniversalDecoder
open CtxRomAuth AdaptiveCtxReceive

structure Envelope where
  nonce : CtxNonce
  ad : List.Vector UInt8 281
  raw : Pqxdh.Bytes

def pack (value : Envelope) : Pqxdh.Bytes := value.nonce.toList ++ value.ad.toList ++ value.raw

def unpack (bytes : Pqxdh.Bytes) : Option Envelope :=
  if nonceWidth : (bytes.take 12).length = 12 then
    if adWidth : ((bytes.drop 12).take 281).length = 281 then
      some ⟨⟨bytes.take 12, nonceWidth⟩, ⟨(bytes.drop 12).take 281, adWidth⟩, bytes.drop 293⟩
    else none
  else none

/-- The reduction framing recovers both private context coordinates and every original network byte exactly. -/
theorem unpack_pack (value : Envelope) : unpack (pack value) = some value := by
  cases value with
  | mk nonce ad raw =>
    simp [unpack, pack, List.drop_append]

/-- Distinct simulator contexts or original raw messages cannot become the same framed component input. -/
theorem pack_injective : Function.Injective pack := by
  intro left right equal
  have decoded := congrArg unpack equal
  simpa only [unpack_pack, Option.some.injEq] using decoded

/-- Every component framing adds exactly the retained twelve-byte nonce and 281-byte associated data. -/
theorem pack_length (value : Envelope) : (pack value).length = value.raw.length + 293 := by
  simp [pack, Nat.add_left_comm, Nat.add_comm]

noncomputable def decodeFrame (value : Envelope) : Option RawCtxReceive.DecodedFrame → Option CtxUnclaimedAcceptance.Target
  | none => none
  | some frame =>
      match parsed : RawCtxFrameDecoding.fromPayload frame.payload with
      | none => none
      | some slices => some (RawCtxKeyFreeDecoder.target value.nonce frame.sequence frame value.ad.toList
          slices parsed value.ad.2)

noncomputable def decoder (read : RawCtxReceive.FrameDecoder) : RawDecoder := fun bytes => do
  let value ← unpack bytes
  if value.raw.isEmpty then none else decodeFrame value (read value.raw)

/-- One fixed key-free decoder handles every reached nonce, AD and owner frame before any opening reply is available. -/
theorem decoder_pack (read : RawCtxReceive.FrameDecoder) (value : Envelope)
    (frame : RawCtxReceive.DecodedFrame) (slices : RawCtxFrameDecoding.Slices)
    (nonempty : value.raw.isEmpty = false) (decoded : read value.raw = some frame)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices) :
    decoder read (pack value) = some (RawCtxKeyFreeDecoder.target value.nonce frame.sequence frame
      value.ad.toList slices parsed value.ad.2) := by
  simp only [decoder, decodeFrame, unpack_pack, Option.bind_eq_bind, Option.bind_some, nonempty,
    Bool.false_eq_true, ite_false, decoded]
  split
  · simp_all
  · rename_i other same
    have equal : other = slices := Option.some.inj (same.symm.trans parsed)
    subst other
    rfl

/-- Missing framing bytes reject before any source frame is decoded. -/
theorem decoder_unframed (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (missing : unpack bytes = none) : decoder read bytes = none := by
  simp [decoder, missing]

/-- The original source empty-input rejection survives the private framing. -/
theorem decoder_empty (read : RawCtxReceive.FrameDecoder) (value : Envelope)
    (empty : value.raw.isEmpty = true) : decoder read (pack value) = none := by
  simp only [decoder, decodeFrame, unpack_pack, Option.bind_eq_bind, Option.bind_some, empty, ite_true]

/-- Malformed original frame bytes reject after exact removal of the private metadata. -/
theorem decoder_malformed (read : RawCtxReceive.FrameDecoder) (value : Envelope)
    (malformed : read value.raw = none) : decoder read (pack value) = none := by
  simp only [decoder, decodeFrame, unpack_pack, Option.bind_eq_bind, Option.bind_some, malformed]
  split <;> rfl

/-- Protected-payload rejection is retained instead of manufacturing a target from a malformed body. -/
theorem decoder_payload (read : RawCtxReceive.FrameDecoder) (value : Envelope)
    (frame : RawCtxReceive.DecodedFrame) (decoded : read value.raw = some frame)
    (malformed : RawCtxFrameDecoding.fromPayload frame.payload = none) : decoder read (pack value) = none := by
  simp only [decoder, decodeFrame, unpack_pack, Option.bind_eq_bind, Option.bind_some, decoded]
  split
  · rfl
  · split
    · rfl
    · rename_i slices parsed
      simp [malformed] at parsed

/-- The framing contains exactly the simulator's current source nonce/AD and the original raw delivery. -/
def envelope (nonce : CtxNonce) (context : RawCtxWholeOwner.OpenContext)
    (width : context.associatedData.length = 281) : Envelope :=
  ⟨nonce, ⟨context.associatedData, width⟩, context.raw⟩

/-- The fixed universal decoder produces the exact native target for every reached owner context; no fixed owner/pin/AD premise is required. -/
theorem source_target (input : RawCtxWholeOwner.OpenInput) (read : RawCtxReceive.FrameDecoder)
    (slices : RawCtxFrameDecoding.Slices)
    (width : input.context.associatedData.length = 281)
    (nonempty : input.context.raw.isEmpty = false)
    (decoded : read input.context.raw = some input.context.frame)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (sequence : input.sequence = input.context.frame.sequence) :
    decoder read (pack (envelope (RawCtxSourceOpen.sourceNonce input) input.context width)) =
      some (RawCtxCanonicalOpening.selectedTarget input slices parsed width) := by
  rw [RawCtxKeyFreeDecoder.target_source]
  simpa only [envelope, sequence, List.Vector.toList] using decoder_pack read
    (envelope (RawCtxSourceOpen.sourceNonce input) input.context width)
    input.context.frame slices nonempty decoded parsed

/-- Framing changes only the component transport bytes; the native cryptographic opening and every canonical poststate field are identical. -/
theorem framed_opening (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (width : input.context.associatedData.length = 281)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (state : AdaptiveCtxCanonical.CanonicalState)
    (decoded : decoder read bytes = some (RawCtxCanonicalOpening.selectedTarget input slices parsed width)) :
    RawCtxCanonicalOpening.sourceOpening c input
      (RawCtxCanonicalOpening.selectedTarget input slices parsed width) state =
      AdaptiveCtxCanonical.canonicalRaw (decoder read) c (RawCtxSourceOpen.sourceKey input) bytes state := by
  simp only [RawCtxCanonicalOpening.sourceOpening, RawCtxSourceOpen.openInput_typed c input slices parsed width,
    RawCtxSourceOpen.typedOpen, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind, AdaptiveCtxCanonical.canonicalRaw,
    decoded, RawCtxCanonicalOpening.afterOpening, RawCtxCanonicalOpening.selectedTarget,
    AdaptiveCtxCanonical.targetOpen]

/-- The selected challenger returns the native optional plaintext on the identical shared state under arbitrary reached source contexts. -/
theorem selected_open (key : PqxdhSecretInputKdf.RootOutput) (nonce : CtxNonce)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxSharedModes.State)
    (slices : RawCtxFrameDecoding.Slices) (width : context.associatedData.length = 281)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices)
    (sequenceMatches : sequence = context.frame.sequence) :
    (AdaptiveCtxSharedModes.targetImpl true (decoder read) c key
      (.inr (pack (envelope nonce context width)))).run state =
      (fun result => (result.1, RawCtxSharedSourceOpening.retain state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c
          (RawCtxSelectedMessageOpening.nativeInput key nonce sequence context)
          (RawCtxCanonicalOpening.selectedTarget
            (RawCtxSelectedMessageOpening.nativeInput key nonce sequence context) slices parsed width)
          (AdaptiveCtxSharedModes.canonicalProjection state) := by
  rw [RawCtxSharedSourceOpening.real_complete]
  have accepted := source_target (RawCtxSelectedMessageOpening.nativeInput key nonce sequence context)
    read slices width nonempty decoded parsed sequenceMatches
  rw [RawCtxSelectedMessageOpening.selected_nonce] at accepted
  have exactOpen := framed_opening c
    (RawCtxSelectedMessageOpening.nativeInput key nonce sequence context) slices parsed width
    read (pack (envelope nonce context width)) (AdaptiveCtxSharedModes.canonicalProjection state) accepted
  rw [RawCtxSelectedMessageOpening.selected_key] at exactOpen
  exact congrArg (fun work =>
    (fun result => (result.1, RawCtxSharedSourceOpening.retain state result.2)) <$> work) exactOpen.symm

/-- The original network bytes remain verbatim after the exactly 293-byte private prefix. -/
theorem raw_verbatim (value : Envelope) : (pack value).drop 293 = value.raw := by
  simp [pack, List.drop_append]

noncomputable def request (value : Envelope) : OracleComp ReceiveSpec (Option Pqxdh.Bytes) :=
  ReceiveSpec.query (.inr (pack value))

set_option backward.isDefEq.respectTransparency false in
/-- Framing still charges one selected verification attempt, with no public-hash, seal or explicit uniform request; the component retains its ordinary internal hash/AEAD bill. -/
theorem request_bills (value : Envelope) :
    (request value).IsQueryBoundP IsRawQuery 1 ∧
      (request value).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash 0 ∧
      (request value).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0 ∧
      (request value).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform 0 := by
  simp [request, isQueryBoundP_query_iff, IsRawQuery, AdaptiveCtxQueryBounds.SourceHash,
    AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxQueryBounds.SourceUniform]

/-- Frame decoding is an explicitly counted deterministic adapter operation, not an additional security assumption. -/
abbrev FrameReadSpec := Pqxdh.Bytes →ₒ Option RawCtxReceive.DecodedFrame

noncomputable def readProgram (bytes : Pqxdh.Bytes) :
    OracleComp FrameReadSpec (Option CtxUnclaimedAcceptance.Target) :=
  match unpack bytes with
  | none => pure none
  | some value =>
      if value.raw.isEmpty then pure none else do
        let frame ← FrameReadSpec.query value.raw
        pure (decodeFrame value frame)

/-- The counted frame-reader service evaluates to exactly the maintained fixed universal decoder. -/
theorem readProgram_exact (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) :
    simulateQ (fun raw => (pure (read raw) : ProbComp (Option RawCtxReceive.DecodedFrame))) (readProgram bytes) =
      pure (decoder read bytes) := by
  unfold readProgram decoder
  cases unpack bytes with
  | none => simp
  | some value =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split <;> simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Every framed component attempt performs at most one additional original-frame reader operation; missing framing or empty original bytes perform none. -/
theorem readProgram_queries (bytes : Pqxdh.Bytes) : (readProgram bytes).IsTotalQueryBound 1 := by
  unfold readProgram
  split
  · trivial
  · split
    · trivial
    · simp [IsTotalQueryBound]

/-- The complete selected-attempt framing ledger charges all original raw bytes plus exactly 293 metadata bytes per attempt. -/
theorem framing_ledger (values : List Envelope) :
    (values.map (fun value => (pack value).length)).sum =
      (values.map (fun value => value.raw.length)).sum + 293 * values.length := by
  induction values with
  | nil => simp
  | cons value tail ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, pack_length]
    omega

end BeaconcryptCore.Computational.RawCtxUniversalDecoder

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.unpack_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.unpack_pack

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.pack_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.pack_injective

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.pack_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.pack_length

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_pack

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_unframed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_unframed

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_empty

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_malformed

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.decoder_payload

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.source_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.source_target

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.framed_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.framed_opening

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.selected_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.selected_open

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.raw_verbatim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.raw_verbatim

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.request_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.request_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.readProgram_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.readProgram_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.readProgram_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.readProgram_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalDecoder.framing_ledger' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalDecoder.framing_ledger
