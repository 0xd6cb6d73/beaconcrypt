-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRegistrationBuild
import BeaconcryptCore.Computational.CborTaggedBuild

/-! The pointwise posthash AD151 registration suffix has a pure internal frame representation; its real outer response writer remains optional. The internal writer is bounded by complete CBOR frame size. Native writer success is never assumed, and record writers are left to the split compiler. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawCanonicalBuild
variable (associatedData : Aeneas.Std.Array Aeneas.Std.U8 151#usize)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerRegistrationPublication
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def canonicalWriter (frame : RawCtxReceive.DecodedFrame) : Option Pqxdh.Bytes :=
  if CborSizing.frameLen frame.sequence.val frame.sender.val frame.payload.length ≤ CborSizing.maxMessageSize
  then some (CborTransport.render frame) else none

def canonical (wire : Codec Reader Response) : Codec Reader Response :=
  { wire with frameWrite := canonicalWriter }

/-- The concrete parser's ordinary canonical read-back law, restricted to admitted complete frames. Allocation is absent from this law. -/
def CanonicalReadBack (wire : Codec Reader Response) : Prop :=
  ∀ frame, CborSizing.frameLen frame.sequence.val frame.sender.val frame.payload.length ≤ CborSizing.maxMessageSize →
    wire.frameRead (CborTransport.render frame) = some frame

theorem frame_readBack (wire : Codec Reader Response) (parser : CanonicalReadBack wire) :
    PqxdhServerAuthNegativeControl.FrameReadBack (canonical wire) := by
  intro frame bytes written
  simp only [canonical, canonicalWriter] at written
  split_ifs at written with admitted
  cases Option.some.inj written
  refine ⟨?_, parser frame admitted⟩
  have representable : frame.payload.length < 2 ^ 64 := by
    unfold CborSizing.frameLen CborSizing.byteStringLen CborSizing.maxMessageSize at admitted
    omega
  rw [CborTransport.render, ite_eq_left representable]
  simp

theorem canonical_written (frame : RawCtxReceive.DecodedFrame)
    (admitted : CborSizing.frameLen frame.sequence.val frame.sender.val frame.payload.length ≤
      CborSizing.maxMessageSize) : canonicalWriter frame = some (CborTransport.render frame) := by
  simp only [canonicalWriter, ite_eq_left admitted]

/-- A supported protected payload fits its internal first frame whenever the native outer response was admitted. This uses only the existing AEAD body-length law. -/
theorem first_frame_fits (crypto : Pqxdh.Crypto) (lengths : RawCtxSourcePublication.BodyLength crypto)
    (input : RawCtxSourceSend.SealInput) (valid : input.context.associatedData.length = 151)
    (first : input.sequence = 1#u64) (assigned : Nat)
    (admitted : CborSizing.responseLen (input.context.plaintext.length + 80) assigned ≤ CborSizing.maxMessageSize)
    (cache after : CtxRomAuth.CtxRO.QueryCache) (record : CtxRomAuth.CtxRomRecord)
    (actual : (record, after) ∈ support ((simulateQ CtxRomAuth.ctxRandomOracle
      (CtxRomAuth.ctxSeal crypto (RawCtxCanonicalSeal.sourceKey input)
        (RawCtxCanonicalSeal.sourceInput input valid))).run cache)) :
    canonicalWriter (RawCtxCanonicalSeal.recordFrame input record) =
      some (CborTransport.render (RawCtxCanonicalSeal.recordFrame input record)) := by
  apply canonical_written
  have width := RawCtxSourcePublication.protected_length crypto lengths input valid cache after record actual
  change CborSizing.frameLen input.sequence.val input.context.senderId.val
    (RawCtxCanonicalSeal.recordFrame input record).payload.length ≤ CborSizing.maxMessageSize
  rw [width, first]
  exact CborSizing.registration_frame_fits (input.context.plaintext.length + 80) assigned input.context.senderId.val admitted

/-- Pure virtual framing preserves every reached shared-cache state, including a hash cache hit. No native frame writer is queried. -/
theorem shared_seal_render {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (lengths : RawCtxSourcePublication.BodyLength crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (valid : input.context.associatedData.length = 151)
    (first : input.sequence = 1#u64) (assigned : Nat)
    (admitted : CborSizing.responseLen (input.context.plaintext.length + 80) assigned ≤ CborSizing.maxMessageSize)
    (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (RawCtxCanonicalSeal.sharedImpl crypto canonicalWriter kdf)
      (RawCtxSourceSeal.sealInput input)).run (auxiliary, cache) =
      (fun result => (Option.map (CborRawRegistrationBuild.renderPayload input) result.1, result.2)) <$>
        (simulateQ (RawCtxCanonicalSeal.sharedImpl crypto CborRawRegistrationBuild.rawWriter kdf)
          (RawCtxSourceSeal.sealInput input)).run (auxiliary, cache) := by
  rw [RawCtxCanonicalSeal.shared_seal crypto canonicalWriter kdf input valid auxiliary cache,
    RawCtxCanonicalSeal.shared_seal crypto CborRawRegistrationBuild.rawWriter kdf input valid auxiliary cache]
  simp only [map_bind, map_pure]
  apply bind_congr_of_forall_mem_support
  rintro ⟨record, after⟩ actual
  rw [first_frame_fits crypto lengths input valid first assigned admitted cache after record actual]
  rfl

theorem native_seal (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (input : RawCtxSourceSend.SealInput) :
    PqxdhServerAuthExperiment.nativeTail (A := List RawCtxSourceSend.SealContext) setup wire checks
        (.inl (.inr input)) =
      simulateQ (RawCtxCanonicalSeal.sharedImpl setup.source.crypto wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source)) (RawCtxSourceSeal.sealInput input) := by
  simp only [PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with aead | (hash | frame)
  all_goals simp [PqxdhRegistrationProtocolState.registrationImpl,
    RawCtxCanonicalSeal.sharedImpl, QueryImpl.compose, RawCtxSourceSeal.sealLift,
    RawCtxMixedOwner.sendLift]

/-- Mapping a successful seal's bytes preserves the logging decision and the entire primitive poststate. -/
theorem log_map {S : Type} (encode : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : StateT S ProbComp (Option Pqxdh.Bytes)) (update : S → S) (state : S) :
    (do let sealed ← Option.map encode <$> work
        if sealed.isSome then modify update
        pure sealed : StateT S ProbComp (Option Pqxdh.Bytes)).run state =
      (fun result => (Option.map encode result.1, result.2)) <$>
        (do let sealed ← work
            if sealed.isSome then modify update
            pure sealed : StateT S ProbComp (Option Pqxdh.Bytes)).run state := by
  simp only [StateT.run_bind, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨reply, after⟩
  cases reply <;> simp [StateT.run_pure, StateT.run_modify]

theorem tail_seal_render (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto) (sender : Std.U64)
    (input : RawCtxSourceSend.SealInput) (valid : input.context.associatedData.length = 151)
    (first : input.sequence = 1#u64) (assigned : Nat)
    (admitted : CborSizing.responseLen (input.context.plaintext.length + 80) assigned ≤ CborSizing.maxMessageSize)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.normalize (canonical wire) sender) checks
      (.inl (.inr input))).run state =
      (fun result => (Option.map (CborRawRegistrationBuild.renderPayload input) result.1, result.2)) <$>
        (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks
          (.inl (.inr input))).run state := by
  have mapped : PqxdhServerAuthExperiment.nativeTail
      (A := List RawCtxSourceSend.SealContext) setup
      (CborRegistrationCodec.normalize (canonical wire) sender) checks (.inl (.inr input)) =
      Option.map (CborRawRegistrationBuild.renderPayload input) <$>
        PqxdhServerAuthExperiment.nativeTail setup (CborRegistrationCodec.raw wire) checks (.inl (.inr input)) := by
    rw [native_seal, native_seal]
    apply StateT.ext
    intro current
    rw [StateT.run_map]
    exact shared_seal_render setup.source.crypto lengths (RawCtxSourceHkdf.kdfImpl setup.source)
      input valid first assigned admitted current.1 current.2
  simp only [PqxdhServerAuthExperiment.tailImpl, mapped]
  exact log_map (CborRawRegistrationBuild.renderPayload input) _
    (fun current => (current.1 ++ [input.context], current.2)) state

def renderEncrypted (sender : Std.U64) (encrypted : RawCtxSourceSend.Encrypted) : RawCtxSourceSend.Encrypted :=
  { encrypted with ciphertext := CborTransport.render ⟨encrypted.sequence, sender, encrypted.ciphertext⟩ }

theorem send_program_run {PrimitiveState : Type}
    (implementation : QueryImpl TailSpec (StateT PrimitiveState ProbComp))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (pending : ratchet.concrete.SendKdf RawCtxSourceSend.SealContext)
    (started : RawCtxSourceSend.beginSend kernel context = .SendKdfRequested pending)
    (state : PrimitiveState) :
    (simulateQ implementation (simulateQ sendLift (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send kernel context)))).run state = (do
        let response ← (implementation (.inl (.inl pending.request))).run state
        let ready := RawCtxSourceSend.resumeSend pending response.1
        let sealed ← (implementation (.inl (.inr (RawCtxSourceSend.arguments ready)))).run response.2
        pure ((ready.advanced, Option.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments ready))
          sealed.1), sealed.2)) := by
  simp only [RawCtxSourceSend.send, started,
    RawCtxSourceSend.program, simulateQ_bind, simulateQ_spec_query, sendLift, RawCtxSourceSend.adapter, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    pure_bind, bind_assoc]
  rfl

/-- The first send changes only the internal ciphertext representation; the advanced kernel, optional failures, logs and complete cache are identical. -/
theorem send_render (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto) (sender : Std.U64)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (zero : kernel.refined.control.send_sequence = 0#u64)
    (context : RawCtxSourceSend.SealContext) (valid : context.associatedData.length = 151)
    (assigned : Nat)
    (admitted : CborSizing.responseLen (context.plaintext.length + 80) assigned ≤ CborSizing.maxMessageSize)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup
      (CborRegistrationCodec.normalize (canonical wire) sender) checks)
      (simulateQ sendLift (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))).run state =
      (fun result => ((result.1.1, Option.map (renderEncrypted context.senderId) result.1.2), result.2)) <$>
        (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
          (simulateQ sendLift (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))).run state := by
  have nonmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX := by
    rw [zero]
    decide
  obtain ⟨pending, started, _, sameContext, _, _, _, nextSequence, _, _⟩ :=
    RawCtxSourceSend.beginSend_fields kernel context nonmax
  have first : pending.sequence = 1#u64 := by
    apply Std.UScalar.eq_of_val_eq
    rw [nextSequence, zero]
    rfl
  let ready := RawCtxSourceSend.resumeSend pending (RawCtxSourceHkdf.response setup.source.crypto pending.request)
  have arguments : RawCtxSourceSend.arguments ready = ⟨ready.material, 1#u64, context⟩ := by
    obtain ⟨stepped, _, resumed⟩ := RawCtxSourceSend.resumeSend_fields pending
      (RawCtxSourceHkdf.response setup.source.crypto pending.request)
    simp only [ready, RawCtxSourceSend.arguments, resumed, first, sameContext]
  rw [send_program_run _ kernel context pending started state,
    send_program_run _ kernel context pending started state]
  simp only [PqxdhServerAuthNegativeControl.tailImpl_kdf_run, pure_bind]
  change _ = (fun result => ((result.1.1, Option.map (renderEncrypted context.senderId) result.1.2), result.2)) <$>
    (do let sealed ← (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks
          (.inl (.inr (RawCtxSourceSend.arguments ready)))).run state
        pure ((ready.advanced, Option.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments ready)) sealed.1), sealed.2))
  rw [arguments, tail_seal_render setup wire checks lengths sender
    ⟨ready.material, 1#u64, context⟩ valid rfl assigned admitted state]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨reply, after⟩
  cases reply <;> rfl

/-- The actual raw response tail equals the normalized logical tail, including an outer writer rejection after successful sealing. -/
theorem after_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack wire) (sender : Std.U64)
    (candidate : pqxdh.ServerRegistrationCandidate) (pinned : candidate.server_identity_key_id = sender)
    (root : PqxdhSecretInputKdf.RootOutput) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (initialized : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel)
    (authenticated : Pqxdh.Bytes)
    (assigned : Nat)
    (admitted : CborSizing.responseLen (authenticated.length + 80) assigned ≤ CborSizing.maxMessageSize)
    (server : State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup
      (CborRegistrationCodec.normalize (canonical wire) sender) checks)
      (PqxdhServerRegistrationPublication.afterInitialization (associatedData := associatedData) candidate authenticated kernel associatedData server)).run state =
      (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
        (PqxdhServerRegistrationPublication.afterInitialization (associatedData := associatedData) candidate authenticated kernel associatedData server)).run state := by
  have valid : (firstContext (associatedData := associatedData) candidate authenticated).associatedData.length = 151 := by
    simp only [firstContext, PqxdhRefinement.absBytes_length]
    rfl
  obtain ⟨initial, run, _, _, refines⟩ :=
    PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
  have same : initial = kernel := RustM.ok.inj (run.symm.trans initialized)
  have zero : kernel.refined.control.send_sequence = 0#u64 := by
    apply Std.UScalar.eq_of_val_eq
    change kernel.refined.control.send_sequence.val = 0
    rw [← same]
    exact refines.sendSequence
  simp only [PqxdhServerRegistrationPublication.afterInitialization, simulateQ_bind, StateT.run_bind]
  rw [send_render setup wire checks lengths sender kernel zero (firstContext (associatedData := associatedData) candidate authenticated)
    valid assigned admitted state]
  simp only [bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro sent actual
  simp only [simulateQ_spec_query, PqxdhServerAuthNegativeControl.tailImpl_aux,
    PqxdhServerAuthExperiment.tailAux, StateT.run_pure, pure_bind]
  cases present : sent.1.2 with
  | none => rfl
  | some encrypted =>
    obtain ⟨digest, metadata, _, written, _⟩ := PqxdhServerAuthNegativeControl.tail_send setup
      (CborRegistrationCodec.raw wire) checks root kernel initialized
      (firstContext (associatedData := associatedData) candidate authenticated) state.1 state.2 sent actual encrypted present
    have sequence : encrypted.sequence = 1#u64 := congrArg RawCtxSourceSend.Encrypted.sequence metadata
    have width : encrypted.ciphertext.length = authenticated.length + 80 := by
      simp only [CborRegistrationCodec.raw, RawCtxSourceSeal.frame, Option.some.injEq] at written
      rw [← written]
      unfold RawCtxSourcePublication.BodyLength at lengths
      simp [firstContext, lengths, setup.source.crypto.aeadSeal_tag_length]
    have fit : CborSizing.frameLen encrypted.sequence.val candidate.server_identity_key_id.val
        encrypted.ciphertext.length ≤ CborSizing.maxMessageSize := by
      rw [width, sequence]
      exact CborSizing.registration_frame_fits (authenticated.length + 80) assigned
        candidate.server_identity_key_id.val admitted
    have parsed := parser ⟨encrypted.sequence, candidate.server_identity_key_id, encrypted.ciphertext⟩ fit
    have parsed' := parsed
    simp only [sequence, pinned] at parsed'
    have writeSame : (CborRegistrationCodec.normalize (canonical wire) sender).write2
        (responseFields candidate (renderEncrypted candidate.server_identity_key_id encrypted)) =
        (CborRegistrationCodec.raw wire).write2 (responseFields candidate encrypted) := by
      simp [CborRegistrationCodec.normalize, CborRegistrationCodec.unwrap, canonical,
        responseFields, renderEncrypted, parsed', sequence, pinned, CborRegistrationCodec.raw]
    simp only [Option.map_some, simulateQ_bind, simulateQ_spec_query,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_bind, StateT.run_pure, pure_bind]
    simp only [firstContext]
    rw [writeSame]
    cases (CborRegistrationCodec.raw wire).write2 (responseFields candidate encrypted) <;>
      simp only [simulateQ_pure, StateT.run_pure]

theorem candidate_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack wire) (sender : Std.U64)
    (candidate : pqxdh.ServerRegistrationCandidate) (pinned : candidate.server_identity_key_id = sender)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes) (assigned : Nat)
    (admitted : CborSizing.responseLen ((data.getD registrationWitness).length + 88) assigned ≤
      CborSizing.maxMessageSize)
    (server : State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup
      (CborRegistrationCodec.normalize (canonical wire) sender) checks)
      (PqxdhServerRegistrationPublication.candidateTail (associatedData := associatedData) setup.source candidate root data associatedData server)).run state =
      (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
        (PqxdhServerRegistrationPublication.candidateTail (associatedData := associatedData) setup.source candidate root data associatedData server)).run state := by
  simp only [PqxdhServerRegistrationPublication.candidateTail, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    StateT.run_pure, pure_bind]
  cases checks.beaconIdentity candidate.beacon_identity_public_key <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_pure, pure_bind, simulateQ_pure]
  cases checks.reservePeer <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_pure, StateT.run_pure]
  cases initialized : Refinement.ServerTransactionRefinement.initializeCandidate candidate
      (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse setup.source.crypto) <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure]
  case ok kernel =>
    have initial : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel :=
      (PqxdhServerRegistrationPublication.candidate_initialization setup.source candidate root).symm.trans initialized
    split <;> (try simp only [simulateQ_pure, StateT.run_pure])
    split <;> (try simp only [simulateQ_pure, StateT.run_pure])
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_pure, pure_bind]
    cases checks.reservePlaintext (8 + (data.getD registrationWitness).length) <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
        simulateQ_pure, StateT.run_pure]
    cases bindingEq : candidate.key_id_binding <;>
      simp only [simulateQ_pure, StateT.run_pure]
    case ok binding =>
      simp only [simulateQ_map, StateT.run_map]
      rw [after_raw (associatedData := associatedData) setup wire checks lengths parser sender candidate pinned root kernel initial _
        assigned (by
          have total : (PqxdhRefinement.absBytes binding.bytes ++ data.getD registrationWitness).length + 80 =
              (data.getD registrationWitness).length + 88 := by
            have width := (authenticated_length binding (data.getD registrationWitness)).1
            omega
          rw [total]
          exact admitted)]

theorem build_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack wire) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes) (assigned : Nat)
    (admitted : CborSizing.responseLen ((data.getD registrationWitness).length + 88) assigned ≤
      CborSizing.maxMessageSize)
    (server : State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup
      (CborRegistrationCodec.normalize (canonical wire) server.identityKeyId) checks)
      (PqxdhServerRegistrationPublication.build (associatedData := associatedData) setup.source pending root data associatedData server)).run state =
      (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
        (PqxdhServerRegistrationPublication.build (associatedData := associatedData) setup.source pending root data associatedData server)).run state := by
  unfold build
  cases next : pqxdh.server_next_key_id server.control <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure]
  case ok result =>
    cases result <;> simp only [simulateQ_pure, StateT.run_pure]
    case Ok key =>
      cases prepared : pqxdh.server_prepare_commit server.control pending
          ⟨server.server.identity, server.identityKeyId⟩
          (if (server.server.peers key).isSome then .Occupied else .Available) <;>
        simp only [simulateQ_pure, StateT.run_pure]
      case ok result =>
        cases result <;> simp only [simulateQ_pure, StateT.run_pure]
        case Ok candidate =>
          obtain ⟨_, _, pinned, _, _⟩ := PqxdhServerAuthNegativeControl.prepare_commit_fields
            server.control pending ⟨server.server.identity, server.identityKeyId⟩ _ candidate prepared
          exact candidate_raw (associatedData := associatedData) setup wire checks lengths parser server.identityKeyId candidate pinned root data assigned
            admitted server state

/-- The full moved-token build retains pending-token consumption, installed peers, counters, commitment cache and private seal log on every outcome. -/
theorem native_build_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack wire) (session : Nat) (data : Option Pqxdh.Bytes) (assigned : Nat)
    (admitted : CborSizing.responseLen ((data.getD registrationWitness).length + 88) assigned ≤
      CborSizing.maxMessageSize) (state : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhServerAuthNative.nativeBuild setup
        (CborRegistrationCodec.normalize (canonical wire) state.2.server.identityKeyId) checks session data state =
      PqxdhServerAuthNative.nativeBuild setup (CborRegistrationCodec.raw wire) checks session data state := by
  simp only [PqxdhServerAuthNative.nativeBuild, PqxdhServerAuthNative.nativeGet_bind]
  cases found : state.2.pending session
  case none => rfl
  case some token =>
    cases guard : prehash state.2.server token.pending data
    case none => simp only [guard]
    case some candidate =>
      simp only [guard, PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeHash, bind_map_left]
      apply bind_congr
      intro hashed
      simp only [PqxdhServerAuthNative.nativeGet, PqxdhServerAuthNative.localState,
        PqxdhServerAuthNative.nativeCoins, PqxdhServerAuthNative.nativeSet, pure_bind, bind_map_left,
        build_raw (PqxdhTranscriptAd.adOf hashed.1) setup wire checks lengths parser token.pending token.root data
          assigned admitted]

end BeaconcryptCore.Computational.CborRawCanonicalBuild

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.native_build_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.native_build_raw

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.frame_readBack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.frame_readBack

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.canonical_written' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.canonical_written

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.first_frame_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.first_frame_fits

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.shared_seal_render' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.shared_seal_render

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.native_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.native_seal

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.log_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.log_map

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.tail_seal_render' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.tail_seal_render

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.send_program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.send_program_run

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.send_render' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.send_render

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.after_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.after_raw

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.candidate_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.candidate_raw

/-- info: 'BeaconcryptCore.Computational.CborRawCanonicalBuild.build_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCanonicalBuild.build_raw
