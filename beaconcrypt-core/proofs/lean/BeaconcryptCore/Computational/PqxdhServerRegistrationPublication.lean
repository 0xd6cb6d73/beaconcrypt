import BeaconcryptCore.Computational.PqxdhRootTableInitialization
import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxServerRouting
import BeaconcryptCore.Refinement.ServerTransactionRefinement

/-!
The private Server registration-response tail uses the already-produced root and already-consumed registration context. It rechecks current allocation control, binding and peer availability before identity parsing or reservation. The extracted candidate initializer executes the same fixed-source 64-byte call, then plaintext admission and allocation precede the actual first-send driver. Authenticated plaintext is erased before the optional seal result is inspected. Phase2 serialization precedes candidate commit and same-handle peer publication. Failed sealing may advance the local candidate, which remains unpublished on any ordinary failure.

The direct source equations preserve exact supplied callback arguments, original optional results, prior logical map/control and every normal auxiliary/primitive poststate. Totality over all typed replies excludes diagnostic loss of poststate. Arbitrary stateful probabilistic tail support separately retains send, erase and writer poststates. The seven private source categories each have a checked one-call cap, and native seal expansion separately preserves KDF, AEAD, commitment-hash, inner-frame-writer and auxiliary counts. Fixed initial HKDF, preparation, binding bytes, copies, allocation, erasure and serialization remain real local work; logical callback budgets do not assert zero sampling or native execution cost inside their implementations.

This is a supplied-root source-tail interface, not a new root sampler or a completed global registration experiment. All kernels, root and consumed context are private protocol data. The source equations use explicit functional/stateful callback models; they do not independently prove native allocation, identity parsing, zeroization, packed-codec, HashMap, compiler or library implementation behavior. Functional map publication does not claim crash-atomic native insertion/control assignment or erase reservation-capacity effects. The earlier private generation/authentication/root experiment, dynamic registration policy and native lifetime/ownership/reveal/global security connection remain separate. No injectivity, independent owner key, authentication or primitive-hardness premise is introduced.
-/

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.ServerTransactionRefinement
open BeaconcryptCore.Computational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

private theorem id_bind_eq {α β : Type} (value : Id α) (next : α → Id β) :
    value >>= next = next value := rfl

private theorem state_bind_eq {α β S : Type} (first : StateM S α)
    (next : α → StateM S β) (state : S) :
    (first >>= next) state = next (first state).1 (first state).2 := rfl

private theorem state_pure_eq {α S : Type} (value : α) (state : S) :
    (pure value : StateM S α) state = (value, state) := rfl

private theorem rust_ok_map {α β : Type} (f : α → β) (value : α) :
    f <$> (ok value : RustM α) = ok (f value) := rfl

abbrev Bytes := Pqxdh.Bytes
abbrev Identity := RawCtxServerRouting.Identity

/-- These are the original Phase2 setter inputs, before optional packed serialization. -/
structure ResponseFields where
  keyId : Std.U64
  ephemeral : Std.Array Std.U8 32#usize
  identity : Identity
  kemCiphertext : Std.Array Std.U8 1088#usize
  appCiphertext : Bytes

def responseFields (candidate : pqxdh.ServerRegistrationCandidate)
    (encrypted : RawCtxSourceSend.Encrypted) : ResponseFields :=
  ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
    candidate.kem_ciphertext, encrypted.ciphertext⟩

structure Response where
  serialized : Bytes
  keyId : Std.U64

/-- Existing peer state, allocation control and the already-consumed registration context. -/
structure State (Metadata PeerMetadata Consumed : Type) where
  server : RawCtxServerRouting.Server Metadata PeerMetadata
  identityKeyId : Std.U64
  control : pqxdh.ServerState
  consumed : Consumed

inductive AuxQuery where
  | checkIdentity : Identity → AuxQuery
  | reservePeer : AuxQuery
  | reservePlaintext : Nat → AuxQuery
  | erase : Bytes → AuxQuery
  | write : ResponseFields → AuxQuery

abbrev AuxSpec : OracleSpec AuxQuery
  | .checkIdentity _ => Bool
  | .reservePeer => Bool
  | .reservePlaintext _ => Bool
  | .erase _ => Unit
  | .write _ => Option Bytes

abbrev TailSpec := RawCtxSourceSend.PrimitiveSpec + AuxSpec
abbrev NativeSpec := RawCtxSourceSeal.NativeSpec + AuxSpec

def sendLift : QueryImpl RawCtxSourceSend.PrimitiveSpec (OracleComp TailSpec) :=
  fun query => liftM (TailSpec.query (.inl query))

def nativeAdapter : QueryImpl TailSpec (OracleComp NativeSpec)
  | .inl query => simulateQ (fun request => liftM (NativeSpec.query (.inl request)))
      (RawCtxSourceSeal.nativeAdapter query)
  | .inr fields => liftM (NativeSpec.query (.inr fields))

/-- Install exactly the committed candidate and the advanced first-send kernel. -/
def publish {Metadata PeerMetadata Consumed : Type}
    (state : State Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (metadata : PeerMetadata) : State Metadata PeerMetadata Consumed :=
  { state with
    control := candidate.next_state
    server := { state.server with peers := Function.update state.server.peers candidate.key_id (some ⟨candidate.beacon_identity_public_key, kernel, metadata⟩) } }

def firstContext (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Bytes) : RawCtxSourceSend.SealContext :=
  ⟨authenticated, candidate.key_id, candidate.server_identity_key_id,
    absBytes candidate.associated_data⟩

/-- The post-allocation source tail runs the first send before Phase2 serialization and publication. -/
noncomputable def afterInitialization {Metadata PeerMetadata Consumed : Type}
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (Option Response × State Metadata PeerMetadata Consumed) := do
  let (advanced, encrypted) ← simulateQ sendLift (simulateQ RawCtxSourceSend.adapter
    (RawCtxSourceSend.send kernel (firstContext candidate authenticated)))
  let _ ← TailSpec.query (.inr (.erase authenticated))
  match encrypted with
  | none => pure (none, state)
  | some encrypted =>
      let serialized ← TailSpec.query (.inr (.write (responseFields candidate encrypted)))
      match serialized with
      | none => pure (none, state)
      | some serialized => pure (some ⟨serialized, candidate.key_id⟩, publish state candidate advanced metadata)

theorem publish_commit {Metadata PeerMetadata Consumed : Type}
    (state : State Metadata PeerMetadata Consumed) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata) :
    pqxdh.server_commit candidate = ok
      ((publish state candidate kernel metadata).control,
        ⟨candidate.key_id, candidate.beacon_identity_public_key, candidate.associated_data⟩) := rfl

theorem publish_fields {Metadata PeerMetadata Consumed : Type}
    (state : State Metadata PeerMetadata Consumed) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata) :
    (publish state candidate kernel metadata).server.peers candidate.key_id =
        some ⟨candidate.beacon_identity_public_key, kernel, metadata⟩ ∧
      (publish state candidate kernel metadata).server.identity = state.server.identity ∧
      (publish state candidate kernel metadata).server.metadata = state.server.metadata ∧
      (publish state candidate kernel metadata).consumed = state.consumed ∧
      ∀ key, key ≠ candidate.key_id →
        (publish state candidate kernel metadata).server.peers key = state.server.peers key := by
  refine ⟨?_, rfl, rfl, rfl, fun key hkey => Function.update_of_ne hkey ..⟩
  simp only [publish, Function.update_self]

/-- Source diagnostic failure/divergence is retained, not turned into optional rejection. -/
def continueRust {α β ι : Type} {spec : OracleSpec ι} (result : RustM α)
    (continuation : α → OracleComp spec (RustM β)) : OracleComp spec (RustM β) :=
  match result with
  | .ok value => continuation value
  | .fail error => pure (.fail error)
  | .div => pure .div

def registrationWitness : Bytes := [255]

/-- All callbacks are private source effects, including allocation and zeroization. -/
noncomputable def candidateTail {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) := do
  let valid ← TailSpec.query (.inr (.checkIdentity candidate.beacon_identity_public_key))
  if !valid then pure (ok (none, state)) else do
    let reserved ← TailSpec.query (.inr .reservePeer)
    if !reserved then pure (ok (none, state)) else
      continueRust (initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
        (PqxdhRootTableInitialization.initialResponse source.crypto)) fun kernel => do
        let plaintext := data.getD registrationWitness
        if plaintext.isEmpty then pure (ok (none, state))
        else if 8 + plaintext.length ≤ Usize.max then do
          let allocated ← TailSpec.query (.inr (.reservePlaintext (8 + plaintext.length)))
          if !allocated then pure (ok (none, state)) else
            continueRust (candidate.key_id_binding) fun binding =>
              ok <$> afterInitialization candidate (absBytes binding.bytes ++ plaintext)
                kernel metadata state
        else pure (ok (none, state))

/-- The native builder rechecks allocation and the current binding before any tail effect. -/
noncomputable def build {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
  continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        continueRust (pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => candidateTail source candidate root data metadata state

theorem candidate_initialization
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput) :
    initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
        (PqxdhRootTableInitialization.initialResponse source.crypto) =
      PqxdhRootTableInitialization.initialKernelRun source false root := rfl

theorem candidate_binding (candidate : pqxdh.ServerRegistrationCandidate) :
    ∃ binding, candidate.key_id_binding = ok binding ∧
      absBytes binding.bytes = Pqxdh.LE64 candidate.key_id.val :=
  registration_key_id_binding_abs candidate.key_id

/-- The actual fixed-width binding prefix makes the inner send's empty-input guard unreachable. -/
theorem authenticated_length (binding : pqxdh.RegistrationKeyIdBinding) (plaintext : Bytes) :
    (absBytes binding.bytes ++ plaintext).length = 8 + plaintext.length ∧
      (absBytes binding.bytes ++ plaintext).isEmpty = false := by
  have hlength : (absBytes binding.bytes ++ plaintext).length = 8 + plaintext.length := by
    simp [absBytes_length]
  refine ⟨hlength, ?_⟩
  have hne : absBytes binding.bytes ++ plaintext ≠ [] := by
    intro h
    have hz := congrArg List.length h
    simp only [hlength, List.length_nil] at hz
    omega
  simpa only [List.isEmpty_eq_false_iff] using hne

/-- Actual source send effects advance the private candidate even when its frame fails. -/
theorem first_send_state {PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (primitive : PrimitiveState)
    (hzero : kernel.refined.control.send_sequence.val = 0)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × PrimitiveState)
    (hsupport : sent ∈ support ((simulateQ impl (simulateQ sendLift
      (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send kernel (firstContext candidate authenticated))))).run primitive)) :
    sent.1.1.refined.control.send_sequence.val = 1 ∧
      sent.1.1.refined.control.receive_sequence = kernel.refined.control.receive_sequence ∧
      sent.1.1.refined.control.receive_cache = kernel.refined.control.receive_cache ∧
      sent.1.1.refined.receive_chain = kernel.refined.receive_chain ∧
      sent.1.1.refined.receive_slots = kernel.refined.receive_slots := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at hsupport
  have hmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro h
    have hv := congrArg UScalar.val h
    simp only [hzero] at hv
    contradiction
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hstate⟩ :=
    RawCtxSourceSend.send_nonexhausted_support _ kernel (firstContext candidate authenticated)
      primitive hmax sent hsupport
  simpa only [hzero, Nat.zero_add] using hstate

def functionalImpl {PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState) : QueryImpl TailSpec (StateM PrimitiveState)
  | .inl (.inl request) => fun state => execute state request
  | .inl (.inr input) => fun state => sealReply state input
  | .inr query => aux query

def selectedSeal {PrimitiveState : Type}
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (primitive : PrimitiveState) (pending : SendSeal RawCtxSourceSend.SealContext) :
    Option RawCtxSourceSend.Encrypted × PrimitiveState :=
  let result := sealReply primitive (RawCtxSourceSend.arguments pending)
  (result.1.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)), result.2)

set_option backward.isDefEq.respectTransparency false in
theorem functional_send {PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState) :
    (functionalImpl execute sealReply aux ∘ₛ sendLift) ∘ₛ RawCtxSourceSend.adapter =
      RawCtxSourceSend.deterministicImpl execute (selectedSeal sealReply) := by
  funext query primitive
  cases query <;> simp only [QueryImpl.compose, RawCtxSourceSend.adapter,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sendLift, functionalImpl,
    RawCtxSourceSend.deterministicImpl, selectedSeal]
  rfl

/-- Direct extracted send/finish, then actual erase/writer effects, then logical publication. -/
def sourceAfterInitialization {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState) :
    RustM ((Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) := do
  let (sent, afterSend) ← RawCtxSourceSend.sourceDriver execute (selectedSeal sealReply)
    kernel (firstContext candidate authenticated) primitive
  let (_, afterErase) := aux (.erase authenticated) afterSend
  match sent.2 with
  | none => ok ((none, state), afterErase)
  | some encrypted =>
      let (written, afterWrite) := aux (.write (responseFields candidate encrypted)) afterErase
      match written with
      | none => ok ((none, state), afterWrite)
      | some bytes => ok ((some ⟨bytes, candidate.key_id⟩,
          publish state candidate sent.1 metadata), afterWrite)

set_option backward.isDefEq.respectTransparency false in
theorem source_afterInitialization_exact {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState) :
    sourceAfterInitialization execute sealReply aux candidate authenticated kernel metadata state primitive =
      ok ((simulateQ (functionalImpl execute sealReply aux)
        (afterInitialization candidate authenticated kernel metadata state)).run primitive) := by
  rw [sourceAfterInitialization, RawCtxSourceSend.sourceDriver_exact]
  simp only [afterInitialization, simulateQ_bind, bind_tc_ok]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, functional_send]
  simp only [simulateQ_spec_query, functionalImpl, StateT.run_bind]
  generalize (simulateQ (RawCtxSourceSend.deterministicImpl execute (selectedSeal sealReply))
    (RawCtxSourceSend.send kernel (firstContext candidate authenticated))).run primitive = sent
  rcases sent with ⟨⟨advanced, encrypted⟩, afterSend⟩
  cases encrypted <;> try rfl
  rename_i encrypted
  change (let (written, afterWrite) := aux (.write (responseFields candidate encrypted)) (aux (.erase authenticated) afterSend).2
    match written with
    | none => ok ((none, state), afterWrite)
    | some bytes => ok ((some (Response.mk bytes candidate.key_id),
        publish state candidate advanced metadata), afterWrite)) =
    ok ((simulateQ (functionalImpl execute sealReply aux) (do
      let written ← TailSpec.query (.inr (.write (responseFields candidate encrypted)))
      match written with
      | none => pure (none, state)
      | some bytes => pure (some (Response.mk bytes candidate.key_id),
          publish state candidate advanced metadata))).run (aux (.erase authenticated) afterSend).2)
  simp only [simulateQ_bind, simulateQ_spec_query, functionalImpl, StateT.run_bind]
  simp only [StateT.run]
  generalize aux (.write (responseFields candidate encrypted)) (aux (.erase authenticated) afterSend).2 = written
  rcases written with ⟨written, afterWrite⟩
  cases written <;> rfl

/-- Pair the successful source result with its complete primitive state; diagnostic RustM outcomes remain diagnostic. -/
def collectState {α PrimitiveState : Type} (result : RustM α × PrimitiveState) :
    RustM (α × PrimitiveState) := (fun value => (value, result.2)) <$> result.1

private theorem collect_ok {α S : Type} (work : StateM S α) (state : S) :
    collectState ((ok <$> work).run state) = ok (work.run state) := rfl

def Normal {α ι : Type} {spec : OracleSpec ι} (work : OracleComp spec (RustM α)) : Prop :=
  ∀ output ∈ support work, ∃ value, output = ok value

private theorem normal_pure {α ι : Type} {spec : OracleSpec ι} (value : α) :
    Normal (pure (ok value) : OracleComp spec (RustM α)) := by
  intro output houtput
  simp only [mem_support_pure_iff] at houtput
  exact ⟨value, houtput⟩

private theorem normal_bind {α β ι : Type} {spec : OracleSpec ι}
    (first : OracleComp spec β) (next : β → OracleComp spec (RustM α))
    (hnormal : ∀ value, Normal (next value)) : Normal (first >>= next) := by
  intro output houtput
  simp only [mem_support_bind_iff] at houtput
  obtain ⟨value, _, hnext⟩ := houtput
  exact hnormal value output hnext

private theorem normal_map {α ι : Type} {spec : OracleSpec ι} (work : OracleComp spec α) :
    Normal (ok <$> work) := by
  intro output houtput
  rw [support_map] at houtput
  obtain ⟨value, _, rfl⟩ := houtput
  exact ⟨value, rfl⟩

/-- Every possible typed callback continuation returns a normal source result. -/
theorem candidate_normal {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Bytes) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    Normal (candidateTail source candidate root data metadata state) := by
  obtain ⟨kernel, hinitial⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok
    (PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray root))
    (PqxdhRootTableInitialization.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, ratchet.SYM_RATCHET_INFO⟩)
  have hinit : initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse source.crypto) = ok kernel := by
    simpa only [initializeCandidate_eq, initializeServer_eq] using hinitial
  obtain ⟨binding, hbinding, _⟩ := candidate_binding candidate
  simp only [candidateTail, hinit, hbinding, continueRust]
  apply normal_bind
  intro valid
  cases valid
  · exact normal_pure _
  · apply normal_bind
    intro reserved
    cases reserved
    · exact normal_pure _
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      split_ifs
      · exact normal_pure _
      · apply normal_bind
        intro allocated
        cases allocated
        · exact normal_pure _
        · exact normal_map _
      · exact normal_pure _

def sourceCandidateTail {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    RustM ((Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) :=
  let (valid, afterCheck) := aux (.checkIdentity candidate.beacon_identity_public_key) primitive
  if !valid then ok ((none, state), afterCheck) else
    let (reserved, afterReserve) := aux .reservePeer afterCheck
    if !reserved then ok ((none, state), afterReserve) else do
      let kernel ← initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
        (PqxdhRootTableInitialization.initialResponse source.crypto)
      let plaintext := data.getD registrationWitness
      if plaintext.isEmpty then ok ((none, state), afterReserve)
      else if 8 + plaintext.length ≤ Usize.max then
        let (allocated, afterAllocation) := aux (.reservePlaintext (8 + plaintext.length)) afterReserve
        if !allocated then ok ((none, state), afterAllocation) else do
          let binding ← candidate.key_id_binding
          sourceAfterInitialization execute sealReply aux candidate
            (absBytes binding.bytes ++ plaintext) kernel metadata state afterAllocation
      else ok ((none, state), afterReserve)

set_option backward.isDefEq.respectTransparency false in
theorem source_candidateTail_exact {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    sourceCandidateTail execute sealReply aux source candidate root data metadata state primitive =
      collectState ((simulateQ (functionalImpl execute sealReply aux)
        (candidateTail source candidate root data metadata state)).run primitive) := by
  obtain ⟨kernel, hinitial⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok
    (PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray root))
    (PqxdhRootTableInitialization.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, ratchet.SYM_RATCHET_INFO⟩)
  have hinit : initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse source.crypto) = ok kernel := by
    simpa only [initializeCandidate_eq, initializeServer_eq] using hinitial
  obtain ⟨binding, hbinding, _⟩ := candidate_binding candidate
  simp only [sourceCandidateTail, candidateTail, hinit, hbinding, continueRust,
    simulateQ_bind, simulateQ_spec_query, functionalImpl, StateT.run_bind, bind_tc_ok]
  simp only [StateT.run, id_bind_eq]
  split_ifs <;> simp_all only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query,
    functionalImpl, ite_true, ite_false, Bool.false_eq_true, collectState,
    state_bind_eq, state_pure_eq, rust_ok_map]
  generalize aux (.reservePlaintext (8 + (data.getD registrationWitness).length))
    (aux .reservePeer (aux (.checkIdentity candidate.beacon_identity_public_key) primitive).2).2 = allocation
  rcases allocation with ⟨allocated, afterAllocation⟩
  cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_true, ite_false, simulateQ_pure, state_pure_eq, rust_ok_map, simulateQ_map]
  all_goals try rfl
  change sourceAfterInitialization execute sealReply aux candidate
      (Pqxdh.LE64 candidate.key_id.val ++ data.getD registrationWitness) kernel metadata state afterAllocation =
    collectState ((ok <$> simulateQ (functionalImpl execute sealReply aux)
      (afterInitialization candidate (Pqxdh.LE64 candidate.key_id.val ++ data.getD registrationWitness)
        kernel metadata state)).run afterAllocation)
  rw [collect_ok]
  exact source_afterInitialization_exact ..

def sourceBuild {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    RustM ((Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) := do
  let next ← pqxdh.server_next_key_id state.control
  match next with
  | .Err _ => ok ((none, state), primitive)
  | .Ok next =>
      let availability := if (state.server.peers next).isSome then
        pqxdh.KeyIdAvailability.Occupied else .Available
      let prepared ← pqxdh.server_prepare_commit state.control pending
        ⟨state.server.identity, state.identityKeyId⟩ availability
      match prepared with
      | .Err _ => ok ((none, state), primitive)
      | .Ok candidate => sourceCandidateTail execute sealReply aux source candidate root data metadata state primitive

set_option backward.isDefEq.respectTransparency false in
theorem source_build_exact {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    sourceBuild execute sealReply aux source pending root data metadata state primitive =
      collectState ((simulateQ (functionalImpl execute sealReply aux)
        (build source pending root data metadata state)).run primitive) := by
  simp only [sourceBuild, build]
  cases hn : pqxdh.server_next_key_id state.control with
  | fail => rfl
  | div => rfl
  | ok next =>
      cases next with
      | Err => rfl
      | Ok next =>
          simp only [continueRust, bind_tc_ok]
          cases hp : pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail => rfl
          | div => rfl
          | ok prepared =>
              cases prepared with
              | Err => rfl
              | Ok candidate => exact source_candidateTail_exact ..

/-- Every optional branch retains the actual send and writer poststates; publication is last. -/
theorem afterInitialization_support {Metadata PeerMetadata Consumed PrimitiveState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState)
    (result : (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl
      (afterInitialization candidate authenticated kernel metadata state)).run primitive)) :
    ∃ sent afterSend afterErase,
      (sent, afterSend) ∈ support ((simulateQ impl (simulateQ sendLift
        (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send kernel (firstContext candidate authenticated))))).run primitive) ∧
      ((), afterErase) ∈ support ((impl (.inr (.erase authenticated))).run afterSend) ∧
      match sent.2 with
      | none => result = ((none, state), afterErase)
      | some encrypted => ∃ written afterWrite,
          (written, afterWrite) ∈ support ((impl (.inr (.write (responseFields candidate encrypted)))).run afterErase) ∧
          result = ((written.map (fun bytes => ⟨bytes, candidate.key_id⟩),
            if written.isSome then publish state candidate sent.1 metadata else state), afterWrite) := by
  simp only [afterInitialization, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hsupport
  obtain ⟨⟨sent, afterSend⟩, hsent, hnext⟩ := hsupport
  simp only [simulateQ_spec_query] at hnext
  obtain ⟨⟨erased, afterErase⟩, herased, hnext⟩ := hnext
  cases erased
  refine ⟨sent, afterSend, afterErase, hsent, herased, ?_⟩
  cases he : sent.2 with
  | none =>
      simpa only [he, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using hnext
  | some encrypted =>
      simp only [he, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hnext
      obtain ⟨⟨written, afterWrite⟩, hwritten, hresult⟩ := hnext
      refine ⟨written, afterWrite, hwritten, ?_⟩
      cases written <;> simpa only [simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff, Option.map_none, Option.map_some, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, ite_false, ite_true] using hresult

/-- Current-control rejection and every typed candidate continuation return normally. -/
theorem build_normal {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    Normal (build source pending root data metadata state) := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, continueRust]
  cases next with
  | Err => exact normal_pure _
  | Ok next =>
    obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
      state.control pending ⟨state.server.identity, state.identityKeyId⟩
      (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
    simp only [hprepared]
    cases prepared with
    | Err => exact normal_pure _
    | Ok candidate => exact candidate_normal source candidate root data metadata state

private theorem normal_run {α PrimitiveState ι κ : Type}
    {source : OracleSpec ι} {base : OracleSpec κ}
    (impl : QueryImpl source (StateT PrimitiveState (OracleComp base)))
    (work : OracleComp source (RustM α)) (hnormal : Normal work)
    (state : PrimitiveState) (result : RustM α × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl work).run state)) :
    ∃ value, result.1 = ok value := by
  apply hnormal
  apply OracleComp.support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ hsupport

/-- No source diagnostic hides a primitive poststate in any interpreted builder execution. -/
theorem build_run_normal {Metadata PeerMetadata Consumed PrimitiveState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl
      (build source pending root data metadata state)).run primitive)) :
    ∃ value, result = (ok value, result.2) := by
  obtain ⟨value, hvalue⟩ := normal_run impl _ (build_normal source pending root data metadata state)
    primitive result hsupport
  exact ⟨value, Prod.ext hvalue rfl⟩

inductive CallKind where
  | kdf | seal | identity | peerReserve | plaintextReserve | erase | writer
  deriving DecidableEq

def auxKind : AuxQuery → CallKind
  | .checkIdentity _ => .identity
  | .reservePeer => .peerReserve
  | .reservePlaintext _ => .plaintextReserve
  | .erase _ => .erase
  | .write _ => .writer

def callKind : TailSpec.Domain → CallKind
  | .inl (.inl _) => .kdf
  | .inl (.inr _) => .seal
  | .inr query => auxKind query

private theorem sendLift_bound {α : Type} (kind : CallKind)
    (work : OracleComp RawCtxSourceSend.PrimitiveSpec α) (budget : Nat)
    (hbound : work.IsQueryBoundP
      (fun query => (if query.isLeft then CallKind.kdf else .seal) = kind) budget) :
    (simulateQ sendLift work).IsQueryBoundP (fun query => callKind query = kind) budget := by
  apply RawCtxSourceOpen.simulate_bound sendLift _ _ work budget hbound
  intro query
  change (liftM (TailSpec.query (.inl query)) : OracleComp TailSpec _).IsQueryBoundP _ _
  rw [isQueryBoundP_query_iff]
  cases query <;> simp only [callKind, Sum.isLeft, ite_true]
  all_goals split_ifs <;> simp_all

private theorem selected_bound (kernel : ConcreteRatchetKernel)
    (context : RawCtxSourceSend.SealContext) (kind : CallKind) :
    (simulateQ sendLift (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send kernel context))).IsQueryBoundP
      (fun query => callKind query = kind)
      (if kind = .kdf ∨ kind = .seal then 1 else 0) := by
  apply sendLift_bound
  cases kind
  case kdf =>
    apply (isQueryBoundP_congr_pred (p' := fun query => query.isLeft = true)
      (fun query => by cases query <;> simp)).mpr
    exact (RawCtxSourceSend.selected_bounds kernel context).1
  case «seal» =>
    apply (isQueryBoundP_congr_pred (p' := fun query => query.isLeft = false)
      (fun query => by cases query <;> simp)).mpr
    exact (RawCtxSourceSend.selected_bounds kernel context).2
  all_goals
    apply (isQueryBoundP_congr_pred (p' := fun _ => False)
      (fun query => by cases query <;> simp)).mpr
    exact isQueryBoundP_false _ _

def afterAllowance (kind : CallKind) : Nat :=
  if kind = .kdf ∨ kind = .seal ∨ kind = .erase ∨ kind = .writer then 1 else 0

/-- The initialized tail pays once for KDF, sealing, erasure and optional Phase2 writing. -/
theorem afterInitialization_bound {Metadata PeerMetadata Consumed : Type}
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (afterInitialization candidate authenticated kernel metadata state).IsQueryBoundP
      (fun query => callKind query = kind) (afterAllowance kind) := by
  unfold afterInitialization
  refine (isQueryBoundP_bind (selected_bound kernel (firstContext candidate authenticated) kind)
    (m := if kind = .erase ∨ kind = .writer then 1 else 0) (fun sent _ => ?_)).mono ?_
  · rw [isQueryBoundP_query_bind_iff]
    constructor
    · cases kind <;> simp [callKind, auxKind]
    · intro erased
      cases erased
      cases sent.2 with
      | none => exact isQueryBoundP_pure _ _ _
      | some encrypted =>
        rw [isQueryBoundP_query_bind_iff]
        constructor
        · cases kind <;> simp [callKind, auxKind]
        · intro serialized
          cases serialized <;> exact isQueryBoundP_pure _ _ _
  · cases kind <;> simp [afterAllowance]

/-- Each original candidate-tail effect category is charged at most once, including rejected attempts. -/
theorem candidate_bound {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (candidateTail source candidate root data metadata state).IsQueryBoundP
      (fun query => callKind query = kind) 1 := by
  obtain ⟨kernel, hinitial⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok
    (PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray root))
    (PqxdhRootTableInitialization.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, ratchet.SYM_RATCHET_INFO⟩)
  have hinit : initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse source.crypto) = ok kernel := by
    simpa only [initializeCandidate_eq, initializeServer_eq] using hinitial
  obtain ⟨binding, hbinding, _⟩ := candidate_binding candidate
  simp only [candidateTail, hinit, hbinding, continueRust]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun valid => ?_⟩
  cases valid
  · exact isQueryBoundP_pure _ _ _
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · cases kind <;> simp [callKind, auxKind]
    · intro reserved
      cases reserved
      · exact isQueryBoundP_pure _ _ _
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · exact isQueryBoundP_pure _ _ _
        · split
          · rw [isQueryBoundP_query_bind_iff]
            constructor
            · cases kind <;> simp [callKind, auxKind]
            · intro allocated
              cases allocated
              · exact isQueryBoundP_pure _ _ _
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false, isQueryBoundP_map_iff]
                apply (afterInitialization_bound candidate _ kernel metadata state kind).mono
                cases kind <;> simp [callKind, auxKind, afterAllowance]
          · exact isQueryBoundP_pure _ _ _

/-- Preparation adds no callback, so all seven classes retain the complete builder's one-call cap. -/
theorem build_bound {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (build source pending root data metadata state).IsQueryBoundP
      (fun query => callKind query = kind) 1 := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, continueRust]
  cases next with
  | Err => exact isQueryBoundP_pure _ _ _
  | Ok next =>
    obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
      state.control pending ⟨state.server.identity, state.identityKeyId⟩
      (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
    simp only [hprepared]
    cases prepared with
    | Err => exact isQueryBoundP_pure _ _ _
    | Ok candidate => exact candidate_bound source candidate root data metadata state kind

def leftPredicate (predicate : RawCtxSourceSeal.NativeSpec.Domain → Bool) : NativeSpec.Domain → Bool
  | .inl query => predicate query
  | .inr _ => false

private theorem nativeLift_bound {α : Type}
    (predicate : RawCtxSourceSeal.NativeSpec.Domain → Bool)
    (work : OracleComp RawCtxSourceSeal.NativeSpec α) (budget : Nat)
    (hbound : work.IsQueryBoundP (fun query => predicate query = true) budget) :
    (simulateQ (fun query => liftM (NativeSpec.query (.inl query))) work : OracleComp NativeSpec α).IsQueryBoundP
      (fun query => leftPredicate predicate query = true) budget := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work budget hbound
  intro query
  change (liftM (NativeSpec.query (.inl query)) : OracleComp NativeSpec _).IsQueryBoundP _ _
  rw [isQueryBoundP_query_iff]
  simp only [leftPredicate]
  split_ifs <;> simp_all

/-- Native expansion preserves the actual source ratchet-KDF count. -/
theorem native_kdf_bound {α : Type} (work : OracleComp TailSpec α) (budget : Nat)
    (hbound : work.IsQueryBoundP (fun query => callKind query = .kdf) budget) :
    (simulateQ nativeAdapter work).IsQueryBoundP
      (fun query => leftPredicate Sum.isLeft query = true) budget := by
  apply RawCtxSourceOpen.simulate_bound nativeAdapter _ _ work budget hbound
  intro query
  cases query with
  | inr aux =>
    change (liftM (NativeSpec.query (.inr aux)) : OracleComp NativeSpec _).IsQueryBoundP _ _
    rw [isQueryBoundP_query_iff]
    simp [leftPredicate]
  | inl request =>
    apply nativeLift_bound
    have bounded := RawCtxSourceSeal.nativeAdapter_kdf_bound
      (liftM (RawCtxSourceSend.PrimitiveSpec.query request))
      (if callKind (.inl request) = .kdf then 1 else 0) ?_
    · simpa only [simulateQ_spec_query, OracleSpec.Range, TailSpec,
        OracleSpec.add_apply_inl] using bounded
    · rw [isQueryBoundP_query_iff]
      cases request <;> simp [callKind]

/-- Each selected seal pays separately for its actual AEAD, hash and frame-writing category. -/
theorem native_seal_bound {α : Type} (work : OracleComp TailSpec α) (budget : Nat)
    (hbound : work.IsQueryBoundP (fun query => callKind query = .seal) budget)
    (kind : RawCtxSourceSeal.CallKind) :
    (simulateQ nativeAdapter work).IsQueryBoundP
      (fun query => leftPredicate (RawCtxSourceSeal.category kind) query = true) budget := by
  apply RawCtxSourceOpen.simulate_bound nativeAdapter _ _ work budget hbound
  intro query
  cases query with
  | inr aux =>
    change (liftM (NativeSpec.query (.inr aux)) : OracleComp NativeSpec _).IsQueryBoundP _ _
    rw [isQueryBoundP_query_iff]
    simp [leftPredicate]
  | inl request =>
    apply nativeLift_bound
    have bounded := RawCtxSourceSeal.nativeAdapter_seal_bound
      (liftM (RawCtxSourceSend.PrimitiveSpec.query request))
      (if callKind (.inl request) = .seal then 1 else 0) ?_ kind
    · simpa only [simulateQ_spec_query, OracleSpec.Range, TailSpec,
        OracleSpec.add_apply_inl] using bounded
    · rw [isQueryBoundP_query_iff]
      cases request <;> simp [callKind]

def auxPredicate (kind : CallKind) : NativeSpec.Domain → Bool
  | .inl _ => false
  | .inr query => decide (auxKind query = kind)

/-- Native primitive expansion does not erase or add any private allocation, erasure or Phase2-writing request. -/
theorem native_aux_bound {α : Type} (work : OracleComp TailSpec α) (budget : Nat)
    (kind : CallKind)
    (hbound : work.IsQueryBoundP (fun query => callKind query = kind) budget) :
    (simulateQ nativeAdapter work).IsQueryBoundP
      (fun query => auxPredicate kind query = true) budget := by
  apply RawCtxSourceOpen.simulate_bound nativeAdapter _ _ work budget hbound
  intro query
  cases query with
  | inr aux =>
    change (liftM (NativeSpec.query (.inr aux)) : OracleComp NativeSpec _).IsQueryBoundP _ _
    rw [isQueryBoundP_query_iff]
    simp only [auxPredicate, decide_eq_true_eq, callKind]
    split_ifs <;> simp_all
  | inl request =>
    unfold nativeAdapter
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ _ (isQueryBoundP_false _ _)
    intro nativeQuery
    change (liftM (NativeSpec.query (.inl nativeQuery)) : OracleComp NativeSpec _).IsQueryBoundP _ _
    rw [isQueryBoundP_query_iff]
    simp [auxPredicate]

/-- The full builder inherits all concrete native effect caps without ignoring optional failures. -/
theorem native_build_bounds {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    let work := simulateQ nativeAdapter (build source pending root data metadata state)
    work.IsQueryBoundP (fun query => leftPredicate Sum.isLeft query = true) 1 ∧
      (∀ kind, work.IsQueryBoundP
        (fun query => leftPredicate (RawCtxSourceSeal.category kind) query = true) 1) ∧
      (∀ kind, work.IsQueryBoundP (fun query => auxPredicate kind query = true) 1) := by
  exact ⟨native_kdf_bound _ 1 (build_bound source pending root data metadata state .kdf),
    fun kind => native_seal_bound _ 1 (build_bound source pending root data metadata state .seal) kind,
    fun kind => native_aux_bound _ 1 kind (build_bound source pending root data metadata state kind)⟩

/-- Concrete AEAD/hash/frame expansion retains the normal result and entire final primitive state. -/
theorem native_build_normal {Metadata PeerMetadata Consumed PrimitiveState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (result : RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl (simulateQ nativeAdapter
      (build source pending root data metadata state))).run primitive)) :
    ∃ value, result = (ok value, result.2) := by
  rw [← QueryImpl.simulateQ_compose] at hsupport
  exact build_run_normal _ source pending root data metadata state primitive result hsupport

/-- Candidate initialization uses the supplied root and gives the complete zero-counter, empty-cache source relation. -/
theorem candidate_initial_state {AD PT CT : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput) :
    ∃ kernel, initializeCandidate candidate (PqxdhRootTableInitialization.rootArray root)
        (PqxdhRootTableInitialization.initialResponse source.crypto) = ok kernel ∧
      kernel.refined.control.send_sequence.val = 0 ∧
      KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  obtain ⟨kernel, initialized, _, _, refines⟩ :=
    PqxdhRootTableInitialization.initialize_refines source cr false root
  refine ⟨kernel, (candidate_initialization source candidate root).trans initialized, ?_, refines⟩
  exact refines.sendSequence

end BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.publish_commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.publish_commit

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.publish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.publish_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_initialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_initialization

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_binding

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.authenticated_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.authenticated_length

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.first_send_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.first_send_state

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.functional_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.functional_send

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_afterInitialization_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_afterInitialization_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_candidateTail_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_candidateTail_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.source_build_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.afterInitialization_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.afterInitialization_support

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_run_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_run_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.afterInitialization_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.afterInitialization_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.build_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_kdf_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_seal_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_aux_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_aux_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_build_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_build_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_build_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.native_build_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_initial_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.candidate_initial_state
