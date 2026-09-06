import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxServerRouting

/-!
This module follows native Server encrypt_message routing: read associated data from the requested assigned-ID entry, read the immutable local sender field, select the same mutable peer entry, then call the source send helper. The helper's empty-input rejection occurs after those outer lookups. The metadata accessor is a functional projection of the native identity_key_kid field, not an application input. The same stored peer identity and exact extracted 153-byte AD accompany its whole ratchet; publication replaces only that entry's kernel, even when active sealing fails. Equal identity keys under different assigned handles are allowed.

All eleven statements are operational or query accounting. Actual optional ciphertext replies, complete primitive state and the full map remain in the adaptive send-only program. Source case inversion preserves the same selected entry and advanced kernel, with every receive field unchanged. Server/peer identity and metadata and the raw-receive attempt counter survive adaptive target selection. KDF, AEAD, hash and writer each have cap qSend; primitive work, map lookup, AD construction, byte copying and serialization inside those calls remain separate costs.

The finite-u64 function map, immutable metadata accessor and synchronous whole-kernel representation are explicit source/library boundaries, not native HashMap, field extraction or compiler proofs. The existing ready-slot theorem supplies the normal-return choreography of each selected helper. Actual shared cryptographic instantiation, mixed sends/receives/registrations/reveals, persistence/CAS/crash behavior, evolving-key/session selection and global security reductions remain separate obligations. No injectivity of identity/AD/key terms, canonical serialization, secret target plaintext or new primitive security assumption is used.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxServerSend
open RawCtxServerRouting

/-- Source AD lookup precedes the immutable sender read and same-entry mutable selection, before empty-input rejection. -/
noncomputable def sendServer {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata) :
    OracleComp RawCtxSourceSeal.NativeSpec (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) :=
  match peerAssociatedData state.server kid with
  | none => pure (none, state)
  | some ad =>
      let sender := senderId state.server.metadata
      match state.server.peers kid with
      | none => pure (none, state)
      | some peer => do
          let result ← simulateQ RawCtxSourceSeal.nativeAdapter
            ((RawCtxSourceSend.sendOwner sender plaintext).run
              ⟨selectedOwner kid ad peer, state.rawAttempts⟩)
          pure (result.1, ⟨putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)

/-- Missing assigned handles reject before the ratchet or any private primitive invocation. -/
theorem sendServer_missing {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata)
    (hpeer : state.server.peers kid = none) :
    sendServer senderId plaintext kid state = pure (none, state) := by
  simp [sendServer, peerAssociatedData, hpeer]

/-- The same actual map entry supplies identity-derived AD, selected ratchet and publication handle. -/
theorem sendServer_selected {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata)
    (peer : Peer PeerMetadata) (hpeer : state.server.peers kid = some peer) :
    sendServer senderId plaintext kid state = (do
      let result ← simulateQ RawCtxSourceSeal.nativeAdapter
        ((RawCtxSourceSend.sendOwner (senderId state.server.metadata) plaintext).run
          ⟨selectedOwner kid (associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩)
      pure (result.1, ⟨putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)) := by
  simp only [sendServer, peerAssociatedData, hpeer, Bind.bind, Option.bind, pure]

/-- Complete primitive state is retained outside synchronous whole-map publication. -/
noncomputable def sendGame {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) :
    OracleComp base ((Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) × PrimitiveState) :=
  (simulateQ impl (sendServer senderId plaintext kid state)).run primitive

/-- Every supported send is early missing-peer rejection or the exact same-entry source send and publication. -/
theorem sendGame_cases {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext kid state primitive)) :
    (state.server.peers kid = none ∧ result = ((none, state), primitive)) ∨
      ∃ peer sent, state.server.peers kid = some peer ∧
        sent ∈ support (RawCtxSourceSend.sendGame (impl ∘ₛ RawCtxSourceSeal.nativeAdapter)
          (senderId state.server.metadata) plaintext
          ⟨selectedOwner kid (associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩ primitive) ∧
        result = ((sent.1.1, ⟨putPeer state.server kid peer sent.1.2.owner.kernel, sent.1.2.rawAttempts⟩), sent.2) := by
  cases hpeer : state.server.peers kid with
  | none =>
      simp only [sendGame, sendServer_missing senderId plaintext kid state hpeer, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      exact Or.inl ⟨rfl, hsupport⟩
  | some peer =>
      rw [sendGame, sendServer_selected senderId plaintext kid state peer hpeer] at hsupport
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff, ← QueryImpl.simulateQ_compose] at hsupport
      obtain ⟨sent, hsent, heq⟩ := hsupport
      exact Or.inr ⟨peer, sent, rfl, hsent, heq⟩

/-- Sending preserves Server identity/control metadata and the receive-attempt counter on every returned option. -/
theorem sendGame_metadata {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext kid state primitive)) :
    result.1.2.rawAttempts = state.rawAttempts ∧
      result.1.2.server.identity = state.server.identity ∧
      result.1.2.server.metadata = state.server.metadata := by
  rcases sendGame_cases impl senderId plaintext kid state primitive result hsupport with
    ⟨_, rfl⟩ | ⟨peer, sent, _, hsent, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨(RawCtxSourceSend.sendGame_publication (impl ∘ₛ RawCtxSourceSeal.nativeAdapter)
      (senderId state.server.metadata) plaintext _ primitive sent hsent).1, rfl, rfl⟩

/-- No send changes any enrolled peer identity or metadata, even when two handles store equal identities. -/
theorem sendGame_peer_fields {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext kid state primitive)) (other : Std.U64) :
    (result.1.2.server.peers other).map (fun peer => (peer.identity, peer.metadata)) =
      (state.server.peers other).map (fun peer => (peer.identity, peer.metadata)) := by
  rcases sendGame_cases impl senderId plaintext kid state primitive result hsupport with
    ⟨_, rfl⟩ | ⟨peer, sent, hpeer, _, rfl⟩
  · rfl
  · by_cases heq : other = kid
    · simp only [heq, putPeer_selected, hpeer, Option.map_some]
    · simp only [putPeer_other _ _ _ _ _ heq]

/-- Peer lookup adds no primitive calls; all four actual inner interfaces retain the one-send cap. -/
theorem sendServer_bounds {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata) :
    (sendServer senderId plaintext kid state).IsQueryBoundP (fun query => query.isLeft = true) 1 ∧
      ∀ kind, (sendServer senderId plaintext kid state).IsQueryBoundP
        (fun query => RawCtxSourceSeal.category kind query = true) 1 := by
  cases hpeer : state.server.peers kid with
  | none => simp only [sendServer_missing senderId plaintext kid state hpeer, isQueryBoundP_pure, implies_true, and_self]
  | some peer =>
      rw [sendServer_selected senderId plaintext kid state peer hpeer]
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact RawCtxSourceSeal.nativeSend_bounds (senderId state.server.metadata) plaintext _

/-- The application selects only plaintext and an assigned target; material and immutable routing remain private. -/
abbrev ApplicationSpec := (Pqxdh.Bytes × Std.U64) →ₒ Option RawCtxSourceSend.Encrypted

noncomputable def applicationImpl {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64) :
    QueryImpl ApplicationSpec (StateT (State Metadata PeerMetadata) (OracleComp RawCtxSourceSeal.NativeSpec)) :=
  fun request state => sendServer senderId request.1 request.2 state

/-- Adaptive sends across assigned targets retain one full server map and four separately charged qSend caps. -/
theorem application_bounds {Metadata PeerMetadata Result : Type} (senderId : Metadata → Std.U64)
    (client : OracleComp ApplicationSpec Result) (qSend : Nat)
    (hbound : client.IsTotalQueryBound qSend) (state : State Metadata PeerMetadata) :
    let program := (simulateQ (applicationImpl senderId) client).run state
    program.IsQueryBoundP (fun query => query.isLeft = true) qSend ∧
      ∀ kind, program.IsQueryBoundP (fun query => RawCtxSourceSeal.category kind query = true) qSend := by
  have hb : client.IsQueryBoundP (fun _ => True) qSend := hbound.isQueryBoundP
  exact ⟨hb.simulateQ_run_StateT_of_step
    (fun request server => (sendServer_bounds senderId request.1 request.2 server).1) state,
    fun kind => hb.simulateQ_run_StateT_of_step
      (fun request server => (sendServer_bounds senderId request.1 request.2 server).2 kind) state⟩

/-- Primitive state is serialized alongside the entire map, with publication preceding the API response. -/
noncomputable def serverImpl {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) :
    QueryImpl ApplicationSpec (StateT (State Metadata PeerMetadata × PrimitiveState) (OracleComp base)) :=
  fun request state => do
    let result ← sendGame impl senderId request.1 request.2 state.1 state.2
    pure (result.1.1, (result.1.2, result.2))

/-- Exact state flattening retains the selected-map transition and complete primitive interpreter. -/
theorem application_interpretation {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) :
    (impl.mapStateTBase (applicationImpl (PeerMetadata := PeerMetadata) senderId)).flattenStateT =
      serverImpl impl senderId := by
  funext request state
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, applicationImpl, serverImpl,
    sendGame, StateT.run, StateT.mk, bind_pure_comp]

/-- Adaptive target-selected sends preserve the original result, full server and actual primitive poststate. -/
theorem application_schedule_interpretation {Metadata PeerMetadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (client : OracleComp ApplicationSpec Result)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (applicationImpl senderId) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (serverImpl impl senderId) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, application_interpretation]

/-- Every active selected-peer send publishes its advanced kernel, including failed sealing, and retains all receive data. -/
theorem sendGame_active {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (peer : Peer PeerMetadata) (hpeer : state.server.peers kid = some peer)
    (hnonempty : plaintext.isEmpty = false)
    (hmax : peer.kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext kid state primitive)) :
    ∃ kernel, result.1.2.server = putPeer state.server kid peer kernel ∧
      kernel.refined.control.send_sequence.val = peer.kernel.refined.control.send_sequence.val + 1 ∧
      kernel.refined.control.receive_sequence = peer.kernel.refined.control.receive_sequence ∧
      kernel.refined.control.receive_cache = peer.kernel.refined.control.receive_cache ∧
      kernel.refined.receive_chain = peer.kernel.refined.receive_chain ∧
      kernel.refined.receive_slots = peer.kernel.refined.receive_slots := by
  rcases sendGame_cases impl senderId plaintext kid state primitive result hsupport with
    ⟨missing, _⟩ | ⟨selected, sent, hselected, hsent, rfl⟩
  · simp only [hpeer, reduceCtorEq] at missing
  · have same := Option.some.inj (hselected.symm.trans hpeer)
    subst selected
    exact ⟨_, rfl, RawCtxSourceSend.sendGame_active_state (impl ∘ₛ RawCtxSourceSeal.nativeAdapter)
      (senderId state.server.metadata) plaintext _ primitive hnonempty hmax sent hsent⟩

/-- Adaptive sends across handles preserve all server/peer identities and metadata and do not increment receive attempts. -/
theorem schedule_metadata {Metadata PeerMetadata PrimitiveState Result : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (client : OracleComp ApplicationSpec Result)
    (state : State Metadata PeerMetadata × PrimitiveState)
    (result : Result × (State Metadata PeerMetadata × PrimitiveState))
    (hsupport : result ∈ support ((simulateQ (serverImpl impl senderId) client).run state)) :
    result.2.1.rawAttempts = state.1.rawAttempts ∧
      result.2.1.server.identity = state.1.server.identity ∧
      result.2.1.server.metadata = state.1.server.metadata ∧
      ∀ other, (result.2.1.server.peers other).map (fun peer => (peer.identity, peer.metadata)) =
        (state.1.server.peers other).map (fun peer => (peer.identity, peer.metadata)) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      exact hsupport ▸ ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | query_bind request next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hsupport
      obtain ⟨step, hstep, hrest⟩ := hsupport
      have htail := ih step.1 step.2 result hrest
      change step ∈ support ((serverImpl impl senderId request).run state) at hstep
      simp only [serverImpl, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨sent, hsent, rfl⟩ := hstep
      have hmeta := sendGame_metadata impl senderId request.1 request.2 state.1 state.2 sent hsent
      exact ⟨htail.1.trans hmeta.1, htail.2.1.trans hmeta.2.1, htail.2.2.1.trans hmeta.2.2,
        fun other => (htail.2.2.2 other).trans
          (sendGame_peer_fields impl senderId request.1 request.2 state.1 state.2 sent hsent other)⟩

end BeaconcryptCore.Computational.RawCtxServerSend

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendServer_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendServer_missing

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendServer_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendServer_selected

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendGame_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendGame_cases

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendGame_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendGame_metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendGame_peer_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendGame_peer_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendServer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendServer_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.application_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.application_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.application_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.application_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.application_schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.application_schedule_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.sendGame_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.sendGame_active

/--
info: 'BeaconcryptCore.Computational.RawCtxServerSend.schedule_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerSend.schedule_metadata
