import BeaconcryptCore.Computational.RawCtxOwnerProvenance
import BeaconcryptCore.Refinement.PqxdhCore

/-!
This is a source-shaped synchronous receive wrapper for the complete Server peer map. Header routing and later full payload decoding remain separate functions, allowing the source header probe to succeed before payload rejection. The same assigned-u64 entry supplies its public identity, the exact extracted associated-data bytes and the complete selected ratchet. Every failed receive preserves the full server; actual primitive effects remain outside rollback. Successful replies retain source material, original raw/frame/context and actual optional plaintext. Raw-only adaptive schedules preserve every peer identity/metadata and count all attempts.

The u64 function map is a mathematical representation, not an extraction or implementation proof of native HashMap. It has a finite machine-key domain but supplies no useful enrolled-peer/session resource budget. The normal synchronous ownership and ready-kernel representation, native codec and compiler, native map storage, exceptions/crashes, concurrent send/registration/reveal actions, persistence and cryptographic multi-key composition remain separate boundaries. Equal public identities at different assigned handles are permitted. These operational results assert neither cryptographic origin nor secrecy, and the API's returned plaintext is distinct from public network observation. Existing source-rank/opening counts and inner component costs remain separate; no lookup or ambient primitive work is hidden in a new security assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxServerRouting

abbrev Identity := Std.Array Std.U8 32#usize

/-- Exact associated-data builder from the extracted core, in source server/beacon order. -/
noncomputable def associatedArray (server peer : Identity) : Std.Array Std.U8 281#usize :=
  (build_associated_data_abs server peer).choose

theorem associatedArray_exact (server peer : Identity) :
    pqxdh.build_associated_data server peer = ok (associatedArray server peer) :=
  (build_associated_data_abs server peer).choose_spec.1

noncomputable def associatedBytes (server peer : Identity) : Pqxdh.Bytes :=
  absBytes (associatedArray server peer)

theorem associatedBytes_exact (server peer : Identity) :
    associatedBytes server peer = Pqxdh.assocData (absBytes server) (absBytes peer) :=
  (build_associated_data_abs server peer).choose_spec.2

theorem associatedBytes_length (server peer : Identity) :
    (associatedBytes server peer).length = 281 := by
  simp only [associatedBytes, absBytes_length, usize_val_281]

/-- Distinct assigned handles may store equal public identities; no injectivity is required. -/
structure Peer (PeerMetadata : Type) where
  identity : Identity
  kernel : ConcreteRatchetKernel
  metadata : PeerMetadata

/-- The complete peer map and all remaining server fields remain part of the owned state. -/
structure Server (Metadata PeerMetadata : Type) where
  identity : Identity
  peers : Std.U64 → Option (Peer PeerMetadata)
  metadata : Metadata

structure State (Metadata PeerMetadata : Type) where
  server : Server Metadata PeerMetadata
  rawAttempts : Nat

/-- Header routing can succeed even when the later complete payload decoder rejects. -/
abbrev SenderDecoder := Pqxdh.Bytes → Option Std.U64

/-- Successful full decoding agrees with header routing on the sender; failure domains may differ. -/
def DecoderAgreement (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) : Prop :=
  ∀ raw frame, decode raw = some frame → route raw = some frame.sender

/-- Source AD lookup reads the identity from the same assigned-handle map used for mutable selection. -/
noncomputable def peerAssociatedData {Metadata PeerMetadata : Type}
    (server : Server Metadata PeerMetadata) (kid : Std.U64) : Option Pqxdh.Bytes := do
  let peer ← server.peers kid
  pure (associatedBytes server.identity peer.identity)

/-- The private selected owner binds one complete ratchet to its route, AD and retained peer fields. -/
def selectedOwner {PeerMetadata : Type} (kid : Std.U64) (ad : Pqxdh.Bytes)
    (peer : Peer PeerMetadata) : RawCtxWholeOwner.Owner PeerMetadata :=
  ⟨peer.kernel, kid, ad, peer.metadata⟩

/-- Publication updates only the selected whole ratchet and preserves the peer's identity and metadata. -/
def putPeer {Metadata PeerMetadata : Type} (server : Server Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer PeerMetadata) (kernel : ConcreteRatchetKernel) :
    Server Metadata PeerMetadata :=
  { server with peers := Function.update server.peers kid (some { peer with kernel := kernel }) }

/-- Source-ordered routing/AD/mutable lookup precede the raw helper's own decode and sender check. -/
noncomputable def rawGame {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) :
    OracleComp base ((core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState) :=
  match route raw with
  | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
  | some kid =>
      match peerAssociatedData state.server kid with
      | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
      | some ad =>
          match state.server.peers kid with
          | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
          | some peer => do
              let result ← RawCtxWholeOwner.rawGame impl decode raw
                ⟨selectedOwner kid ad peer, state.rawAttempts⟩ primitive
              pure ((result.1.1,
                ⟨putPeer state.server kid peer result.1.2.owner.kernel, result.1.2.rawAttempts⟩), result.2)

/-- Both native lookups see the same immutable entry during this synchronous operation. -/
theorem peerAssociatedData_some {Metadata PeerMetadata : Type}
    (server : Server Metadata PeerMetadata) (kid : Std.U64) (ad : Pqxdh.Bytes)
    (had : peerAssociatedData server kid = some ad) :
    ∃ peer, server.peers kid = some peer ∧ ad = associatedBytes server.identity peer.identity := by
  simp only [peerAssociatedData] at had
  cases hpeer : server.peers kid <;> simp only [hpeer, Bind.bind, Option.bind, pure, reduceCtorEq, Option.some.injEq] at had
  exact ⟨_, rfl, had.symm⟩

/-- Selected publication retains exactly the peer identity and all other peer metadata. -/
theorem putPeer_selected {Metadata PeerMetadata : Type} (server : Server Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer PeerMetadata) (kernel : ConcreteRatchetKernel) :
    (putPeer server kid peer kernel).peers kid = some { peer with kernel := kernel } := by
  simp only [putPeer, Function.update_self]

/-- Other assigned handles retain their complete entries, even if their public identities coincide. -/
theorem putPeer_other {Metadata PeerMetadata : Type} (server : Server Metadata PeerMetadata)
    (kid other : Std.U64) (peer : Peer PeerMetadata) (kernel : ConcreteRatchetKernel)
    (hne : other ≠ kid) :
    (putPeer server kid peer kernel).peers other = server.peers other := by
  simp only [putPeer, Function.update_of_ne hne]

/-- Reinstalling the entry kernel restores the entire functional server state. -/
theorem putPeer_entry {Metadata PeerMetadata : Type} (server : Server Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer PeerMetadata) (hpeer : server.peers kid = some peer) :
    putPeer server kid peer peer.kernel = server := by
  simp only [putPeer, ← hpeer, Function.update_eq_self]

/-- A supported server call either rejects before owner selection or runs exactly the selected whole owner. -/
theorem rawGame_cases {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl route decode raw state primitive)) :
    result = ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive) ∨
      ∃ kid peer opened, route raw = some kid ∧ state.server.peers kid = some peer ∧
        opened ∈ support (RawCtxWholeOwner.rawGame impl decode raw
          ⟨selectedOwner kid (associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩ primitive) ∧
        result = ((opened.1.1,
          ⟨putPeer state.server kid peer opened.1.2.owner.kernel, opened.1.2.rawAttempts⟩), opened.2) := by
  cases hroute : route raw <;> simp only [rawGame, hroute] at hsupport
  · exact Or.inl (by simpa only [support_pure, Set.mem_singleton_iff] using hsupport)
  · rename_i kid
    cases hpeer : state.server.peers kid <;>
      simp [peerAssociatedData, hpeer] at hsupport
    · exact Or.inl hsupport
    · obtain ⟨reply, owner, nextPrimitive, hopen, hresult⟩ := hsupport
      exact Or.inr ⟨kid, _, ((reply, owner), nextPrimitive), rfl, hpeer, hopen, hresult.symm⟩

/-- Failed header routing makes no primitive request and retains the full server and primitive state. -/
theorem rawGame_missing_sender {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) (hroute : route raw = none) :
    rawGame impl route decode raw state primitive =
      pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive) := by
  simp only [rawGame, hroute]

/-- An unknown assigned handle makes no primitive request after header routing. -/
theorem rawGame_missing_peer {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) (kid : Std.U64)
    (hroute : route raw = some kid) (hpeer : state.server.peers kid = none) :
    rawGame impl route decode raw state primitive =
      pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive) := by
  simp [rawGame, hroute, peerAssociatedData, hpeer]

/-- Every raw server call counts exactly once and preserves all non-peer server fields. -/
theorem rawGame_preserves_metadata {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl route decode raw state primitive)) :
    result.1.2.rawAttempts = state.rawAttempts + 1 ∧
      result.1.2.server.identity = state.server.identity ∧
      result.1.2.server.metadata = state.server.metadata := by
  rcases rawGame_cases impl route decode raw state primitive result hsupport with
    rfl | ⟨kid, peer, opened, hroute, hpeer, hopen, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨(RawCtxWholeOwner.rawGame_preserves_metadata impl decode raw _ primitive opened hopen).1, rfl, rfl⟩

/-- A failed server receive restores the entire peer map while retaining the actual primitive effects. -/
theorem rawGame_failure_server {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl route decode raw state primitive))
    (hfailure : result.1.1 = .None) : result.1.2.server = state.server := by
  rcases rawGame_cases impl route decode raw state primitive result hsupport with
    rfl | ⟨kid, peer, opened, hroute, hpeer, hopen, rfl⟩
  · rfl
  · have howner := RawCtxWholeOwner.rawGame_failure_owner impl decode raw _ primitive opened hopen hfailure
    simpa only [howner, selectedOwner] using putPeer_entry state.server kid peer hpeer

/-- Server success uses the selected assigned handle, same peer AD, decoded sequence and true primitive plaintext. -/
theorem rawGame_success {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl route decode raw state primitive))
    (message : RawCtxWholeOwner.Decrypted) (hsuccess : result.1.1 = .Some message) :
    ∃ (kid : Std.U64) (peer : Peer PeerMetadata) (frame : RawCtxReceive.DecodedFrame)
      (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) (input : RawCtxWholeOwner.OpenInput)
      (before : PrimitiveState) (kernel : ConcreteRatchetKernel),
      route raw = some kid ∧ state.server.peers kid = some peer ∧ decode raw = some frame ∧
      message.keyId = kid ∧ message.sequence = frame.sequence ∧
      RawCtxWholeOwner.arguments pending = some input ∧ pending.material = ok (.Some input.material) ∧
      input.sequence = frame.sequence ∧
      input.context = ⟨raw, frame, associatedBytes state.server.identity peer.identity⟩ ∧
      (.Some message.plaintext, result.2) ∈ support ((impl (.inr input)).run before) ∧
      result.1.2.server = putPeer state.server kid peer kernel := by
  rcases rawGame_cases impl route decode raw state primitive result hsupport with
    rfl | ⟨kid, peer, opened, hroute, hpeer, hopen, rfl⟩
  · cases hsuccess
  · obtain ⟨frame, pending, input, plaintext, before, hdecode, hvalid, hargs,
      hmaterial, hsequence, hcontext, hmessage, hreply⟩ :=
      RawCtxOwnerProvenance.raw_success impl decode raw _ primitive opened hopen message hsuccess
    refine ⟨kid, peer, frame, pending, input, before, opened.1.2.owner.kernel,
      hroute, hpeer, hdecode, ?_, ?_, hargs, hmaterial, hsequence, hcontext, ?_, rfl⟩
    · simpa only [hmessage, RawCtxWholeOwner.decrypted, hcontext, selectedOwner] using hvalid.1
    · simpa only [hmessage, RawCtxWholeOwner.decrypted] using hsequence
    · simpa only [hmessage, RawCtxWholeOwner.decrypted] using hreply

/-- Every handle retains its peer identity and metadata; no successful receive can rebind an assigned ID. -/
theorem rawGame_peer_fields {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl route decode raw state primitive)) (other : Std.U64) :
    (result.1.2.server.peers other).map (fun peer => (peer.identity, peer.metadata)) =
      (state.server.peers other).map (fun peer => (peer.identity, peer.metadata)) := by
  rcases rawGame_cases impl route decode raw state primitive result hsupport with
    rfl | ⟨kid, peer, opened, hroute, hpeer, hopen, rfl⟩
  · rfl
  · by_cases heq : other = kid
    · simp only [heq, putPeer_selected, hpeer, Option.map_some]
    · simp only [putPeer_other _ _ _ _ _ heq]

/-- Every adaptive request serializes the complete server map and the separate primitive state. -/
noncomputable def serverImpl {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxWholeOwner.RawSpec
      (StateT (State Metadata PeerMetadata × PrimitiveState) (OracleComp base)) :=
  fun raw state => do
    let result ← rawGame impl route decode raw state.1 state.2
    pure (result.1.1, (result.1.2, result.2))

/-- One actual raw request counts once while preserving the complete server identity and metadata. -/
theorem serverImpl_step {Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata × PrimitiveState)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × (State Metadata PeerMetadata × PrimitiveState))
    (hsupport : result ∈ support ((serverImpl impl route decode raw).run state)) :
    result.2.1.rawAttempts = state.1.rawAttempts + 1 ∧
      result.2.1.server.identity = state.1.server.identity ∧
      result.2.1.server.metadata = state.1.server.metadata := by
  simp only [serverImpl, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
  obtain ⟨received, hreceived, rfl⟩ := hsupport
  exact rawGame_preserves_metadata impl route decode raw state.1 state.2 received hreceived

/-- A raw-only adaptive client may deliver across assigned handles and stop using actual optional replies. -/
noncomputable def scheduleGame {Metadata PeerMetadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : State Metadata PeerMetadata × PrimitiveState) :
    OracleComp base (Result × (State Metadata PeerMetadata × PrimitiveState)) :=
  (simulateQ (serverImpl impl route decode) client).run state

/-- Every adaptive raw attempt across the whole peer map is charged to the caller's explicit budget. -/
theorem scheduleGame_bounds {Metadata PeerMetadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (qRaw : Nat) (hbound : client.IsTotalQueryBound qRaw)
    (state : State Metadata PeerMetadata × PrimitiveState)
    (result : Result × (State Metadata PeerMetadata × PrimitiveState))
    (hsupport : result ∈ support (scheduleGame impl route decode client state)) :
    result.2.1.rawAttempts ≤ state.1.rawAttempts + qRaw ∧
      result.2.1.server.identity = state.1.server.identity ∧
      result.2.1.server.metadata = state.1.server.metadata := by
  unfold scheduleGame at hsupport
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      subst result
      exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  | query_bind raw rest ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hsupport
      obtain ⟨step, hstep, hrest⟩ := hsupport
      have hnext := serverImpl_step impl route decode raw state step hstep
      have htail := ih step.1 (qRaw - 1) (hbound.2 step.1) step.2 result hrest
      exact ⟨by omega, htail.2.1.trans hnext.2.1, htail.2.2.trans hnext.2.2⟩

/-- Raw-only adaptive scheduling never rebinds or removes an established peer identity. -/
theorem scheduleGame_peer_fields {Metadata PeerMetadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : State Metadata PeerMetadata × PrimitiveState)
    (result : Result × (State Metadata PeerMetadata × PrimitiveState))
    (hsupport : result ∈ support (scheduleGame impl route decode client state)) (other : Std.U64) :
    (result.2.1.server.peers other).map (fun peer => (peer.identity, peer.metadata)) =
      (state.1.server.peers other).map (fun peer => (peer.identity, peer.metadata)) := by
  unfold scheduleGame at hsupport
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      exact hsupport ▸ rfl
  | query_bind raw rest ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hsupport
      obtain ⟨step, hstep, hrest⟩ := hsupport
      have htail := ih step.1 step.2 result hrest
      change step ∈ support ((serverImpl impl route decode raw).run state) at hstep
      simp only [serverImpl, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨received, hreceived, rfl⟩ := hstep
      exact htail.trans (rawGame_peer_fields impl route decode raw state.1 state.2 received hreceived other)

end BeaconcryptCore.Computational.RawCtxServerRouting

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.associatedArray_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.associatedArray_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.associatedBytes_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.associatedBytes_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.associatedBytes_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.associatedBytes_length

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.peerAssociatedData_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.peerAssociatedData_some

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_selected

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_other

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.putPeer_entry

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_cases

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_missing_sender' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_missing_sender

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_missing_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_missing_peer

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_preserves_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_preserves_metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_failure_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_failure_server

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_success

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_peer_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.rawGame_peer_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.serverImpl_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.serverImpl_step

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.scheduleGame_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.scheduleGame_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxServerRouting.scheduleGame_peer_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerRouting.scheduleGame_peer_fields
