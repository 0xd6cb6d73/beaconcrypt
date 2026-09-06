import BeaconcryptCore.Computational.RawCtxMaterialPositions

/-!
Twelve statements connect actual source receive/send execution to directional material positions. A Positioned kernel retains the ordinary source receive/cache relation and an independently labelled send origin. Actual rejected receives preserve their entry kernel and complete primitive poststate; failed sends retain the source's allocated advancement. The original raw/mixed interfaces, optional replies and adaptive stopping are unchanged.

The checked Beacon or Server initializer supplies its actual returned directional chains as the initial origins. Current native chains and occupied skipped slots project to the corresponding source counter positions and exact byte-model key/nonce material. These are facts about one fixed functional HKDF source; no distinct-origin, distinct-key, entropy, ideal-decryption or fresh-output-hybrid premise is used. The earlier chronological KDF log is used only through its proved complete erasure and remains excluded from public/reveal/snapshot/persistence interfaces.

The theorem state retains the complete owner and shared primitive cache/auxiliary state; it is not adversary observation. Origins are private proof labels and may coincide across owners. Source initialization does not prove the global root-generation distribution or native library/representation contracts. Reveals, restore/alias ownership, evolving-key hybrid interpretation and global security need their explicit compositions. The original computation and its query ledgers remain unchanged; deterministic primitive and local work remain real computation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
open BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxPositionedOwner
open RawCtxMaterialPositions

noncomputable def crypto (c : Pqxdh.Crypto) := concreteCrypto c (RawCtxSourceHkdf.response c)

def Positioned (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) : Prop :=
  ∃ send receive, KernelRefines (crypto c) receiveOrigin send receive kernel ∧
    send.ck = Ratchet.chainAt (crypto c) sendOrigin send.n

/-- Every supported actual receive preserves both directional origins and the complete primitive poststate. -/
theorem receive_positions {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin entry)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxSourceOpen.ownerAdapter (RawCtxOwnerOracle.receive entry target context))).run primitive)) :
    Positioned source.crypto sendOrigin receiveOrigin result.1.1 := by
  rw [← source_receive_complete source (RawCtxOwnerOracle.receive entry target context) primitive [],
    support_map, Set.mem_image] at present
  obtain ⟨logged, hlogged, rfl⟩ := present
  obtain ⟨send, receive, hkernel, aligned⟩ := invariant
  obtain ⟨nextReceive, preserved⟩ := receive_preserves_positions (crypto source.crypto)
    (RawCtxSourceHkdf.response source.crypto) receiveOrigin send receive entry context target hkernel
    (sourceOpening source) (primitive, []) logged hlogged
  exact ⟨send, nextReceive, preserved, aligned⟩

/-- Every supported actual send preserves source positions, including allocated advancement after sealing failure. -/
theorem send_positions {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain)
    (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin entry)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxMixedOwner.sendAdapter
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send entry context)))).run primitive)) :
    Positioned source.crypto sendOrigin receiveOrigin result.1.1 := by
  rw [← source_send_complete source writer (RawCtxSourceSend.send entry context) primitive [],
    support_map, Set.mem_image] at present
  obtain ⟨logged, hlogged, rfl⟩ := present
  obtain ⟨send, receive, hkernel, aligned⟩ := invariant
  obtain ⟨nextSend, preserved, nextAligned⟩ := send_preserves_positions (crypto source.crypto)
    (RawCtxSourceHkdf.response source.crypto) receiveOrigin sendOrigin send receive entry context hkernel aligned
    (sourceSealing source writer) (primitive, []) logged hlogged
  exact ⟨nextSend, receive, preserved, nextAligned⟩


noncomputable def receiveNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :=
  RawCtxSharedPrimitive.nativeImpl (Auxiliary := Auxiliary) source.crypto (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxSourceOpen.nativeAdapter

/-- The original raw receive prelude and publication preserve the same positioned kernel. -/
theorem raw_positions {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin state.owner.kernel)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive)) :
    Positioned source.crypto sendOrigin receiveOrigin result.1.2.owner.kernel := by
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at present
  split at present
  · simp only [simulateQ_pure] at present
    subst result
    exact invariant
  · split at present
    · simp only [simulateQ_pure] at present
      subst result
      exact invariant
    · dsimp only at present
      split at present
      · rw [simulateQ_bind] at present
        change result ∈ support (StateT.run _ primitive) at present
        simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at present
        obtain ⟨opened, hopen, rfl⟩ := present
        apply receive_positions source sendOrigin receiveOrigin state.owner.kernel _ _ invariant primitive opened
        simpa only [receiveNative, RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose] using hopen
      · simp only [simulateQ_pure] at present
        subst result
        exact invariant


noncomputable def sendNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :=
  RawCtxMixedShared.sharedImpl (Auxiliary := Auxiliary) source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.sendAdapter

/-- The original optional send API preserves source positions through rejection and publication. -/
theorem sendOwner_positions {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin state.owner.kernel)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxSourceSend.sendGame (sendNative source writer)
      sender plaintext state primitive)) :
    Positioned source.crypto sendOrigin receiveOrigin result.1.2.owner.kernel := by
  unfold RawCtxSourceSend.sendGame RawCtxSourceSend.sendOwner StateT.run at present
  split at present
  all_goals change result ∈ support ((simulateQ (sendNative source writer) _).run primitive) at present
  all_goals simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at present
  · subst result
    exact invariant
  · obtain ⟨sealed, hseal, rfl⟩ := present
    apply send_positions source writer sendOrigin receiveOrigin state.owner.kernel _ invariant primitive sealed
    simpa only [sendNative, QueryImpl.simulateQ_compose] using hseal


/-- The receive branch uses the identical common source KDF and commitment-cache handler. -/
theorem shared_receiveNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    (RawCtxMixedShared.sharedImpl (Auxiliary := Auxiliary) source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
      RawCtxMixedOwner.receiveAdapter) = receiveNative source := by
  funext query
  change simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
    (simulateQ RawCtxMixedOwner.receiveLift (RawCtxSourceOpen.nativeAdapter query)) =
      simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
        (RawCtxSourceOpen.nativeAdapter query)
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

/-- Either original mixed-owner request preserves its fixed directional origins. -/
theorem step_positions {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin state.1.owner.kernel)
    (result : RawCtxMixedOwner.SourceSpec.Range query ×
      (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      sender decode query).run state)) :
    Positioned source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel := by
  cases query with
  | inl plaintext =>
    change result ∈ support ((do
      let sent ← RawCtxSourceSend.sendGame (sendNative source writer) sender plaintext state.1 state.2
      pure (sent.1.1, (sent.1.2, sent.2))) : ProbComp _) at present
    obtain ⟨sent, hsent, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    exact sendOwner_positions source writer sendOrigin receiveOrigin sender plaintext state.1 invariant state.2 sent hsent
  | inr raw =>
    simp only [RawCtxMixedOwner.sourceImpl, shared_receiveNative] at present
    change result ∈ support ((do
      let received ← RawCtxWholeOwner.rawGame (receiveNative source) decode raw state.1 state.2
      pure (received.1.1, (received.1.2, received.2))) : ProbComp _) at present
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ present
    have equal := eq_of_mem_support_pure _ returned
    subst result
    exact raw_positions source sendOrigin receiveOrigin decode raw state.1 invariant state.2 received hreceived

/-- Every supported adaptive mixed-owner run preserves its original directional origins. -/
theorem schedule_positions {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : Positioned source.crypto sendOrigin receiveOrigin state.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      sender decode) client).run state)) :
    Positioned source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value => simpa using present ▸ invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨reply, hreply, htail⟩ := present
    exact ih reply.1 reply.2
      (step_positions source writer sendOrigin receiveOrigin sender decode query state invariant reply hreply)
      result htail

/-- Both live chains remain at their actual native counter positions. -/
theorem positioned_chains (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) (invariant : Positioned c sendOrigin receiveOrigin kernel) :
    kernel.refined.send_chain = Ratchet.chainAt (crypto c) sendOrigin kernel.refined.control.send_sequence.val ∧
      kernel.refined.receive_chain = Ratchet.chainAt (crypto c) receiveOrigin kernel.refined.control.receive_sequence.val := by
  obtain ⟨send, receive, refined, aligned⟩ := invariant
  simpa only [refined.sendChain, refined.sendSequence, refined.receiveChain, refined.receiveControl.seq] using
    And.intro aligned refined.receiveControl.chain

/-- Every occupied source cache slot contains material from its original receive position. -/
theorem positioned_slot (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) (invariant : Positioned c sendOrigin receiveOrigin kernel)
    (index : Nat) (live : index < kernel.refined.control.receive_cache.len.val) :
    ∃ cached : ratchet.refined.CachedReceiveKey RatchetMaterial,
      kernel.refined.receive_slots.val[index]! = core.option.Option.Some cached ∧
      0 < cached.sequence.val ∧ cached.sequence.val ≤ kernel.refined.control.receive_sequence.val ∧
      cached.material = Ratchet.msgKeyAt (crypto c) receiveOrigin (cached.sequence.val - 1) := by
  obtain ⟨send, receive, refined, _⟩ := invariant
  obtain ⟨pair, cached, member, stored, _, sequence, material⟩ := refined.slotSound index live
  refine ⟨cached, stored, ?_, ?_, ?_⟩
  case refine_3 =>
    simpa only [sequence, material, Nat.add_sub_cancel] using refined.receiveControl.keys pair member
  case refine_2 =>
    simpa only [sequence, refined.receiveControl.seq] using Nat.succ_le_of_lt (refined.receiveControl.keys_lt pair member)
  case refine_1 => simp only [sequence, Nat.add_pos_right, zero_lt_one]

open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- Either actual role initializer establishes the invariant at its returned directional origins. -/
theorem initialized_positions (c : Pqxdh.Crypto) (root : Std.Array Std.U8 32#usize)
    (kernel : ConcreteRatchetKernel)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse c) = ok kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse c) = ok kernel) :
    Positioned c kernel.refined.send_chain kernel.refined.receive_chain kernel := by
  rcases initialized with beacon | server
  · obtain ⟨actual, returned, _, _, refined⟩ := beacon_initial_positions c root
    have equal : actual = kernel := by simpa [beacon] using returned.symm
    subst actual
    exact ⟨_, _, refined, rfl⟩
  · obtain ⟨actual, returned, _, _, refined⟩ := server_initial_positions c root
    have equal : actual = kernel := by simpa [server] using returned.symm
    subst actual
    exact ⟨_, _, refined, rfl⟩

/-- The original mixed source execution retains positions from either actual role initializer through every adaptive continuation. -/
theorem initialized_schedule {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      sender decode) client).run state)) :
    Positioned source.crypto state.1.owner.kernel.refined.send_chain
      state.1.owner.kernel.refined.receive_chain result.2.1.owner.kernel := by
  exact schedule_positions source writer _ _ sender decode client state
    (initialized_positions source.crypto root state.1.owner.kernel initialized) result present

/-- Live source slots identify the exact byte-model key and nonce at the same receive position. -/
theorem positioned_slot_bytes (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) (invariant : Positioned c sendOrigin receiveOrigin kernel)
    (index : Nat) (live : index < kernel.refined.control.receive_cache.len.val) :
    ∃ cached : ratchet.refined.CachedReceiveKey RatchetMaterial,
      kernel.refined.receive_slots.val[index]! = core.option.Option.Some cached ∧
      0 < cached.sequence.val ∧ cached.sequence.val ≤ kernel.refined.control.receive_sequence.val ∧
      absMaterial cached.material = Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c)
        (absChain receiveOrigin) (cached.sequence.val - 1) := by
  obtain ⟨cached, stored, positive, bounded, material⟩ := positioned_slot c sendOrigin receiveOrigin kernel invariant index live
  exact ⟨cached, stored, positive, bounded, by
    simpa only [material, crypto] using (source_position_bytes c receiveOrigin (cached.sequence.val - 1)).2⟩

end BeaconcryptCore.Computational.RawCtxPositionedOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.receive_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.receive_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.send_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.send_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.raw_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.raw_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.sendOwner_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.sendOwner_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.shared_receiveNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.shared_receiveNative

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.step_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.schedule_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.schedule_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_slot

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.initialized_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.initialized_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.initialized_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.initialized_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_slot_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPositionedOwner.positioned_slot_bytes
