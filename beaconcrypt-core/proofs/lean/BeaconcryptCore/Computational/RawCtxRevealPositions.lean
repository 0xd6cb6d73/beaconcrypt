import BeaconcryptCore.Computational.RawCtxProtocolPositions
import BeaconcryptCore.Computational.RawCtxProtocolReveals
import BeaconcryptCore.Refinement.RatchetAccessors

/-!
Eight statements connect actual record-compromise replies to their existing source material positions. The same selected Server peer or established Beacon keeps its supplied directional origins; current-chain reads identify actual native counters, and successful skipped reads identify the true positive sequence and exact byte-model material. Full original record/public/reveal steps and adaptive schedules preserve those relations together with every optional reply, private history and complete shared primitive state.

An actually disclosed current chain deterministically derives material at every later mathematical position on that same direction. This is an exposure equation for the real fixed functional source, not a hardness premise or post-compromise recovery claim. Nat positions beyond native u64 exhaustion denote mathematical KDF iteration, not extra native operations. Distinct handles or directions may share origin/key bytes; no unique or independent key table is inferred.

Origins and theorem state remain private proof context. The existing adversary receives only each requested compromise reply, never the erased KDF log or the full role/primitive state. The original program and query ledgers are unchanged. All supplied starting owner relations, actual generation/registration, cross-owner alias exposure, source restore/copy validity, target freshness, evolving-key hybrid interpretation, native representation/runtime and network declassification retain their explicit obligations. No global cryptographic or symbolic correspondence is asserted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRevealPositions
open RawCtxPositionedOwner RawCtxProtocolPositions RawCtxProtocolReveals

def ownerOrigins {serverCount beaconCount : Nat}
    (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins) : Owner serverCount beaconCount → Origins
  | .server index peer => serverOrigins index peer
  | .beacon index => beaconOrigins index

/-- The actual selected kernel keeps its own original directional positions. -/
theorem selected_positions {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) :
    Positioned c (ownerOrigins serverOrigins beaconOrigins owner).1
      (ownerOrigins serverOrigins beaconOrigins owner).2 kernel := by
  cases owner with
  | server index kid =>
    simp only [selectedKernel, Option.map_eq_some_iff] at selected
    obtain ⟨peer, present, rfl⟩ := selected
    exact invariant.1 index kid peer present
  | beacon index =>
    cases phase : (roles.2 index).beacon.phase
    all_goals simp only [selectedKernel, phase, reduceCtorEq, Option.some.injEq] at selected
    simpa only [BeaconPositioned, phase, selected, ownerOrigins] using invariant.2 index

/-- Each disclosed current chain is at the actual selected owner's native counter. -/
theorem chain_reveal_positions {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) :
    reveal (.sendChain owner) roles = .Some (Ratchet.chainAt (crypto c)
      (ownerOrigins serverOrigins beaconOrigins owner).1 kernel.refined.control.send_sequence.val) ∧
    reveal (.receiveChain owner) roles = .Some (Ratchet.chainAt (crypto c)
      (ownerOrigins serverOrigins beaconOrigins owner).2 kernel.refined.control.receive_sequence.val) := by
  have positions := positioned_chains c (ownerOrigins serverOrigins beaconOrigins owner).1
    (ownerOrigins serverOrigins beaconOrigins owner).2 kernel
    (selected_positions c serverOrigins beaconOrigins roles invariant owner kernel selected)
  simp only [reveal, selected, positions.1, positions.2, and_self]

/-- Actual disclosed skipped material belongs to its positive source wire sequence. -/
theorem skipped_reveal_positions {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) (sequence : Std.U64) (material : RatchetMaterial)
    (disclosed : reveal (.skippedKey owner sequence) roles = .Some material) :
    0 < sequence.val ∧ material = Ratchet.msgKeyAt (crypto c)
      (ownerOrigins serverOrigins beaconOrigins owner).2 (sequence.val - 1) := by
  obtain ⟨send, receive, refined, _⟩ := selected_positions c serverOrigins beaconOrigins roles invariant owner kernel selected
  apply BeaconcryptCore.Refinement.RatchetAccessors.refined_receive_key_is_derived
    (crypto c) (ownerOrigins serverOrigins beaconOrigins owner).2 send receive kernel refined sequence material
  simpa only [disclosed, RevealSpec, OracleSpec.Range, OracleSpec.ofFn] using
    skipped_reveal_exact owner roles kernel sequence selected

/-- Every actual record/public/reveal step preserves all original owner positions and shared effects. -/
theorem reveal_step_positions {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins state.1.1)
    (result : (SourceSpec serverCount beaconCount).Range query ×
      (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
        RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId
      route decode query).run state)) :
    RolesPositioned source.crypto serverOrigins beaconOrigins result.2.1.1 := by
  cases query with
  | inl request =>
    simp only [RawCtxProtocolReveals.sourceImpl, StateT.run] at present
    obtain ⟨child, supported, returned⟩ := mem_support_bind_peel _ _ present
    simpa only [eq_of_mem_support_pure _ returned] using protocol_step_positions source writer
      serverCount beaconCount serverOrigins beaconOrigins senderId route decode request
      (state.1.1, state.2) invariant child supported
  | inr request =>
    simp only [RawCtxProtocolReveals.sourceImpl, StateT.run, mem_support_pure_iff] at present
    subst result
    exact invariant

/-- Arbitrary adaptive compromise continuations retain the same owner positions jointly. -/
theorem reveal_schedule_positions {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (invariant : RolesPositioned source.crypto serverOrigins beaconOrigins state.1.1)
    (result : Result × (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode) client).run state)) :
    RolesPositioned source.crypto serverOrigins beaconOrigins result.2.1.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value => simpa using present ▸ invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨reply, supported, continued⟩ := present
    exact ih reply.1 reply.2
      (reveal_step_positions source writer serverCount beaconCount serverOrigins beaconOrigins senderId
        route decode query state invariant reply supported) result continued

inductive Direction where
  | send
  | receive

noncomputable def chainReveal {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (owner : Owner serverCount beaconCount) (direction : Direction)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) : core.option.Option RatchetChain :=
  match direction with
  | .send => reveal (.sendChain owner) roles
  | .receive => reveal (.receiveChain owner) roles

def chainOrigin (origins : Origins) : Direction → RatchetChain
  | .send => origins.1
  | .receive => origins.2

def chainIndex (kernel : ConcreteRatchetKernel) : Direction → Nat
  | .send => kernel.refined.control.send_sequence.val
  | .receive => kernel.refined.control.receive_sequence.val

/-- An actual successful chain disclosure gives exactly the selected source chain at its current index. -/
theorem chain_disclosure_index {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) (direction : Direction) (chain : RatchetChain)
    (disclosed : chainReveal owner direction roles = .Some chain) :
    chain = Ratchet.chainAt (crypto c) (chainOrigin (ownerOrigins serverOrigins beaconOrigins owner) direction)
      (chainIndex kernel direction) := by
  have actual := chain_reveal_positions c serverOrigins beaconOrigins roles invariant owner kernel selected
  cases direction with
  | send => simpa [chainReveal, actual.1, chainOrigin, chainIndex] using disclosed.symm
  | receive => simpa [chainReveal, actual.2, chainOrigin, chainIndex] using disclosed.symm

/-- Advancing an actually disclosed current chain reproduces every later source material position. -/
theorem disclosed_descendant_material {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) (direction : Direction) (chain : RatchetChain)
    (disclosed : chainReveal owner direction roles = .Some chain)
    (position : Nat) (later : chainIndex kernel direction ≤ position) :
    Ratchet.msgKeyAt (crypto c) chain (position - chainIndex kernel direction) =
      Ratchet.msgKeyAt (crypto c) (chainOrigin (ownerOrigins serverOrigins beaconOrigins owner) direction) position := by
  rw [chain_disclosure_index c serverOrigins beaconOrigins roles invariant owner kernel selected direction chain disclosed,
    Ratchet.msgKeyAt_chainAt, Nat.add_sub_of_le later]

open BeaconcryptCore.Refinement.RepresentationBridge

/-- A successful skipped disclosure retains the exact byte-model key and nonce at the same receive position. -/
theorem skipped_reveal_bytes {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (c : Pqxdh.Crypto) (serverOrigins : Fin serverCount → Std.U64 → Origins)
    (beaconOrigins : Fin beaconCount → Origins)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (invariant : RolesPositioned c serverOrigins beaconOrigins roles)
    (owner : Owner serverCount beaconCount) (kernel : ConcreteRatchetKernel)
    (selected : selectedKernel owner roles = some kernel) (sequence : Std.U64) (material : RatchetMaterial)
    (disclosed : reveal (.skippedKey owner sequence) roles = .Some material) :
    0 < sequence.val ∧ absMaterial material = Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c)
      (absChain (ownerOrigins serverOrigins beaconOrigins owner).2) (sequence.val - 1) := by
  obtain ⟨positive, actual⟩ := skipped_reveal_positions c serverOrigins beaconOrigins roles invariant owner kernel
    selected sequence material disclosed
  exact ⟨positive, by simpa only [actual, crypto] using
    (RawCtxMaterialPositions.source_position_bytes c (ownerOrigins serverOrigins beaconOrigins owner).2
      (sequence.val - 1)).2⟩

end BeaconcryptCore.Computational.RawCtxRevealPositions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.selected_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.selected_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.chain_reveal_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.chain_reveal_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.skipped_reveal_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.skipped_reveal_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.reveal_step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.reveal_step_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.reveal_schedule_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.reveal_schedule_positions

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.chain_disclosure_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.chain_disclosure_index

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.disclosed_descendant_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.disclosed_descendant_material

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealPositions.skipped_reveal_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealPositions.skipped_reveal_bytes
