-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels

/-! Record replay in the common deployment experiment (CE-6, CE-C3). The transcript shows a Server peer accepting a sequence number at every successful Server raw receive whose decrypted record names the peer's key ID, and a Beacon owner accepting one at every successful raw receive of that owner and, for sequence one, at its successful finish (`peerSequences`, `ownerSequences`). The run invariant `Tracked` says that every peer and every owner with a kernel carries the source receive relation with exactly the receive positions of these accepted sequence numbers consumed, and that a handle without a kernel accepted nothing. A raw receive consumes the decoded position on the routed peer or on the addressed owner only (`serverRaw_tracked`, `beaconRaw_tracked`, from `RawCtxReceiveConsumption.raw_spent`); sends, including those of the secrecy commands, advance send chains only (`serverSend_tracked`, `beaconSend_tracked`, `coinSend_tracked`); a build or a finish installs a kernel only where none was (`PqxdhDeploymentRecordKernels`). The constructed Server has no peer and the experiment starts with no owner (`tracked_game`). Since consumed positions never repeat, `record_replay_game` (CE-C3): on every outcome of the experiment, in either mode, for every adversary and with no budget, no peer and no owner accepted a sequence number twice. This is zero loss: a deterministic consequence of slot consumption on one live object, with no probability, codec law or security assumption. Replay across objects, through copies, restoration or persistence, is outside this experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity RawCtxMaterialPositions
open PqxdhDeploymentInterface (Spec Command FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentRecordKernels (Live Finished peerKernel ownerKernel PeerStep OwnersSame)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The sequence number a transcript entry shows Server peer `kid` accepting: a successful Server raw receive whose decrypted record names `kid`. -/
def peerAccepted (kid : Std.U64) : Entry → Option Std.U64
  | ⟨.inl (.inr (.serverRaw _)), .Some message⟩ => if message.keyId = kid then some message.sequence else none
  | _ => none

/-- The sequence number a transcript entry shows Beacon owner `index` accepting: a successful raw receive of that owner, or a successful finish of that owner, which accepted the registration record at sequence one. -/
def ownerAccepted (index : Nat) : Entry → Option Std.U64
  | ⟨.inl (.inr (.beaconRaw owner _)), .Some message⟩ => if owner = index then some message.sequence else none
  | ⟨.inl (.inr (.finish owner _)), some _⟩ => if owner = index then some 1#u64 else none
  | _ => none

/-- Every sequence number Server peer `kid` accepted, in transcript order. -/
def peerSequences (transcript : List Entry) (kid : Std.U64) : List Std.U64 :=
  transcript.filterMap (peerAccepted kid)

/-- Every sequence number Beacon owner `index` accepted, in transcript order. -/
def ownerSequences (transcript : List Entry) (index : Nat) : List Std.U64 :=
  transcript.filterMap (ownerAccepted index)

/-- The receive positions of accepted sequence numbers. -/
def positions (sequences : List Std.U64) : List Nat := sequences.map fun sequence => sequence.val - 1

/-- A record handle's kernel, if any, carries the source receive relation with its accepted positions consumed; a handle without a kernel accepted nothing. -/
def Holds (c : Pqxdh.Crypto) (kernel : Option ConcreteRatchetKernel) (sequences : List Std.U64) : Prop :=
  match kernel with
  | some kernel => ∃ sendOrigin receiveOrigin,
      RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel (positions sequences)
  | none => sequences = []

/-- The CE-C3 run invariant: every Server peer and every Beacon owner satisfies `Holds` for the sequence numbers the transcript shows it accepting. -/
structure Tracked (c : Pqxdh.Crypto) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK) : Prop where
  peers : ∀ kid, Holds c (peerKernel state.native.shared.2.server.server kid) (peerSequences transcript kid)
  owners : ∀ index, Holds c (ownerKernel state.native.owners[index]?) (ownerSequences transcript index)

/-- A kernel kept, or a live kernel installed where none was, keeps `Holds`. -/
theorem holds_step (c : Pqxdh.Crypto) (before after : Option ConcreteRatchetKernel) (sequences : List Std.U64)
    (held : Holds c before sequences)
    (step : after = before ∨ (before = none ∧ ∃ kernel, after = some kernel ∧ Live c kernel)) :
    Holds c after sequences := by
  rcases step with same | ⟨absent, kernel, installed, live⟩
  · rw [same]
    exact held
  · rw [absent] at held
    change sequences = [] at held
    rw [installed, held]
    exact live

/-- The consumed positions may be listed in any order. -/
theorem consumed_perm {c : Pqxdh.Crypto} {sendOrigin receiveOrigin : RatchetChain} {kernel : ConcreteRatchetKernel}
    {first second : List Nat} (permuted : first.Perm second)
    (consumed : RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel first) :
    RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel second := by
  obtain ⟨send, receive, refines, aligned, spent, unique⟩ := consumed
  exact ⟨send, receive, refines, aligned, fun index member => spent index (permuted.mem_iff.mpr member),
    permuted.nodup_iff.mp unique⟩

/-- The sequence number a receive reply accepts, if any. -/
def acceptedOf : core.option.Option RawCtxWholeOwner.Decrypted → List Std.U64
  | .Some message => [message.sequence]
  | .None => []

/-- A receive on a kernel that holds its accepted positions holds them with the new acceptance appended. -/
theorem holds_receive (c : Pqxdh.Crypto) (kernel : ConcreteRatchetKernel) (sequences : List Std.U64)
    (sendOrigin receiveOrigin : RatchetChain) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (consumed : RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel
      (RawCtxReceiveConsumption.recordReply reply (positions sequences))) :
    Holds c (some kernel) (sequences ++ acceptedOf reply) := by
  refine ⟨sendOrigin, receiveOrigin, ?_⟩
  cases reply with
  | none => simpa [RawCtxReceiveConsumption.recordReply, acceptedOf] using consumed
  | some message =>
      apply consumed_perm _ consumed
      simp only [RawCtxReceiveConsumption.recordReply, acceptedOf, positions, List.map_append, List.map_cons,
        List.map_nil]
      exact (List.perm_append_singleton _ _).symm

/-- Logging the produced frames changes no supported record result. -/
theorem logged_support {Result S : Type} (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S ProbComp))
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : S)
    (result : (Result × List PqxdhDeploymentNative.Frame) × S)
    (member : result ∈ support ((simulateQ impl (PqxdhDeploymentNative.logged work)).run state)) :
    (result.1.1, result.2) ∈ support ((simulateQ impl work).run state) := by
  have forgotten := PqxdhDeploymentNative.logged_forget work []
  rw [← forgotten, simulateQ_map, StateT.run_map, support_map]
  exact ⟨result, member, rfl⟩

/-- The accepted sequence numbers of a peer after one more entry. -/
theorem peerSequences_append (transcript : List Entry) (entry : Entry) (kid : Std.U64) :
    peerSequences (transcript ++ [entry]) kid = peerSequences transcript kid ++ (peerAccepted kid entry).toList := by
  simp only [peerSequences, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases peerAccepted kid entry <;> rfl

/-- The accepted sequence numbers of an owner after one more entry. -/
theorem ownerSequences_append (transcript : List Entry) (entry : Entry) (index : Nat) :
    ownerSequences (transcript ++ [entry]) index =
      ownerSequences transcript index ++ (ownerAccepted index entry).toList := by
  simp only [ownerSequences, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases ownerAccepted index entry <;> rfl

/-- What a Server raw receive entry shows a peer accepting. -/
theorem peerAccepted_server (kid : Std.U64) (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    :
    peerAccepted kid ⟨.inl (.inr (.serverRaw raw)), reply⟩ =
      match reply with
      | .Some message => if message.keyId = kid then some message.sequence else none
      | .None => none := by
  cases reply <;> rfl

/-- The routed-receive form of the Server raw step: a supported routed receive on the live peer map keeps the invariant for any state that installs its peer map and keeps the owners. -/
theorem tracked_server (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (route :
    RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (transcript : List Entry)
    (state : PqxdhDeploymentNative.State KemSK) (tracked : Tracked source.crypto transcript state)
    (primitive : RawCtxSharedPrimitive.SharedState Unit)
    (reached : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Unit Unit) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (opened : reached ∈ support (RawCtxServerRouting.rawGame (RawCtxReceiveConsumption.receiveNative source) route
      decode raw (PqxdhDeploymentNative.serverView state) primitive))
    (after : PqxdhDeploymentNative.State KemSK) (server : after.native.shared.2.server.server = reached.1.2.server)
    (owners : after.native.owners = state.native.owners) :
    Tracked source.crypto (transcript ++ [⟨.inl (.inr (.serverRaw raw)), reached.1.1⟩]) after := by
  have quiet : ∀ index, ownerAccepted index ⟨.inl (.inr (.serverRaw raw)), reached.1.1⟩ = none := fun _ => rfl
  refine ⟨fun kid => ?_, fun index => ?_⟩
  · rw [server, peerSequences_append, peerAccepted_server]
    rcases RawCtxServerRouting.rawGame_cases _ route decode raw _ primitive reached opened with
      rejected | ⟨routed, peer, received, routedEq, found, receivedMember, shape⟩
    · rw [rejected]
      simp only [Option.toList_none, List.append_nil]
      exact tracked.peers kid
    · have keyId : ∀ message, reached.1.1 = .Some message → message.keyId = routed := by
        intro message success
        obtain ⟨kid', _, _, _, _, _, _, routed', _, _, keyEq, _⟩ := RawCtxServerRouting.rawGame_success _ route decode
          raw _ primitive reached opened message success
        rw [routedEq, Option.some.injEq] at routed'
        rw [keyEq, routed']
      rw [shape] at keyId ⊢
      by_cases same : kid = routed
      · subst same
        have held := tracked.peers kid
        have kernelOf : peerKernel state.native.shared.2.server.server kid = some peer.kernel := by
          change (state.native.shared.2.server.server.peers kid).map (·.kernel) = some peer.kernel
          change state.native.shared.2.server.server.peers kid = some peer at found
          rw [found, Option.map_some]
        rw [kernelOf] at held
        obtain ⟨sendOrigin, receiveOrigin, consumed⟩ := held
        have next := RawCtxReceiveConsumption.raw_spent source sendOrigin receiveOrigin _ decode raw _ consumed
          primitive
          received receivedMember
        have holds := holds_receive source.crypto _ _ sendOrigin receiveOrigin received.1.1 next
        have kernelAfter : peerKernel (RawCtxServerRouting.putPeer (PqxdhDeploymentNative.serverView state).server kid
            peer received.1.2.owner.kernel) kid = some received.1.2.owner.kernel := by
          simp only [peerKernel, RawCtxServerRouting.putPeer_selected, Option.map_some]
        rw [kernelAfter]
        have accepted : (match received.1.1 with
            | .Some message => if message.keyId = kid then some message.sequence else none
            | .None => none).toList = acceptedOf received.1.1 := by
          cases reply : received.1.1 with
          | none => rfl
          | some message =>
              have own := keyId message reply
              simp only [own, ite_true, Option.toList_some, acceptedOf]
        rw [accepted]
        exact holds
      · have kernelAfter : peerKernel (RawCtxServerRouting.putPeer (PqxdhDeploymentNative.serverView state).server
            routed peer received.1.2.owner.kernel) kid = peerKernel state.native.shared.2.server.server kid := by
          simp only [peerKernel, RawCtxServerRouting.putPeer_other _ _ _ _ _ same]
          rfl
        rw [kernelAfter]
        have nothing : (match received.1.1 with
            | .Some message => if message.keyId = kid then some message.sequence else none
            | .None => none) = none := by
          cases reply : received.1.1 with
          | none => rfl
          | some message =>
              have own := keyId message reply
              simp only [own, Ne.symm same, ite_false]
        simp only [nothing, Option.toList_none, List.append_nil]
        exact tracked.peers kid
  · rw [owners, ownerSequences_append, quiet, Option.toList_none, List.append_nil]
    exact tracked.owners index

/-- A Server raw receive keeps the invariant: only the routed peer can accept, its kernel consumes the accepted position, and every other peer and every owner is unchanged. -/
theorem serverRaw_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) (transcript : List Entry)
    (state : PqxdhDeploymentNative.State KemSK) (tracked : Tracked setup.source.crypto transcript state)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route (.inr raw)).run state)) :
    Tracked setup.source.crypto (transcript ++ [⟨.inl (.inr (.serverRaw raw)), result.1⟩]) result.2 := by
  have fields := PqxdhDeploymentNative.serverStep_fields setup codec route (.inr raw) state result supported
  simp only [PqxdhDeploymentNative.serverStep, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  change inner ∈ support (StateT.run (PqxdhDeploymentNative.record setup codec _) state.native) at member
  rw [PqxdhDeploymentNative.record_run, support_map] at member
  obtain ⟨recorded, recordedMember, rfl⟩ := member
  have opened := logged_support _ _ _ recorded recordedMember
  change _ ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec) (RawCtxServerMixed.rawServer route
    codec.frameRead raw (PqxdhDeploymentNative.serverView state))).run _) at opened
  rw [RawCtxServerMixed.raw_interpretation, PqxdhDeploymentNative.primitives,
    RawCtxReceiveConsumption.shared_receiveNative] at opened
  exact tracked_server setup.source route codec.frameRead raw transcript state tracked _ _ opened _ rfl fields.1

/-- An entry that shows no handle accepting keeps the invariant. -/
theorem tracked_quiet (c : Pqxdh.Crypto) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (entry : Entry) (tracked : Tracked c transcript state) (quietPeer : ∀ kid, peerAccepted kid entry = none)
    (quietOwner : ∀ index, ownerAccepted index entry = none) : Tracked c (transcript ++ [entry]) state := by
  refine ⟨fun kid => ?_, fun index => ?_⟩
  · rw [peerSequences_append, quietPeer, Option.toList_none, List.append_nil]
    exact tracked.peers kid
  · rw [ownerSequences_append, quietOwner, Option.toList_none, List.append_nil]
    exact tracked.owners index

/-- Composition of query implementations is associative. -/
theorem compose_assoc {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}
    {m : Type → Type} [Monad m] [LawfulMonad m] (first : QueryImpl spec₁ m) (second : QueryImpl spec₂ (OracleComp
      spec₁))
    (third : QueryImpl spec₃ (OracleComp spec₂)) : (first ∘ₛ second) ∘ₛ third = first ∘ₛ (second ∘ₛ third) := by
  funext query
  simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]

/-- A Server send keeps the invariant with the transcript fixed: the addressed peer's kernel advances its send chain only. -/
theorem serverSend_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (plaintext : Pqxdh.Bytes) (kid : Std.U64) (transcript : List Entry)
    (state : PqxdhDeploymentNative.State KemSK) (tracked : Tracked setup.source.crypto transcript state)
    (result : Option RawCtxSourceSend.Encrypted × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route (.inl (plaintext, kid))).run
      state)) :
    Tracked setup.source.crypto transcript result.2 := by
  have fields := PqxdhDeploymentNative.serverStep_fields setup codec route (.inl (plaintext, kid)) state result
    supported
  simp only [PqxdhDeploymentNative.serverStep, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  change inner ∈ support (StateT.run (PqxdhDeploymentNative.record setup codec _) state.native) at member
  rw [PqxdhDeploymentNative.record_run, support_map] at member
  obtain ⟨recorded, recordedMember, rfl⟩ := member
  have sent := logged_support _ _ _ recorded recordedMember
  change _ ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec) (RawCtxServerMixed.sendServer
    (PqxdhDeploymentNative.senderId state) plaintext kid (PqxdhDeploymentNative.serverView state))).run _) at sent
  rw [RawCtxServerMixed.send_interpretation] at sent
  refine ⟨fun other => ?_, fun index => ?_⟩
  · change Holds _ (peerKernel recorded.1.1.2.server other) _
    rcases RawCtxServerSend.sendGame_cases _ _ plaintext kid _ _ _ sent with ⟨_, missing⟩ | ⟨peer, step, found,
      stepMember, shape⟩
    · rw [congrArg (fun reached => reached.1.2) missing]
      exact tracked.peers other
    · rw [congrArg (fun reached => reached.1.2) shape]
      by_cases same : other = kid
      · subst same
        have held := tracked.peers other
        have kernelOf : peerKernel state.native.shared.2.server.server other = some peer.kernel := by
          change (state.native.shared.2.server.server.peers other).map (·.kernel) = some peer.kernel
          change state.native.shared.2.server.server.peers other = some peer at found
          rw [found, Option.map_some]
        rw [kernelOf] at held
        obtain ⟨sendOrigin, receiveOrigin, consumed⟩ := held
        rw [compose_assoc, ← RawCtxMixedOwner.sendAdapter] at stepMember
        have next := RawCtxReceiveConsumption.send_spent setup.source codec.frameWrite sendOrigin receiveOrigin _ _
          plaintext _ consumed _ step stepMember
        have kernelAfter : peerKernel (RawCtxServerRouting.putPeer (PqxdhDeploymentNative.serverView state).server
            other peer step.1.2.owner.kernel) other = some step.1.2.owner.kernel := by
          simp only [peerKernel, RawCtxServerRouting.putPeer_selected, Option.map_some]
        show Holds _ (peerKernel (RawCtxServerRouting.putPeer (PqxdhDeploymentNative.serverView state).server
          other peer step.1.2.owner.kernel) other) _
        rw [kernelAfter]
        exact ⟨sendOrigin, receiveOrigin, next⟩
      · have kernelAfter : peerKernel (RawCtxServerRouting.putPeer (PqxdhDeploymentNative.serverView state).server
            kid peer step.1.2.owner.kernel) other = peerKernel state.native.shared.2.server.server other := by
          simp only [peerKernel, RawCtxServerRouting.putPeer_other _ _ _ _ _ same]
          rfl
        rw [kernelAfter]
        exact tracked.peers other
  · rw [fields.1]
    exact tracked.owners index

/-- A Beacon raw receive on the shared record primitives: an owner that is not Established rejects and keeps its Beacon; an Established owner runs the source raw receive on its kernel and reinstalls the returned kernel. -/
theorem beacon_raw_cases {Identity DhPair KemPair : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (beacon : RawCtxBeaconLifecycle.State Identity DhPair KemPair)
    (primitive : RawCtxSharedPrimitive.SharedState Unit)
    (reached : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxBeaconLifecycle.State Identity DhPair KemPair) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (member : reached ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec)
      ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inr raw)).run beacon)).run primitive)) :
    (reached.1.1 = .None ∧ reached.1.2.beacon = beacon.beacon) ∨
      ∃ control associatedData kernel opened, beacon.beacon.phase = .established control associatedData kernel ∧
        opened ∈ support (RawCtxWholeOwner.rawGame (RawCtxReceiveConsumption.receiveNative setup.source) codec.frameRead
          raw (RawCtxBeaconLifecycle.selected beacon control associatedData kernel) primitive) ∧
        reached.1.1 = opened.1.1 ∧
        reached.1.2.beacon.phase = .established control associatedData opened.1.2.owner.kernel := by
  cases phase : beacon.beacon.phase with
  | established control associatedData kernel =>
      right
      have unfolded : (RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inr raw)).run beacon = (do
          let result ← (RawCtxMixedOwner.ownerImpl beacon.beacon.identityKeyId codec.frameRead (.inr raw)).run
            (RawCtxBeaconLifecycle.selected beacon control associatedData kernel)
          pure (result.1, RawCtxBeaconLifecycle.reinstall beacon control associatedData result.2)) := by
        simp only [StateT.run, RawCtxBeaconLifecycle.beaconImpl, phase]
      rw [unfolded, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨opened, openedMember, rest⟩ := member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      subst rest
      refine ⟨control, associatedData, kernel, opened, rfl, ?_, rfl, rfl⟩
      unfold RawCtxWholeOwner.rawGame
      rw [← RawCtxReceiveConsumption.shared_receiveNative setup.source codec.frameWrite, QueryImpl.simulateQ_compose]
      exact openedMember
  | _ =>
      left
      have unfolded : (RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inr raw)).run beacon =
          pure (RawCtxBeaconLifecycle.rejected (.inr raw) beacon) := by
        simp only [StateT.run, RawCtxBeaconLifecycle.beaconImpl, phase]
      rw [unfolded, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩

/-- A Beacon send on the shared record primitives: an owner that is not Established keeps its Beacon; an Established owner runs the source send on its kernel and reinstalls the returned kernel. -/
theorem beacon_send_cases {Identity DhPair KemPair : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (plaintext : Pqxdh.Bytes) (beacon : RawCtxBeaconLifecycle.State Identity DhPair
      KemPair)
    (primitive : RawCtxSharedPrimitive.SharedState Unit)
    (reached : (Option RawCtxSourceSend.Encrypted × RawCtxBeaconLifecycle.State Identity DhPair KemPair) ×
      RawCtxSharedPrimitive.SharedState Unit)
    (member : reached ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec)
      ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inl plaintext)).run beacon)).run primitive)) :
    reached.1.2.beacon = beacon.beacon ∨
      ∃ control associatedData kernel step, beacon.beacon.phase = .established control associatedData kernel ∧
        step ∈ support (RawCtxSourceSend.sendGame (RawCtxReceiveConsumption.sendNative setup.source codec.frameWrite)
          beacon.beacon.identityKeyId plaintext (RawCtxBeaconLifecycle.selected beacon control associatedData kernel)
          primitive) ∧
        reached.1.2.beacon.phase = .established control associatedData step.1.2.owner.kernel := by
  cases phase : beacon.beacon.phase with
  | established control associatedData kernel =>
      right
      have unfolded : (RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inl plaintext)).run beacon = (do
          let result ← (RawCtxMixedOwner.ownerImpl beacon.beacon.identityKeyId codec.frameRead (.inl plaintext)).run
            (RawCtxBeaconLifecycle.selected beacon control associatedData kernel)
          pure (result.1, RawCtxBeaconLifecycle.reinstall beacon control associatedData result.2)) := by
        simp only [StateT.run, RawCtxBeaconLifecycle.beaconImpl, phase]
      rw [unfolded, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, rest⟩ := member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      subst rest
      refine ⟨control, associatedData, kernel, step, rfl, ?_, rfl⟩
      rw [RawCtxSourceSend.sendGame, RawCtxReceiveConsumption.sendNative, QueryImpl.simulateQ_compose]
      exact stepMember
  | _ =>
      left
      have unfolded : (RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inl plaintext)).run beacon =
          pure (RawCtxBeaconLifecycle.rejected (.inl plaintext) beacon) := by
        simp only [StateT.run, RawCtxBeaconLifecycle.beaconImpl, phase]
      rw [unfolded, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl

/-- A Beacon record entry shows no Server peer accepting. -/
theorem peerAccepted_beacon (kid : Std.U64) (index : Nat) (raw : Pqxdh.Bytes)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    peerAccepted kid ⟨.inl (.inr (.beaconRaw index raw)), reply⟩ = none := by
  cases reply <;> rfl

/-- What a Beacon raw receive entry shows an owner accepting. -/
theorem ownerAccepted_beacon (other index : Nat) (raw : Pqxdh.Bytes) (reply : core.option.Option
    RawCtxWholeOwner.Decrypted) :
    (ownerAccepted other ⟨.inl (.inr (.beaconRaw index raw)), reply⟩).toList =
      if index = other then acceptedOf reply else [] := by
  cases reply with
  | none => split <;> rfl
  | some message =>
      by_cases same : index = other
      · simp [ownerAccepted, acceptedOf, same]
      · simp [ownerAccepted, same]

/-- A Beacon raw receive keeps the invariant: only the addressed owner can accept, its kernel consumes the accepted position, and the Server and every other owner are unchanged. -/
theorem beaconRaw_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (raw : Pqxdh.Bytes) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (tracked : Tracked setup.source.crypto transcript state)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index (.inr raw)).run state)) :
    Tracked setup.source.crypto (transcript ++ [⟨.inl (.inr (.beaconRaw index raw)), result.1⟩]) result.2 := by
  have fields := PqxdhDeploymentNative.beaconStep_fields setup codec index (.inr raw) state result supported
  refine ⟨fun kid => ?_, fun other => ?_⟩
  · rw [peerSequences_append, peerAccepted_beacon, Option.toList_none, List.append_nil, fields.2.2.1]
    exact tracked.peers kid
  · rw [ownerSequences_append, ownerAccepted_beacon]
    by_cases same : index = other
    · subst same
      simp only [↓reduceIte]
      unfold PqxdhDeploymentNative.beaconStep at supported
      cases found : state.native.owners[index]? with
      | none =>
          simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          simpa only [found, acceptedOf, List.append_nil, PqxdhDeploymentNative.absent] using tracked.owners index
      | some owner =>
          simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          change inner ∈ support (StateT.run (PqxdhDeploymentNative.record setup codec _) state.native) at member
          rw [PqxdhDeploymentNative.record_run, support_map] at member
          obtain ⟨recorded, recordedMember, rfl⟩ := member
          have opened := logged_support _ _ _ recorded recordedMember
          have bound := (List.getElem?_eq_some_iff.mp found).1
          show Holds _ (ownerKernel ((state.native.owners.set index { owner with beacon := recorded.1.1.2.beacon
            })[index]?))
            (ownerSequences transcript index ++ acceptedOf recorded.1.1.1)
          rw [List.getElem?_set_self bound]
          have held := tracked.owners index
          rw [found] at held
          rcases beacon_raw_cases setup codec raw _ _ _ opened with ⟨rejected, sameBeacon⟩ |
            ⟨control, associatedData, kernel, received, phase, receivedMember, reply, newPhase⟩
          · simp only at rejected sameBeacon
            rw [rejected, sameBeacon]
            simpa only [acceptedOf, List.append_nil] using held
          · simp only at reply newPhase phase
            have kernelOf : ownerKernel (some owner) = some kernel := by
              simp only [ownerKernel, phase]
            rw [kernelOf] at held
            obtain ⟨sendOrigin, receiveOrigin, consumed⟩ := held
            have next := RawCtxReceiveConsumption.raw_spent setup.source sendOrigin receiveOrigin _ codec.frameRead raw
              _
              consumed _ received receivedMember
            have holds := holds_receive setup.source.crypto _ _ sendOrigin receiveOrigin received.1.1 next
            have kernelAfter : ownerKernel (some { owner with beacon := recorded.1.1.2.beacon }) =
                some received.1.2.owner.kernel := by
              simp only [ownerKernel, newPhase]
            rw [kernelAfter, reply]
            exact holds
    · simp only [same, ↓reduceIte, List.append_nil]
      rw [(fields.2.2.2.2.2.2.2 other (Ne.symm same)).1]
      exact tracked.owners other

/-- A Beacon send keeps the invariant with the transcript fixed: the addressed owner's kernel advances its send chain only. -/
theorem beaconSend_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (plaintext : Pqxdh.Bytes) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (tracked : Tracked setup.source.crypto transcript state)
    (result : Option RawCtxSourceSend.Encrypted × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index (.inl plaintext)).run state)) :
    Tracked setup.source.crypto transcript result.2 := by
  have fields := PqxdhDeploymentNative.beaconStep_fields setup codec index (.inl plaintext) state result supported
  refine ⟨fun kid => ?_, fun other => ?_⟩
  · rw [fields.2.2.1]
    exact tracked.peers kid
  · by_cases same : index = other
    · subst same
      unfold PqxdhDeploymentNative.beaconStep at supported
      cases found : state.native.owners[index]? with
      | none =>
          simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact tracked.owners index
      | some owner =>
          simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          change inner ∈ support (StateT.run (PqxdhDeploymentNative.record setup codec _) state.native) at member
          rw [PqxdhDeploymentNative.record_run, support_map] at member
          obtain ⟨recorded, recordedMember, rfl⟩ := member
          have opened := logged_support _ _ _ recorded recordedMember
          have bound := (List.getElem?_eq_some_iff.mp found).1
          show Holds _ (ownerKernel ((state.native.owners.set index { owner with beacon := recorded.1.1.2.beacon
            })[index]?))
            (ownerSequences transcript index)
          rw [List.getElem?_set_self bound]
          have held := tracked.owners index
          rw [found] at held
          rcases beacon_send_cases setup codec plaintext _ _ _ opened with sameBeacon |
            ⟨control, associatedData, kernel, step, phase, stepMember, newPhase⟩
          · simp only at sameBeacon
            rw [sameBeacon]
            exact held
          · simp only at newPhase phase
            have kernelOf : ownerKernel (some owner) = some kernel := by
              simp only [ownerKernel, phase]
            rw [kernelOf] at held
            obtain ⟨sendOrigin, receiveOrigin, consumed⟩ := held
            have next := RawCtxReceiveConsumption.send_spent setup.source codec.frameWrite sendOrigin receiveOrigin _ _
              plaintext _ consumed _ step stepMember
            have kernelAfter : ownerKernel (some { owner with beacon := recorded.1.1.2.beacon }) =
                some step.1.2.owner.kernel := by
              simp only [ownerKernel, newPhase]
            rw [kernelAfter]
            exact ⟨sendOrigin, receiveOrigin, next⟩
    · rw [(fields.2.2.2.2.2.2.2 other (Ne.symm same)).1]
      exact tracked.owners other

/-- A native registration step that keeps every established kernel and every peer kernel except for live installations keeps the invariant. -/
theorem tracked_source (c : Pqxdh.Crypto) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (native : PqxdhRegistrationSchedule.State KemSK) (tracked : Tracked c transcript state)
    (peers : PeerStep c state.native.shared.2.server.server native.shared.2.server.server)
    (owners : OwnersSame state.native.owners native.owners) : Tracked c transcript { state with native := native } :=
  ⟨fun kid => holds_step c _ _ _ (tracked.peers kid) (peers kid),
    fun index => by
      change Holds c (ownerKernel native.owners[index]?) _
      rw [owners index]
      exact tracked.owners index⟩

/-- What a finish entry shows an owner accepting. -/
theorem ownerAccepted_finish (other index : Nat) (raw : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes) :
    (ownerAccepted other ⟨.inl (.inr (.finish index raw)), reply⟩).toList =
      if index = other ∧ reply.isSome then [1#u64] else [] := by
  cases reply with
  | none => simp [ownerAccepted]
  | some plaintext =>
      by_cases same : index = other
      · simp [ownerAccepted, same]
      · simp [ownerAccepted, same]

/-- A Beacon finish keeps the invariant: a successful finish establishes its owner with a kernel that consumed sequence one, which the transcript shows that owner accepting. -/
theorem finish_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes) (transcript : List Entry)
    (state : PqxdhDeploymentNative.State KemSK) (tracked : Tracked setup.source.crypto transcript state)
    (result : Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.onNative
      (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.finish index raw)))).run state)) :
    Tracked setup.source.crypto (transcript ++ [⟨.inl (.inr (.finish index raw)), result.1⟩]) result.2 := by
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result supported
  obtain ⟨peers, _⟩ := PqxdhDeploymentRecordKernels.source_step setup codec checks serverSeed (.finish index raw)
    state.native inner innerMember
  obtain ⟨others, rejected, accepted⟩ := PqxdhDeploymentRecordKernels.finish_owners setup codec index raw state.native
    inner innerMember
  refine ⟨fun kid => ?_, fun other => ?_⟩
  · rw [peerSequences_append, (show peerAccepted kid ⟨.inl (.inr (.finish index raw)), inner.1⟩ = none by
      cases inner.1 <;> rfl), Option.toList_none, List.append_nil]
    exact holds_step _ _ _ _ (tracked.peers kid) (peers kid)
  · rw [ownerSequences_append, ownerAccepted_finish]
    change Holds _ (ownerKernel inner.2.owners[other]?) _
    by_cases same : index = other
    · subst same
      cases reply : inner.1 with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte, List.append_nil]
          rw [rejected reply]
          exact tracked.owners index
      | some plaintext =>
          obtain ⟨before, kernel, after, finished⟩ := accepted plaintext reply
          have held := tracked.owners index
          rw [before] at held
          change ownerSequences transcript index = [] at held
          simp only [Option.isSome_some, and_self, ↓reduceIte]
          rw [after, held]
          exact finished
    · simp only [same, false_and, ↓reduceIte, List.append_nil]
      rw [others other (Ne.symm same)]
      exact tracked.owners other

/-- One coin or command of the native deployment handler keeps the invariant, with the command and its reply appended to the transcript. -/
theorem command_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (tracked : Tracked setup.source.crypto transcript state)
    (result : Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state))
      :
    Tracked setup.source.crypto (transcript ++ [⟨.inl query, result.1⟩]) result.2 := by
  have source : ∀ (request : PqxdhRegistrationSchedule.Request) (notFinish : ∀ index raw, request ≠ .finish index raw)
      (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhDeploymentNative.State KemSK),
      result ∈ support ((PqxdhDeploymentNative.onNative
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request))).run state) →
      Tracked setup.source.crypto transcript result.2 := by
    intro request notFinish result member
    obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result member
    obtain ⟨peers, owners⟩ := PqxdhDeploymentRecordKernels.source_step setup codec checks serverSeed request
      state.native
      inner innerMember
    exact tracked_source _ transcript state inner.2 tracked peers (owners notFinish)
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact tracked_quiet _ transcript state _ tracked (fun _ => rfl) (fun _ => rfl)
  · cases command with
    | create pin keyId =>
        cases parsed : parsePin pin with
        | none =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            subst supported
            exact tracked_quiet _ transcript state _ tracked (fun _ => rfl) (fun _ => rfl)
        | some word =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, support_map, Set.mem_image] at supported
            obtain ⟨inner, member, rfl⟩ := supported
            exact tracked_quiet _ transcript _ _ (source (.create word keyId) (fun _ _ => nofun) inner member)
              (fun _ => rfl) (fun _ => rfl)
    | bundle owner =>
        exact tracked_quiet _ transcript _ _ (source (.bundle owner) (fun _ _ => nofun) result supported)
          (fun _ => rfl) (fun _ => rfl)
    | accept raw =>
        exact tracked_quiet _ transcript _ _ (source (.accept raw) (fun _ _ => nofun) result supported)
          (fun _ => rfl) (fun _ => rfl)
    | build session payload =>
        exact tracked_quiet _ transcript _ _ (source (.build session payload) (fun _ _ => nofun) result supported)
          (fun _ => rfl) (fun _ => rfl)
    | finish owner raw =>
        exact finish_tracked setup codec checks serverSeed owner raw transcript state tracked result supported
    | hmac key message =>
        exact tracked_quiet _ transcript _ _ (source (.hmac key message) (fun _ _ => nofun) result supported)
          (fun _ => rfl) (fun _ => rfl)
    | hash bytes =>
        exact tracked_quiet _ transcript _ _ (source (.hash bytes) (fun _ _ => nofun) result supported)
          (fun _ => rfl) (fun _ => rfl)
    | serverSend kid plaintext =>
        exact tracked_quiet _ transcript _ _ (serverSend_tracked setup codec route plaintext kid transcript state
          tracked result supported) (fun _ => rfl) (fun _ => rfl)
    | serverRaw raw => exact serverRaw_tracked setup codec route raw transcript state tracked result supported
    | beaconSend index plaintext =>
        exact tracked_quiet _ transcript _ _ (beaconSend_tracked setup codec index plaintext transcript state
          tracked result supported) (fun _ => rfl) (fun _ => rfl)
    | beaconRaw index raw =>
        exact beaconRaw_tracked setup codec index raw transcript state tracked result supported

/-- A native-interface program that issues only coins and sends keeps the invariant with the transcript fixed. -/
theorem coinSend_tracked {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (program : OracleComp Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (tracked : Tracked setup.source.crypto transcript state) (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    Tracked setup.source.crypto transcript result.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact tracked
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have middleTracked : Tracked setup.source.crypto transcript middle := by
        rcases query with coin | command
        · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          exact tracked
        · cases command with
          | serverSend kid plaintext =>
              exact serverSend_tracked setup codec route plaintext kid transcript state tracked _ first
          | beaconSend index plaintext =>
              exact beaconSend_tracked setup codec index plaintext transcript state tracked _ first
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      exact ih reply restBound middle middleTracked second

/-- Every query of the complete experiment, including the secrecy commands, keeps the invariant. -/
theorem experiment_tracked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (state : PqxdhDeploymentSecrecy.State KemSK)
    (tracked : Tracked setup.source.crypto state.1.transcript state.2)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    Tracked setup.source.crypto result.2.1.transcript result.2.2 := by
  rcases state with ⟨ledger, native⟩
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    exact command_tracked setup codec checks route serverSeed request ledger.transcript native tracked answer
      answerMember
  · have value : reached.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run
        ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
        _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, member, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds
      secrecy
      ledger reached.1 value
    have kept := coinSend_tracked setup codec checks route serverSeed _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger)
      ledger.transcript native tracked reached member
    simp only [recorded]
    exact tracked_quiet _ ledger.transcript _ _ kept (fun _ => rfl) (fun _ => rfl)

/-- The Server constructor starts with no peer. -/
theorem construct_peers (primitives : Primitives) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (sender : Std.U64) (runtime : A) (created : PqxdhLiveServerConstruction.Created Unit) (after : A)
    (supported : (some created, after) ∈ support
      ((PqxdhLiveServerConstruction.construct primitives ensureInit identityIndex sender none).run runtime)) :
    ∀ kid, created.server.server.peers kid = none := by
  simp only [PqxdhLiveServerConstruction.construct, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨ready, _, supported⟩ := supported
  split at supported
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨seed, _, rfl, _⟩ := supported
    exact fun _ => rfl
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- The CE-C3 invariant along the whole experiment: in either mode, on every outcome of the common deployment experiment, every Server peer and every Beacon owner satisfies `Holds` for the sequence numbers the transcript shows it accepting. -/
theorem tracked_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    Tracked setup.source.crypto final.1.transcript final.2 := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have empty := construct_peers setup.joint ensureInit identityIndex setup.serverKeyId runtime constructed after
      bornMember
    exact OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => Tracked setup.source.crypto state.1.transcript state.2)
      (fun query state tracked result member => experiment_tracked setup codec checks route constructed.seed
        bounds query state tracked result member)
      (asModeO mode adversary) (Ledger.empty, PqxdhDeploymentNative.initial constructed)
      ⟨fun kid => by
        simp [Holds, peerKernel, peerSequences, PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial,
          Ledger.empty, empty kid],
        fun index => by simp [Holds, ownerKernel, ownerSequences, PqxdhDeploymentNative.initial,
          PqxdhRegistrationSchedule.initial, Ledger.empty]⟩ _ executedMember

/-- A handle that satisfies `Holds` accepted no sequence number twice. -/
theorem holds_nodup (c : Pqxdh.Crypto) (kernel : Option ConcreteRatchetKernel) (sequences : List Std.U64)
    (held : Holds c kernel sequences) : sequences.Nodup := by
  cases kernel with
  | none =>
      change sequences = [] at held
      rw [held]
      exact List.nodup_nil
  | some kernel =>
      obtain ⟨_, _, consumed⟩ := held
      exact List.Nodup.of_map _ consumed.spent_nodup

/-- Theorem CE-C3 (record replay, for every owner and peer). In either mode, for every adversary and with no budget, on every outcome of the common deployment experiment, no Server peer and no Beacon owner accepted a record sequence number twice: the sequence numbers of the successful Server raw receives routed to any one peer key ID, and those of the successful raw receives of any one owner, have no duplicate. -/
theorem record_replay_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    (∀ kid, (peerSequences final.1.transcript kid).Nodup) ∧
      ∀ index, (ownerSequences final.1.transcript index).Nodup := by
  have tracked := tracked_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome
    supported created output final reached
  exact ⟨fun kid => holds_nodup _ _ _ (tracked.peers kid), fun index => holds_nodup _ _ _ (tracked.owners index)⟩

end BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.consumed_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.consumed_perm

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.logged_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.logged_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerSequences_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerSequences_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerSequences_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerSequences_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerAccepted_server' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerAccepted_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.serverRaw_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.serverRaw_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.compose_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.compose_assoc

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.serverSend_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.serverSend_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beacon_raw_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beacon_raw_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beacon_send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beacon_send_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerAccepted_beacon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.peerAccepted_beacon

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerAccepted_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerAccepted_beacon

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beaconRaw_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beaconRaw_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beaconSend_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.beaconSend_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerAccepted_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.ownerAccepted_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.finish_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.finish_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.command_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.command_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.coinSend_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.coinSend_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.experiment_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.experiment_tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.construct_peers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.construct_peers

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.tracked_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.holds_nodup

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.record_replay_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay.record_replay_game
