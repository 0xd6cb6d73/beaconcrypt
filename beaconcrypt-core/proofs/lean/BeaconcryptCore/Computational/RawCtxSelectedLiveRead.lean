import BeaconcryptCore.Computational.RawCtxSelectedPublicTrace
import BeaconcryptCore.Computational.RawCtxProtocolReveals

/-!
The three live record-compromise reads forward into the existing concrete role/reveal source. Actual owner selection, optional replies, original request timestamps and the entire role/primitive poststate are retained. The guarded skipped-key lookup is independent of both current-chain interpretations even on malformed slots.

An unavailable current-chain read is a direct exposure event. Outside that event a target-free handler has exactly the actual optional source reply; on the event the actual read returns the selected chain while the target-free handler returns rejection. Known current-chain and skipped-material-key bytes provide at most one available 32-byte candidate per attempted read. This is a value-based candidate projection, not key/handle injectivity or a secrecy bound. Original source attempts still cost one; actual interpreted reads make zero underlying uniform calls, without declaring lookup/log/copy work free.

The full-source specialization retains an explicit selected-kernel representation equation and the non-exposure condition. It does not establish a reached native cut, a complete adaptive exposure coupling, ancestor/root/identity/KEM knowledge policy or an independently sampled target. No native role is fabricated and no secret is resurrected: this module adds no reveal beyond existing installed current chains and guarded skipped material. Private source state is not adversary input. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveRead
open RawCtxSelectedChain RawCtxProtocolReveals PqxdhSecretInputKdf

inductive Read where
  | sendChain
  | receiveChain
  | skippedKey (sequence : Std.U64)
  deriving DecidableEq

def ReadSpec : OracleSpec Read
  | .sendChain | .receiveChain => core.option.Option RatchetChain
  | .skippedKey _ => core.option.Option RatchetMaterial

def request {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount) :
    Read → Request serverCount beaconCount
  | .sendChain => .sendChain owner
  | .receiveChain => .receiveChain owner
  | .skippedKey sequence => .skippedKey owner sequence

noncomputable def nativeRead (read : Read) (entry : Option ConcreteRatchetKernel) : ReadSpec.Range read :=
  match read with
  | .sendChain => match entry with
      | none => .None
      | some kernel => .Some kernel.refined.send_chain
  | .receiveChain => match entry with
      | none => .None
      | some kernel => .Some kernel.refined.receive_chain
  | .skippedKey sequence => match entry with
      | none => .None
      | some kernel => skippedKey kernel sequence

/-- The actual guarded material lookup does not inspect either current chain, including malformed slots. -/
theorem skipped_independent (target : RatchetChain) (entry : Kernel) (sequence : Std.U64) :
    skippedKey (nativeKernel target entry) sequence =
      skippedKey (nativeKernel unusedChain entry) sequence := by
  have h := (skipped_exact (nativeKernel target entry) sequence).symm.trans
    ((RawCtxChainInterpretation.receive_key_chains (interpret target) (interpret target) entry sequence).trans
      ((RawCtxChainInterpretation.receive_key_chains (interpret unusedChain) (interpret unusedChain) entry sequence).symm.trans
        (skipped_exact (nativeKernel unusedChain entry) sequence)))
  injection h

/-- Forward only the chosen read into the original concrete role/reveal source. -/
noncomputable def forward {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount) :
    QueryImpl ReadSpec (OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount))
  | .sendChain => (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).query (.inr (.sendChain owner))
  | .receiveChain => (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).query (.inr (.receiveChain owner))
  | .skippedKey sequence => (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).query (.inr (.skippedKey owner sequence))

def observation {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount)
    (read : Read) (reply : ReadSpec.Range read) : RawCtxProtocolReveals.Observation serverCount beaconCount :=
  match read with
  | .sendChain => ⟨.sendChain owner, reply⟩
  | .receiveChain => ⟨.receiveChain owner, reply⟩
  | .skippedKey sequence => ⟨.skippedKey owner sequence, reply⟩

/-- Original role selection, optional reply, timestamped disclosure and the entire primitive poststate are retained. -/
theorem source_forward {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (owner : Owner serverCount beaconCount) (read : Read)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) ∘ₛ
      forward owner) read).run state =
      pure (nativeRead read (selectedKernel owner state.1.1),
        ((state.1.1, note (observation owner read (nativeRead read (selectedKernel owner state.1.1))) state.1.2), state.2)) := by
  cases read <;> exact congrFun (_root_.simulateQ_spec_query
    (RawCtxProtocolReveals.sourceImpl (PeerMetadata := PeerMetadata) (Identity := Identity)
      (DhPair := DhPair) (KemPair := KemPair) (Auxiliary := Auxiliary)
      source writer serverCount beaconCount senderId route decode) _) state


def slotReply : Slot → core.option.Option RatchetChain
  | .hidden => .None
  | .known chain => .Some chain

/-- The simulator never returns the selected input bytes from an unavailable current-chain slot. -/
noncomputable def labelRead (read : Read) (entry : Option Kernel) : ReadSpec.Range read :=
  match read with
  | .sendChain => match entry with
      | none => .None
      | some kernel => slotReply kernel.send_chain
  | .receiveChain => match entry with
      | none => .None
      | some kernel => slotReply kernel.receive_chain
  | .skippedKey sequence => match entry with
      | none => .None
      | some kernel => skippedKey (nativeKernel unusedChain kernel) sequence

/-- A requested unavailable current chain is direct exposure, independently of byte guesses. -/
def exposed (read : Read) (entry : Option Kernel) : Bool :=
  match read, entry with
  | .sendChain, some kernel => match kernel.send_chain with
      | .hidden => true
      | .known _ => false
  | .receiveChain, some kernel => match kernel.receive_chain with
      | .hidden => true
      | .known _ => false
  | _, _ => false

/-- Outside direct exposure, the target-free read retains the original exact optional source reply. -/
theorem before_exposure (read : Read) (target : RatchetChain) (entry : Option Kernel)
    (safe : exposed read entry = false) :
    nativeRead read (entry.map (nativeKernel target)) = labelRead read entry := by
  cases entry <;> cases read <;> simp_all [nativeRead, labelRead, exposed, skipped_independent]
  all_goals split at safe <;> simp_all [nativeKernel, RawCtxChainInterpretation.mapChains, interpret, slotReply]

/-- The same actual source read and full disclosure history factor through private slots until direct exposure. -/
theorem source_before_exposure {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (owner : Owner serverCount beaconCount) (read : Read)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) (target : RatchetChain) (entry : Option Kernel)
    (selected : selectedKernel owner state.1.1 = entry.map (nativeKernel target))
    (safe : exposed read entry = false) :
    (((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) ∘ₛ
      forward owner) read).run state =
      pure (labelRead read entry,
        ((state.1.1, note (observation owner read (labelRead read entry)) state.1.2), state.2)) := by
  rw [source_forward, selected, before_exposure read target entry safe]

/-- Available 32-byte chain or material-key disclosures enter the same value-based input candidate list. -/
def replyInputs (read : Read) (reply : ReadSpec.Range read) : List RootOutput :=
  match read with
  | .sendChain | .receiveChain => match reply with
      | .None => []
      | .Some chain => [RawCtxSelectedQueryTrace.rootVector chain]
  | .skippedKey _ => match reply with
      | .None => []
      | .Some material => [RawCtxSelectedQueryTrace.rootVector ⟨material.key.bytes⟩]

noncomputable def candidates (read : Read) (entry : Option Kernel) : List RootOutput :=
  replyInputs read (labelRead read entry)

/-- Each attempted reveal contributes at most one available 32-byte value; failed lookups contribute none. -/
theorem reply_length (read : Read) (reply : ReadSpec.Range read) : (replyInputs read reply).length ≤ 1 := by
  cases read <;> cases reply <;> simp [replyInputs]

/-- A flagged chain read actually returns the selected bytes; the target-free handler returns only rejection. -/
theorem exposure_reply (read : Read) (target : RatchetChain) (entry : Option Kernel)
    (hit : exposed read entry = true) :
    match read with
    | .sendChain => nativeRead .sendChain (entry.map (nativeKernel target)) = .Some target ∧
        labelRead .sendChain entry = .None
    | .receiveChain => nativeRead .receiveChain (entry.map (nativeKernel target)) = .Some target ∧
        labelRead .receiveChain entry = .None
    | .skippedKey _ => False := by
  cases entry <;> cases read <;> simp_all only [Option.map_none, Option.map_some]
  all_goals simp only [exposed, Bool.false_eq_true] at hit
  all_goals split at hit <;> simp_all [nativeRead, labelRead, nativeKernel, RawCtxChainInterpretation.mapChains, interpret, slotReply]

/-- The actual source read invokes no underlying uniform oracle, while its source-level attempt is retained. -/
theorem source_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (owner : Owner serverCount beaconCount) (read : Read)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) ∘ₛ
      forward owner) read).run state).IsTotalQueryBound 0 := by
  rw [source_forward]
  trivial

/-- The typed forwarder preserves the original single source reveal attempt. -/
theorem forward_total {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount) (read : Read) :
    (forward owner read).IsTotalQueryBound 1 := by
  cases read <;> exact ⟨Nat.zero_lt_succ 0, fun _ => trivial⟩

end BeaconcryptCore.Computational.RawCtxSelectedLiveRead

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.skipped_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.skipped_independent

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_forward

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.before_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.before_exposure

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_before_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_before_exposure

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.reply_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.reply_length

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.exposure_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.exposure_reply

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.source_uniform

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveRead.forward_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveRead.forward_total
