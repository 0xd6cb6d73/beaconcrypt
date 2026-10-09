-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! The extracted complete-input prelude at the actual native record interfaces. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude
open PqxdhRefinement
variable {Message Root Metadata PeerMetadata Identity DhPair KemPair Reader Response : Type}

/-- Keep every registration and writer field while installing the shared complete frame reader. -/
def withReader (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhServerAuthExperiment.Codec Reader Response :=
  { codec with frameRead := RawCtxFrameDecoding.decode reader.model }

/-- The native prelude passes the selected stored AD and real optional opening reply through the native primitive interface. -/
noncomputable def ownerReceive (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 153#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) :=
  simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxNativeFramePrelude.receive reader ad raw state)

/-- The complete native prelude equals the role's actual raw branch, retaining all primitive callbacks and the whole owner. -/
theorem owner_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 153#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (sender : Std.U64)
    (associated : state.owner.associatedData = absBytes ad) :
    ownerReceive reader ad raw state =
      (RawCtxMixedOwner.ownerImpl sender (RawCtxFrameDecoding.decode reader.model) (.inr raw)).run state := by
  unfold ownerReceive
  rw [RawCtxNativeFramePrelude.receive_source, RawCtxFrameDecoding.sourceReceive_exact reader.model raw state (by simp [associated, absBytes_length])]
  rfl

/-- The source Server reads the same complete header, looks up AD and the peer, runs the native prelude, and reinstalls the returned kernel. -/
noncomputable def serverReceive (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Metadata PeerMetadata) :=
  match RawCtxFrameDecoding.sender reader.model raw with
  | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
  | some kid =>
      match RawCtxServerRouting.peerAssociatedData state.server kid with
      | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
      | some ad =>
          match state.server.peers kid with
          | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
          | some peer => do
              let result ← ownerReceive reader
                (RawCtxServerRouting.associatedArray state.server.identity peer.identity) raw
                ⟨RawCtxServerRouting.selectedOwner kid ad peer, state.rawAttempts⟩
              pure (result.1, ⟨RawCtxServerRouting.putPeer state.server kid peer result.2.owner.kernel,
                result.2.rawAttempts⟩)

/-- Both Server parses and the selected extracted AD instantiate the exact full native raw program without a selected-peer premise. -/
theorem server_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    serverReceive reader raw state = RawCtxServerMixed.rawServer
      (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state := by
  unfold serverReceive RawCtxServerMixed.rawServer
  cases routed : RawCtxFrameDecoding.sender reader.model raw with
  | none => rfl
  | some kid =>
    cases found : state.server.peers kid <;> simp only [RawCtxServerRouting.peerAssociatedData, found, Bind.bind, Option.bind, pure]
    rw [owner_exact reader _ raw _ kid rfl]
    rfl

/-- The source Beacon admits established records with its stored AD and pinned server, and retains every inactive phase on rejection. -/
noncomputable def beaconReceive (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxBeaconLifecycle.State Identity DhPair KemPair) :=
  match state.beacon.phase with
  | .established control ad kernel => do
      let result ← ownerReceive reader ad raw (RawCtxBeaconLifecycle.selected state control ad kernel)
      pure (result.1, RawCtxBeaconLifecycle.reinstall state control ad result.2)
  | _ => pure (RawCtxBeaconLifecycle.rejected (.inr raw) state)

/-- Every Beacon phase runs exactly the full native prelude program, with no assigned-ID equality premise. -/
theorem beacon_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    beaconReceive reader raw state =
      (RawCtxBeaconLifecycle.beaconImpl (RawCtxFrameDecoding.decode reader.model) (.inr raw)).run state := by
  unfold beaconReceive RawCtxBeaconLifecycle.beaconImpl StateT.run
  cases state.beacon.phase <;> try rfl
  rename_i control ad kernel
  simp only [owner_exact reader ad raw (RawCtxBeaconLifecycle.selected state control ad kernel) state.beacon.identityKeyId rfl]
  rfl

open PqxdhDeploymentNative
variable {ι KemSK : Type} {baseSpec : OracleSpec ι}

/-- The shared-reader Server receive runs with the original CE record interpreter and its complete logs and live state. -/
noncomputable def serverRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (raw : Pqxdh.Bytes) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted) := fun state => do
  let result ← (record setup codec (logged (serverReceive reader raw (serverView state)))).run state.native
  pure (result.1.1.1, produce (serverTag (.inr raw)) result.1.2
    (withServer { state with native := result.2 } result.1.1.2))

/-- Installing the shared frame reader changes no primitive call or primitive response. -/
theorem primitives_withReader (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    primitives setup (withReader codec reader) = primitives setup codec := by
  rfl

/-- The CE raw Server branch is the complete native source prelude, including rejection and shared-cache effects. -/
theorem serverRaw_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (serverRaw setup codec reader raw).run state =
      (serverStep setup (withReader codec reader) (RawCtxFrameDecoding.sender reader.model) (.inr raw)).run state := by
  unfold serverRaw serverStep StateT.run
  rw [server_exact]
  rfl

/-- Look up the actual live Beacon, run its native prelude, and reinstall the complete returned owner and logs. -/
noncomputable def beaconRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (index : Nat) (raw : Pqxdh.Bytes) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted) := fun state =>
  match state.native.owners[index]? with
  | none => pure (.None, state)
  | some owner => do
      let result ← (record setup codec (logged (beaconReceive reader raw
        ⟨owner.beacon, state.ownerRaw index⟩))).run state.native
      pure (result.1.1.1, produce (beaconTag index) result.1.2 { state with
        native := { result.2 with owners := result.2.owners.set index { owner with beacon := result.1.1.2.beacon } }
        ownerRaw := Function.update state.ownerRaw index result.1.1.2.rawAttempts })

/-- The CE raw Beacon branch keeps missing-owner rejection, every lifecycle phase and the entire native poststate. -/
theorem beaconRaw_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (beaconRaw setup codec reader index raw).run state =
      (beaconStep setup (withReader codec reader) index (.inr raw)).run state := by
  unfold beaconRaw beaconStep StateT.run
  cases state.native.owners[index]? <;> try rfl
  simp only [beacon_exact]
  rfl

/-- The actual CE Server command consumes the source program on the same bytes and complete state. -/
theorem handler_serverRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (checks : PqxdhServerAuthExperiment.Checks)
    (serverSeed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (handler setup (withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
      serverSeed (.inr (.serverRaw raw))).run state = (serverRaw setup codec reader raw).run state := by
  exact (serverRaw_exact setup codec reader raw state).symm

/-- The actual CE Beacon command consumes the source program for an arbitrary owner handle. -/
theorem handler_beaconRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (checks : PqxdhServerAuthExperiment.Checks)
    (serverSeed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (handler setup (withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model)
      serverSeed (.inr (.beaconRaw index raw))).run state = (beaconRaw setup codec reader index raw).run state := by
  exact (beaconRaw_exact setup codec reader index raw state).symm

end BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.owner_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.owner_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.server_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.server_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.beacon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.beacon_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.primitives_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.primitives_withReader

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.serverRaw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.serverRaw_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.beaconRaw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.beaconRaw_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.handler_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.handler_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.handler_beaconRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.handler_beaconRaw
