-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.MldsaServerRouting

/-! The current extracted complete-input prelude uses stored session AD151. currentServerReceive/current_server_exact route through the selected installed metadata, and completedServer_exact specializes that projection to a completed binding. The independent serverReceive/server_exact equations retain historical identity-derived AD281 mathematics. The CE serverRaw equation runs the current router on the deployment Server, whose peers carry their own installed AD151; it is a pointwise model equality. Beacon and owner prelude statements use their actual stored AD151. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
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
    (ad : Std.Array Std.U8 151#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) :=
  simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxNativeFramePrelude.receive reader ad raw state)

/-- The complete native prelude equals the role's actual raw branch, retaining all primitive callbacks and the whole owner. -/
theorem owner_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (ad : Std.Array Std.U8 151#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (sender : Std.U64)
    (associated : state.owner.associatedData = absBytes ad) :
    ownerReceive reader ad raw state =
      (RawCtxMixedOwner.ownerImpl sender (RawCtxFrameDecoding.decode reader.model) (.inr raw)).run state := by
  unfold ownerReceive
  rw [RawCtxNativeFramePrelude.receive_source, RawCtxFrameDecoding.sourceReceive_exact reader.model raw state (by simp [associated, absBytes_length])]
  rfl

/-- Retained historical CE routing model. It retains its identity-derived AD281 and complete raw owner computation; this is not the current extracted Server prelude. -/
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
              let result ← simulateQ RawCtxMixedOwner.receiveAdapter
                ((RawCtxWholeOwner.rawReceive (RawCtxFrameDecoding.decode reader.model) raw).run
                  ⟨RawCtxServerRouting.selectedOwner kid ad peer, state.rawAttempts⟩)
              pure (result.1, ⟨RawCtxServerRouting.putPeer state.server kid peer result.2.owner.kernel,
                result.2.rawAttempts⟩)

/-- The historical CE model retains its complete routing, raw owner and publication equations. It supplies no current native-source certificate. -/
theorem server_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    serverReceive reader raw state = RawCtxServerMixed.rawServer
      (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state := by
  rfl

/-- Current Server routing passes the complete AD151 of the same selected peer to the actual extracted prelude and reinstalls its complete kernel and counter. -/
noncomputable def currentServerReceive
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Metadata PeerMetadata) :=
  match RawCtxFrameDecoding.sender reader.model raw with
  | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
  | some kid => match state.server.peers kid with
    | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
    | some peer => do
        let result ← ownerReceive reader (sessionData peer.metadata) raw
          ⟨MldsaServerRouting.selected (fun metadata => absBytes (sessionData metadata)) kid peer, state.rawAttempts⟩
        pure (result.1, ⟨RawCtxServerRouting.putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)

/-- The current source prelude equals the complete metadata-routed Server receive, for every peer and raw input, without a global AD or identity-injectivity premise. -/
theorem current_server_exact (sessionData : PeerMetadata → Std.Array Std.U8 151#usize)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    currentServerReceive sessionData reader raw state =
      MldsaServerRouting.receive (fun metadata => absBytes (sessionData metadata))
        (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state := by
  unfold currentServerReceive MldsaServerRouting.receive
  cases routed : RawCtxFrameDecoding.sender reader.model raw with
  | none => rfl
  | some kid =>
    simp only
    cases found : state.server.peers kid with
    | none => rfl
    | some peer =>
      simp only
      rw [owner_exact reader (sessionData peer.metadata) raw
        ⟨MldsaServerRouting.selected (fun metadata => absBytes (sessionData metadata)) kid peer, state.rawAttempts⟩ (0#u64) rfl]
      rfl

/-- Completed registration metadata supplies exactly the actual stored AD to the current routing handler. Installation/source ownership is a separate receipt; this theorem invents no session or digest. -/
theorem completedServer_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata session.CompletedRegistrationBinding)
    (sender : Metadata → Std.U64) :
    currentServerReceive (fun binding : session.CompletedRegistrationBinding => binding.associated_data) reader raw state =
      (MldsaServerRouting.handler (fun binding : session.CompletedRegistrationBinding => absBytes binding.associated_data) sender
        (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) (.inr raw)).run state := by
  change currentServerReceive (fun binding : session.CompletedRegistrationBinding => binding.associated_data) reader raw state =
    MldsaServerRouting.receive (fun binding : session.CompletedRegistrationBinding => absBytes binding.associated_data)
      (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state
  exact current_server_exact (fun binding : session.CompletedRegistrationBinding => binding.associated_data) reader raw state

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
  let result ← (record setup codec (logged (currentServerReceive id reader raw (serverView state)))).run state.native
  pure (result.1.1.1, produce (serverTag (.inr raw)) result.1.2
    (withServer { state with native := result.2 } result.1.1.2))

/-- Installing the shared frame reader changes no primitive call or primitive response. -/
theorem primitives_withReader (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    primitives setup (withReader codec reader) = primitives setup codec := by
  rfl

/-- The CE Server receive retains its complete current prelude under each peer's installed AD151, shared-cache effects and state; dynamic extracted correspondence remains current_server_exact. -/
theorem serverRaw_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (serverRaw setup codec reader raw).run state =
      (serverStep setup (withReader codec reader) (RawCtxFrameDecoding.sender reader.model) (.inr raw)).run state := by
  unfold serverRaw serverStep StateT.run
  rw [current_server_exact]
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

/-- The historical CE Server command retains the same model raw computation and complete state. -/
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

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.current_server_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.current_server_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.completedServer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude.completedServer_exact
