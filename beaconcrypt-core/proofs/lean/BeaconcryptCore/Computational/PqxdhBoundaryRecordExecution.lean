-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRecordPrelude
import BeaconcryptCore.Computational.PqxdhOpenContextBridge

/-! Current owner/Beacon receive-loop transcription uses stored AD151 and CTX227. currentExecuteServer routes the same selected peer metadata into that extracted owner path. The independent executeServer/executeServer_exact equations retain historical AD281 mathematics. The CE executeServerRaw runs the current selected-peer execution on the deployment Server, whose peers carry their own installed AD151; it is a pointwise model equality. The receive loop and outer Rust dispatch remain reviewed transcriptions (RT). -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution
open PqxdhRefinement RawCtxNativeFramePrelude
variable {Message Root Metadata : Type}

/-- Successful native preparation retains an actual borrowed payload whose extracted admission produced the exact stored context. -/
theorem prepared_payload (reader : Reader Message Root) (ad : Std.Array Std.U8 151#usize)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (value : Prepared)
    (execution : prepare reader ad expected raw = ok (some value)) :
    ∃ payload : Slice Std.U8, sliceBytes payload = value.frame.payload ∧
      record.OpenFrameContext.from_frame payload ad value.frame.sender = ok (.Some value.context) := by
  unfold prepare at execution
  split at execution
  · cases execution
  · rw [complete_exact] at execution
    simp only [bind_tc_ok] at execution
    split at execution
    · cases execution
    · split at execution
      · cases execution
      · split at execution
        · cases execution
        · rename_i _ root _ _ _ payload _
          obtain ⟨result, admitted, fields⟩ := BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views payload ad (reader.keyId root)
          rw [admitted] at execution
          cases result with
          | none => cases execution
          | some context =>
            have same := Option.some.inj (RustM.ok.inj execution)
            cases same
            exact ⟨payload, rfl, admitted⟩

/-- After actual successful preparation the production receive executor transcription runs on the same sequence, payload and associated data as the native raw program. -/
theorem prepared_loop (reader : Reader Message Root) (ad : Std.Array Std.U8 151#usize)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (value : Prepared)
    (execution : prepare reader ad expected raw = ok (some value))
    (erased : Std.Array Std.U8 227#usize) (kernel : ConcreteRatchetKernel) :
    PqxdhOpenContextBridge.executeReceiveFrom erased kernel value.frame.sequence value.context =
      (fun result => ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel value.frame.sequence
            ⟨raw, value.frame, absBytes ad⟩)) := by
  obtain ⟨payload, represented, admitted⟩ := prepared_payload reader ad expected raw value execution
  have began := PqxdhOpenContextBridge.begin_receive_map
    (fun (_ : RawCtxWholeOwner.OpenContext) => value.context) kernel value.frame.sequence
    (⟨raw, value.frame, absBytes ad⟩ : RawCtxWholeOwner.OpenContext)
  rw [RawCtxOwnerOracle.begin_exact kernel value.frame.sequence
    (⟨raw, value.frame, absBytes ad⟩ : RawCtxWholeOwner.OpenContext)] at began
  simp only [PqxdhOpenContextBridge.executeReceiveFrom, began, PqxdhOpenContextBridge.map_ok,
    PqxdhOpenBridges.bindResult_ok, RawCtxOwnerOracle.receive]
  exact PqxdhOpenContextBridge.receive_loop_native erased ⟨raw, value.frame, absBytes ad⟩
    value.context payload ad represented rfl admitted _
    (PqxdhOpenContextBridge.begin_context kernel value.frame.sequence _)

/-- Complete native preparation, receive-loop transcription over extracted local steps, actual opening executor and normal-return kernel reinstallation. -/
noncomputable def executeOwner (reader : Reader Message Root) (ad : Std.Array Std.U8 151#usize)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata)) :=
  RawCtxInterpretedOpening.bindResult (prepare reader ad state.owner.expectedSender raw) fun value =>
    match value with
    | none => pure (ok (RawCtxWholeOwner.publish state (state.owner.kernel, .None)))
    | some value =>
        (fun result => RawCtxWholeOwner.publish state <$> result) <$>
          simulateQ RawCtxMixedOwner.receiveLift
            (PqxdhOpenContextBridge.executeReceiveFrom erased state.owner.kernel value.frame.sequence value.context)

/-- The extracted preparation and receive executor transcription equal the complete native owner operation with every actual callback and optional opening reply. -/
theorem executeOwner_exact (reader : Reader Message Root) (ad : Std.Array Std.U8 151#usize)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (associated : state.owner.associatedData = absBytes ad) :
    executeOwner reader ad erased raw state =
      (fun result => ok result) <$> PqxdhBoundaryRecordPrelude.ownerReceive reader ad raw state := by
  unfold executeOwner
  rw [prepared_exact, PqxdhOpenBridges.bindResult_ok]
  unfold PqxdhBoundaryRecordPrelude.ownerReceive RawCtxNativeFramePrelude.receive
  cases hprepared : prepared reader ad state.owner.expectedSender raw with
  | none => simp only [Option.map_none, simulateQ_pure, map_pure]
  | some value =>
    have execution := (prepared_exact reader ad state.owner.expectedSender raw).trans (congrArg RustM.ok hprepared)
    simp only [Option.map_some, Prepared.project]
    rw [prepared_loop reader ad state.owner.expectedSender raw value execution]
    simp only [associated, simulateQ_map, bind_pure_comp, Functor.map_map, RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose, PqxdhOpenContextBridge.map_ok]

variable {PeerMetadata : Type}

/-- Historical CE identity-AD281 routing retains the literal current raw-owner rejection result: no KDF/open callback, one raw attempt, and reinstallation of the same selected kernel. No AD151 is manufactured from identities. -/
noncomputable def executeServer (reader : Reader Message Root)
    (_erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Metadata PeerMetadata)) :=
  match RawCtxFrameDecoding.sender reader.model raw with
  | none => pure (ok (.None, { state with rawAttempts := state.rawAttempts + 1 }))
  | some kid =>
      match RawCtxServerRouting.peerAssociatedData state.server kid with
      | none => pure (ok (.None, { state with rawAttempts := state.rawAttempts + 1 }))
      | some _ad =>
          match state.server.peers kid with
          | none => pure (ok (.None, { state with rawAttempts := state.rawAttempts + 1 }))
          | some peer => pure (ok (.None,
              ⟨RawCtxServerRouting.putPeer state.server kid peer peer.kernel, state.rawAttempts + 1⟩))

/-- The retained historical Server routing equals its full raw-model computation on every input, including wrong-width rejection before KDF/open work. This is not the current extracted Server correspondence. -/
theorem executeServer_exact (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    executeServer reader erased raw state =
      (fun result => ok result) <$> PqxdhBoundaryRecordPrelude.serverReceive reader raw state := by
  unfold executeServer PqxdhBoundaryRecordPrelude.serverReceive
  cases routed : RawCtxFrameDecoding.sender reader.model raw with
  | none => simp only [map_pure]
  | some kid =>
    cases found : state.server.peers kid <;> simp only [RawCtxServerRouting.peerAssociatedData, found, Bind.bind, Option.bind, pure]
    · rfl
    · rename_i peer
      have rejected :
          (RawCtxWholeOwner.rawReceive (RawCtxFrameDecoding.decode reader.model) raw).run
            (⟨RawCtxServerRouting.selectedOwner kid
              (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer,
              state.rawAttempts⟩ : RawCtxWholeOwner.OwnerState PeerMetadata) =
            pure (RawCtxWholeOwner.publish
              ⟨RawCtxServerRouting.selectedOwner kid
                (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩
              (peer.kernel, .None)) := by
        cases empty : raw.isEmpty <;> cases decoded : RawCtxFrameDecoding.decode reader.model raw <;>
          simp [RawCtxWholeOwner.rawReceive, StateT.run, empty, decoded, RawCtxReceive.ValidFrame,
            RawCtxServerRouting.selectedOwner, RawCtxServerRouting.associatedBytes_length]
      rw [rejected]
      simp only [simulateQ_pure, RawCtxWholeOwner.publish]
      rfl

/-- Current Server execution takes AD151 from the metadata of the same selected peer, then runs the extracted owner prelude and receive loop without changing any routing or counter effect. -/
noncomputable def currentExecuteServer
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize) (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Metadata PeerMetadata)) :=
  match RawCtxFrameDecoding.sender reader.model raw with
  | none => pure (ok (.None, { state with rawAttempts := state.rawAttempts + 1 }))
  | some kid => match state.server.peers kid with
    | none => pure (ok (.None, { state with rawAttempts := state.rawAttempts + 1 }))
    | some peer => do
        let result ← executeOwner reader (sessionData peer.metadata) erased raw
          ⟨MldsaServerRouting.selected (fun metadata => absBytes (sessionData metadata)) kid peer, state.rawAttempts⟩
        pure ((fun result => (result.1,
          ⟨RawCtxServerRouting.putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)) <$> result)

/-- The current execution transcription equals the complete metadata-routed extracted prelude, including every optional result and full selected kernel/counter poststate. -/
theorem currentExecuteServer_exact
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize) (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    currentExecuteServer sessionData reader erased raw state =
      (fun result => ok result) <$> PqxdhBoundaryRecordPrelude.currentServerReceive sessionData reader raw state := by
  unfold currentExecuteServer PqxdhBoundaryRecordPrelude.currentServerReceive
  cases routed : RawCtxFrameDecoding.sender reader.model raw with
  | none => rfl
  | some kid =>
    simp only
    cases found : state.server.peers kid with
    | none => rfl
    | some peer =>
      simp only
      rw [executeOwner_exact reader (sessionData peer.metadata) erased raw
        ⟨MldsaServerRouting.selected (fun metadata => absBytes (sessionData metadata)) kid peer, state.rawAttempts⟩ rfl]
      simp only [bind_pure_comp, Functor.map_map, PqxdhOpenContextBridge.map_ok]

/-- The current receive execution uses the same selected metadata AD as the complete current Server handler, with no global AD, identity-derived hash or successful-opening premise. -/
theorem currentExecuteServer_source
    (sessionData : PeerMetadata → Std.Array Std.U8 151#usize) (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    currentExecuteServer sessionData reader erased raw state =
      (fun result => ok result) <$> MldsaServerRouting.receive
        (fun metadata => absBytes (sessionData metadata))
        (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) raw state := by
  rw [currentExecuteServer_exact, PqxdhBoundaryRecordPrelude.current_server_exact]

/-- Completed binding metadata supplies its stored full session AD to current execution; this representation theorem invents no registration, transcript digest or peer. -/
theorem completedExecuteServer_source (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata session.CompletedRegistrationBinding)
    (sender : Metadata → Std.U64) :
    currentExecuteServer (fun binding => binding.associated_data) reader erased raw state =
      (fun result => ok result) <$>
        (MldsaServerRouting.handler (fun binding => absBytes binding.associated_data) sender
          (RawCtxFrameDecoding.sender reader.model) (RawCtxFrameDecoding.decode reader.model) (.inr raw)).run state := by
  rw [currentExecuteServer_exact, PqxdhBoundaryRecordPrelude.completedServer_exact reader raw state sender]
  rfl

variable {Identity DhPair KemPair : Type}

/-- Established Beacon execution uses its stored associated data and full receive-loop transcription; other phases preserve their literal rejection result. -/
noncomputable def executeBeacon (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxBeaconLifecycle.State Identity DhPair KemPair)) :=
  match state.beacon.phase with
  | .established control ad kernel => do
      let result ← executeOwner reader ad erased raw (RawCtxBeaconLifecycle.selected state control ad kernel)
      pure ((fun result => (result.1, RawCtxBeaconLifecycle.reinstall state control ad result.2)) <$> result)
  | _ => pure (ok (RawCtxBeaconLifecycle.rejected (.inr raw) state))

/-- Every Beacon lifecycle phase agrees with the full native source operation, with no target-honesty or successful-opening premise. -/
theorem executeBeacon_exact (reader : Reader Message Root)
    (erased : Std.Array Std.U8 227#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    executeBeacon reader erased raw state =
      (fun result => ok result) <$> PqxdhBoundaryRecordPrelude.beaconReceive reader raw state := by
  unfold executeBeacon PqxdhBoundaryRecordPrelude.beaconReceive
  cases state.beacon.phase <;> try rfl
  rename_i control ad kernel
  simp only [executeOwner_exact reader ad erased raw (RawCtxBeaconLifecycle.selected state control ad kernel) rfl, bind_pure_comp, Functor.map_map, PqxdhOpenContextBridge.map_ok]

open PqxdhDeploymentNative
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A normal result wrapper preserves all native record work and its complete shared poststate. -/
theorem record_map_result {X Y : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (f : X → Y)
    (work : OracleComp RawCtxMixedOwner.NativeSpec X) (state : PqxdhRegistrationSchedule.State KemSK) :
    (record setup codec (f <$> work)).run state =
      (fun result => (f result.1, result.2)) <$> (record setup codec work).run state := by
  simp only [record_run, simulateQ_map, StateT.run_map, Functor.map_map]

private noncomputable def modelExecuteServer
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (raw : Pqxdh.Bytes) (state : RawCtxServerRouting.State Unit PqxdhTranscriptAd.AssociatedData) :
    OracleComp RawCtxMixedOwner.NativeSpec
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxServerRouting.State Unit PqxdhTranscriptAd.AssociatedData)) :=
  currentExecuteServer id reader erased raw state

private theorem modelExecuteServer_exact
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (raw : Pqxdh.Bytes) (state : RawCtxServerRouting.State Unit PqxdhTranscriptAd.AssociatedData) :
    modelExecuteServer reader erased raw state =
      (fun result => ok result) <$> PqxdhBoundaryRecordPrelude.currentServerReceive id reader raw state := by
  rw [modelExecuteServer, currentExecuteServer_exact]

/-- The Server receive transcription runs in the original shared primitive state and publishes its returned peer state and frame log. -/
noncomputable def executeServerRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhDeploymentNative.State KemSK)) := do
  let result ← (record setup codec (logged (modelExecuteServer reader erased raw (serverView state)))).run state.native
  pure ((fun output => (output.1, produce (serverTag (.inr raw)) result.1.2
    (withServer { state with native := result.2 } output.2))) <$> result.1.1)

/-- Full native interpretation preserves the source Server optional plaintext, all live owners and peers, shared hash cache and logs. -/
theorem executeServerRaw_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeServerRaw setup codec reader erased raw state =
      (fun result => ok result) <$> (PqxdhBoundaryRecordPrelude.serverRaw setup codec reader raw).run state := by
  unfold executeServerRaw PqxdhBoundaryRecordPrelude.serverRaw
  rw [modelExecuteServer_exact, logged_map]
  have mapped := record_map_result setup codec (Prod.map (fun result => ok result) id) (logged
    (PqxdhBoundaryRecordPrelude.currentServerReceive id reader raw (serverView state))) state.native
  simp only [StateT.run] at mapped ⊢
  rw [mapped]
  simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq, PqxdhOpenContextBridge.map_ok]

/-- The Beacon receive transcription uses the actual owner lookup and reinstalls the same complete live owner, raw counter and frame log. -/
noncomputable def executeBeaconRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhDeploymentNative.State KemSK)) :=
  match state.native.owners[index]? with
  | none => pure (ok (.None, state))
  | some owner => do
      let result ← (record setup codec (logged (executeBeacon reader erased raw
        ⟨owner.beacon, state.ownerRaw index⟩))).run state.native
      pure ((fun output => (output.1, produce (beaconTag index) result.1.2 { state with
        native := { result.2 with owners := result.2.owners.set index { owner with beacon := output.2.beacon } }
        ownerRaw := Function.update state.ownerRaw index output.2.rawAttempts })) <$> result.1.1)

/-- Missing-owner rejection and every Beacon phase retain the actual full native command result and state. -/
theorem executeBeaconRaw_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeBeaconRaw setup codec reader erased index raw state =
      (fun result => ok result) <$> (PqxdhBoundaryRecordPrelude.beaconRaw setup codec reader index raw).run state := by
  unfold executeBeaconRaw PqxdhBoundaryRecordPrelude.beaconRaw
  cases found : state.native.owners[index]? with
  | none => simp only [StateT.run, found, map_pure]
  | some owner =>
    simp only [StateT.run, found]
    rw [executeBeacon_exact, logged_map]
    have mapped := record_map_result setup codec (Prod.map (fun result => ok result) id)
      (logged (PqxdhBoundaryRecordPrelude.beaconReceive reader raw ⟨owner.beacon, state.ownerRaw index⟩)) state.native
    simp only [StateT.run] at mapped
    rw [mapped]
    simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq, PqxdhOpenContextBridge.map_ok]

/-- The frozen CE raw Server command is the receive execution transcription over extracted local steps with its normal-return wrapper. -/
theorem handler_serverRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (checks : PqxdhServerAuthExperiment.Checks) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeServerRaw setup codec reader erased raw state =
      (fun result => ok result) <$> (handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) serverSeed (.inr (.serverRaw raw))).run state := by
  rw [PqxdhBoundaryRecordPrelude.handler_serverRaw]
  exact executeServerRaw_exact setup codec reader erased raw state

/-- The frozen CE raw Beacon command uses the actual owner handle and receive execution transcription over extracted local steps. -/
theorem handler_beaconRaw (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 227#usize)
    (checks : PqxdhServerAuthExperiment.Checks) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeBeaconRaw setup codec reader erased index raw state =
      (fun result => ok result) <$> (handler setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) serverSeed (.inr (.beaconRaw index raw))).run state := by
  rw [PqxdhBoundaryRecordPrelude.handler_beaconRaw]
  exact executeBeaconRaw_exact setup codec reader erased index raw state

end BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.prepared_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.prepared_payload

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.prepared_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.prepared_loop

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeOwner_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeOwner_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeServer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeServer_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeBeacon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeBeacon_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.record_map_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.record_map_result

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeServerRaw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeServerRaw_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeBeaconRaw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.executeBeaconRaw_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.handler_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.handler_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.handler_beaconRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.handler_beaconRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.currentExecuteServer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.currentExecuteServer_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.currentExecuteServer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.currentExecuteServer_source

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.completedExecuteServer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution.completedExecuteServer_source
