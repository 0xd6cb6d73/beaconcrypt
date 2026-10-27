-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution

/-! Production send transcription composed from extracted begin, resume, getters and finish. The loop and public adapter remain RT. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRecordSend
open PqxdhRefinement RawCtxSourceSend

/-- Read the same extracted one-use capability getters that the source passes to its sealing executor. -/
def executeArguments (ready : SendSeal SealContext) : RustM SealInput := do
  let material ← SendSeal.impl.material ready
  let sequence ← SendSeal.impl.sequence ready
  let context ← SendSeal.impl.context ready
  ok ⟨material, sequence, context⟩

/-- The three actual extracted getter calls return exactly the immutable sealing capability arguments. -/
theorem executeArguments_exact (ready : SendSeal SealContext) :
    executeArguments ready = ok (arguments ready) := by
  rfl

/-- The source send driver executes the original admission and continuation, then the actual sealing program and extracted finish, retaining optional writer failure. -/
noncomputable def executeSend (kernel : ConcreteRatchetKernel) (context : SealContext) :
    OracleComp RawCtxMixedOwner.NativeSpec (RustM (ConcreteRatchetKernel × Option Encrypted)) :=
  RawCtxInterpretedOpening.bindResult (begin_send kernel context) fun start =>
    match start with
    | .SendExhausted entry _ => pure (ok (entry, none))
    | .SendKdfRequested pending =>
        RawCtxInterpretedOpening.bindResult (SendKdf.impl.request pending) fun request => do
          let response ← RawCtxMixedOwner.NativeSpec.query (.inl request)
          RawCtxInterpretedOpening.bindResult (pending.resume response) fun ready =>
            RawCtxInterpretedOpening.bindResult (executeArguments ready) fun input => do
              let ciphertext ← simulateQ RawCtxMixedOwner.sendLift
                (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input))
              pure (ready.finish (ciphertext.map (encrypted input)))

/-- The complete source send transcription agrees with the native program before any query interpretation, including all unsuccessful seal and writer replies. -/
theorem executeSend_exact (kernel : ConcreteRatchetKernel) (context : SealContext) :
    executeSend kernel context =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.sendAdapter
        (simulateQ adapter (send kernel context)) := by
  unfold executeSend
  rw [beginSend_exact, PqxdhOpenBridges.bindResult_ok]
  cases started : beginSend kernel context with
  | SendExhausted entry saved =>
    simp only [send, started, program, simulateQ_pure, map_pure]
  | SendKdfRequested pending =>
    simp only [send, started, program, adapter, RawCtxMixedOwner.sendAdapter, QueryImpl.compose, RawCtxSourceSeal.nativeAdapter, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, RawCtxMixedOwner.sendLift]
    simp only [executeArguments, SendKdf.impl.request, SendSeal.impl.material, SendSeal.impl.sequence, SendSeal.impl.context, bind_tc_ok, resumeSend_exact, PqxdhOpenBridges.bindResult_ok, SendSeal.finish_returns_interpreter_result, map_bind, bind_assoc, pure_bind, map_pure]
    rfl

/-- Whole-owner sending applies the source empty-input gate, original sender/target/AD context and full returned-kernel reinstallation. -/
noncomputable def executeOwner {Metadata : Type} (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    OracleComp RawCtxMixedOwner.NativeSpec (RustM (Option Encrypted × RawCtxWholeOwner.OwnerState Metadata)) :=
  if plaintext.isEmpty then pure (ok (none, state)) else do
    let result ← executeSend state.owner.kernel
      ⟨plaintext, state.owner.expectedSender, sender, state.owner.associatedData⟩
    pure ((fun result => (result.2, { state with owner := { state.owner with kernel := result.1 } })) <$> result)

/-- The native mixed owner send is exactly the source send transcription, with the target API handle separate from the encoded sender. -/
theorem executeOwner_exact {Metadata : Type} (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (decode : RawCtxReceive.FrameDecoder) :
    executeOwner sender plaintext state =
      (fun result => ok result) <$> (RawCtxMixedOwner.ownerImpl sender decode (.inl plaintext)).run state := by
  unfold executeOwner RawCtxMixedOwner.ownerImpl sendOwner StateT.run
  split
  · simp only [StateT.run, simulateQ_pure, map_pure]
  · rw [executeSend_exact]
    simp only [StateT.run, simulateQ_map, bind_pure_comp, Functor.map_map, PqxdhOpenContextBridge.map_ok]

/-- Server sending selects AD and the same mutable peer before running the source driver, then reinstalls its returned kernel even when the writer fails. -/
noncomputable def executeServer {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    OracleComp RawCtxMixedOwner.NativeSpec (RustM (Option Encrypted × RawCtxServerRouting.State Metadata PeerMetadata)) :=
  match RawCtxServerRouting.peerAssociatedData state.server kid with
  | none => pure (ok (none, state))
  | some ad =>
      let sender := senderId state.server.metadata
      match state.server.peers kid with
      | none => pure (ok (none, state))
      | some peer => do
          let result ← executeOwner sender plaintext
            ⟨RawCtxServerRouting.selectedOwner kid ad peer, state.rawAttempts⟩
          pure ((fun result => (result.1,
            ⟨RawCtxServerRouting.putPeer state.server kid peer result.2.owner.kernel,
              result.2.rawAttempts⟩)) <$> result)

/-- Server send transcription equals the native routed program with every optional result and complete peer map. -/
theorem executeServer_exact {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : RawCtxServerRouting.State Metadata PeerMetadata)
    (decode : RawCtxReceive.FrameDecoder) :
    executeServer senderId plaintext kid state =
      (fun result => ok result) <$> RawCtxServerMixed.sendServer senderId plaintext kid state := by
  unfold executeServer RawCtxServerMixed.sendServer RawCtxServerSend.sendServer
  cases found : state.server.peers kid <;> simp only [RawCtxServerRouting.peerAssociatedData, found, Bind.bind, Option.bind, pure]
  · simp only [PFunctor.FreeM.pure_eq_pure, simulateQ_pure, map_pure]
  · rename_i peer
    rw [executeOwner_exact _ _ _ decode]
    simp only [PFunctor.FreeM.bind_eq_bind, PFunctor.FreeM.pure_eq_pure, RawCtxMixedOwner.ownerImpl, StateT.run, RawCtxMixedOwner.sendAdapter, QueryImpl.simulateQ_compose, simulateQ_map, bind_pure_comp, Functor.map_map, PqxdhOpenContextBridge.map_ok]
    rfl

/-- Only an established Beacon sends, using the outer identity ID and the pinned control target independently. -/
noncomputable def executeBeacon {Identity DhPair KemPair : Type} (plaintext : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    OracleComp RawCtxMixedOwner.NativeSpec (RustM (Option Encrypted × RawCtxBeaconLifecycle.State Identity DhPair KemPair)) :=
  match state.beacon.phase with
  | .established control ad kernel => do
      let result ← executeOwner state.beacon.identityKeyId plaintext (RawCtxBeaconLifecycle.selected state control ad kernel)
      pure ((fun result => (result.1, RawCtxBeaconLifecycle.reinstall state control ad result.2)) <$> result)
  | _ => pure (ok (none, state))

/-- Established and rejected Beacon sends retain exactly the native full state and optional reply. -/
theorem executeBeacon_exact {Identity DhPair KemPair : Type} (plaintext : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (decode : RawCtxReceive.FrameDecoder) :
    executeBeacon plaintext state =
      (fun result => ok result) <$> (RawCtxBeaconLifecycle.beaconImpl decode (.inl plaintext)).run state := by
  unfold executeBeacon RawCtxBeaconLifecycle.beaconImpl StateT.run
  cases state.beacon.phase <;> try rfl
  rename_i control ad kernel
  simp only [executeOwner_exact _ _ _ decode, bind_pure_comp, Functor.map_map, PqxdhOpenContextBridge.map_ok]

open PqxdhDeploymentNative
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The Server send transcription uses the real shared record interpreter and logs every attempted writer publication. -/
noncomputable def executeServerSend (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (kid : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (Option Encrypted × PqxdhDeploymentNative.State KemSK)) := do
  let result ← (record setup codec (logged (executeServer (senderId state) plaintext kid (serverView state)))).run state.native
  pure ((fun output => (output.1, produce (serverTag (.inl (plaintext, kid))) result.1.2
    (withServer { state with native := result.2 } output.2))) <$> result.1.1)

/-- Complete CE Server send equality retains the shared hash cache, primitive effects, optional writer result and advanced ratchet. -/
theorem executeServerSend_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (kid : Std.U64) (plaintext : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeServerSend setup codec kid plaintext state =
      (fun result => ok result) <$> (serverStep setup codec route (.inl (plaintext, kid))).run state := by
  unfold executeServerSend serverStep
  rw [executeServer_exact _ _ _ _ codec.frameRead, logged_map]
  have mapped := PqxdhBoundaryRecordExecution.record_map_result setup codec (Prod.map (fun result => ok result) id)
    (logged (RawCtxServerMixed.sendServer (senderId state) plaintext kid (serverView state))) state.native
  simp only [StateT.run] at mapped ⊢
  rw [mapped]
  simp only [RawCtxServerMixed.serverImpl, bind_pure_comp, Functor.map_map, Prod.map, id_eq, PqxdhOpenContextBridge.map_ok]
  rfl

/-- The Beacon send transcription runs on the looked-up live owner, preserves the shared primitive cache and publishes the returned owner and frame log. -/
noncomputable def executeBeaconSend (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (index : Nat) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (Option Encrypted × PqxdhDeploymentNative.State KemSK)) :=
  match state.native.owners[index]? with
  | none => pure (ok (none, state))
  | some owner => do
      let result ← (record setup codec (logged (executeBeacon plaintext
        ⟨owner.beacon, state.ownerRaw index⟩))).run state.native
      pure ((fun output => (output.1, produce (beaconTag index) result.1.2 { state with
        native := { result.2 with owners := result.2.owners.set index { owner with beacon := output.2.beacon } }
        ownerRaw := Function.update state.ownerRaw index output.2.rawAttempts })) <$> result.1.1)

/-- Missing owner, inactive phase and active Beacon sends all agree with the same complete native command. -/
theorem executeBeaconSend_exact (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (index : Nat) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    executeBeaconSend setup codec index plaintext state =
      (fun result => ok result) <$> (beaconStep setup codec index (.inl plaintext)).run state := by
  unfold executeBeaconSend beaconStep
  cases found : state.native.owners[index]? with
  | none => simp only [StateT.run, found, absent, map_pure]
  | some owner =>
    simp only [StateT.run, found]
    rw [executeBeacon_exact _ _ codec.frameRead, logged_map]
    have mapped := PqxdhBoundaryRecordExecution.record_map_result setup codec (Prod.map (fun result => ok result) id)
      (logged ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead (.inl plaintext)).run
        ⟨owner.beacon, state.ownerRaw index⟩)) state.native
    simp only [StateT.run] at mapped ⊢
    rw [mapped]
    simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq, PqxdhOpenContextBridge.map_ok]

/-- The frozen CE Server-send command is the same source driver under the original native interpreter. -/
theorem handler_serverSend (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (kid : Std.U64) (plaintext : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeServerSend setup codec kid plaintext state =
      (fun result => ok result) <$> (handler setup codec checks route serverSeed (.inr (.serverSend kid plaintext))).run state :=
  executeServerSend_exact setup codec route kid plaintext state

/-- The frozen CE Beacon-send command keeps the same owner lookup, publication and original actual reply. -/
theorem handler_beaconSend (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (plaintext : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeBeaconSend setup codec index plaintext state =
      (fun result => ok result) <$> (handler setup codec checks route serverSeed (.inr (.beaconSend index plaintext))).run state :=
  executeBeaconSend_exact setup codec index plaintext state

/-- Whole-owner transcription charges at most one KDF, seal, hash and writer, and no opening call, including every failed send. -/
theorem executeOwner_bounds {Metadata : Type} (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (kind : RawCtxMixedOwner.CallKind) :
    (executeOwner sender plaintext state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind) (RawCtxMixedOwner.sendCost kind) := by
  rw [executeOwner_exact _ _ _ (fun _ => none), isQueryBoundP_map_iff]
  exact RawCtxMixedOwner.send_bounds sender (fun _ => none) plaintext state kind

/-- Server routing adds no primitive calls to the four separate one-send caps. -/
theorem executeServer_bounds {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : RawCtxServerRouting.State Metadata PeerMetadata)
    (kind : RawCtxMixedOwner.CallKind) :
    (executeServer senderId plaintext kid state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind) (RawCtxMixedOwner.sendCost kind) := by
  simpa only [executeServer_exact _ _ _ _ (fun _ => none), isQueryBoundP_map_iff] using
    RawCtxServerMixed.send_bound senderId plaintext kid state kind

/-- Beacon lifecycle selection retains the same separate source primitive caps, including inactive rejection. -/
theorem executeBeacon_bounds {Identity DhPair KemPair : Type} (plaintext : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) (kind : RawCtxMixedOwner.CallKind) :
    (executeBeacon plaintext state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind) (RawCtxMixedOwner.sendCost kind) := by
  simpa only [executeBeacon_exact _ _ (fun _ => none), isQueryBoundP_map_iff] using
    RawCtxBeaconLifecycle.step_bound (fun _ => none) (.inl plaintext) state kind

/-- Every completed active source send advances once and retains all receive state even when its optional sealing or writer reply is absent. -/
theorem executeOwner_active {Metadata PrimitiveState : Type} {κ : Type} {base : OracleSpec κ}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (primitive finalPrimitive : PrimitiveState) (result : Option Encrypted × RawCtxWholeOwner.OwnerState Metadata)
    (nonempty : plaintext.isEmpty = false)
    (notExhausted : state.owner.kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (supported : (ok result, finalPrimitive) ∈ support ((simulateQ impl (executeOwner sender plaintext state)).run primitive)) :
    result.2.owner.kernel.refined.control.send_sequence.val = state.owner.kernel.refined.control.send_sequence.val + 1 ∧
      result.2.owner.kernel.refined.control.receive_sequence = state.owner.kernel.refined.control.receive_sequence ∧
      result.2.owner.kernel.refined.control.receive_cache = state.owner.kernel.refined.control.receive_cache ∧
      result.2.owner.kernel.refined.receive_chain = state.owner.kernel.refined.receive_chain ∧
      result.2.owner.kernel.refined.receive_slots = state.owner.kernel.refined.receive_slots := by
  rw [executeOwner_exact _ _ _ (fun _ => none)] at supported
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image, Prod.mk.injEq, RustM.ok.injEq] at supported
  obtain ⟨⟨actual, final⟩, stepped, rfl, rfl⟩ := supported
  apply sendGame_active_state (impl ∘ₛ RawCtxMixedOwner.sendAdapter) sender plaintext state primitive nonempty notExhausted (actual, final)
  simpa only [sendGame, RawCtxMixedOwner.ownerImpl, StateT.run, QueryImpl.simulateQ_compose] using stepped

end BeaconcryptCore.Computational.PqxdhBoundaryRecordSend

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeArguments_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeArguments_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeSend_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeSend_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServer_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeacon_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeacon_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServerSend_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServerSend_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeaconSend_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeaconSend_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.handler_serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.handler_serverSend

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.handler_beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.handler_beaconSend

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeServer_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeacon_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeBeacon_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRecordSend.executeOwner_active
