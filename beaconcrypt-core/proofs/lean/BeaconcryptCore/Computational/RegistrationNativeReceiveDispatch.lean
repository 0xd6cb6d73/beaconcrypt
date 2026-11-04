-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReceiveOwner

/-! The original native Server/Beacon record dispatch contexts use the extracted receive loop on the same typed Wire parser,281-byte AD arrays, full peer/owner states and instrumented primitive service. Every other record/administrative operation remains the original callback. Source correspondence of the outer parser and public Rust wrappers remains separate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

/-- Missing routes/peers retain the original raw-attempt increment; selected peers supply their actual stored AD array. -/
noncomputable def serverRaw (setup : Setup base KemSK) (wire : Wire)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) (bytes : Pqxdh.Bytes) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxWholeOwner.Decrypted) := fun state =>
  match state.server with
  | none => pure (none, state)
  | some server =>
      let denied := { state with server := some { server with records :=
        { server.records with rawAttempts := server.records.rawAttempts + 1 } } }
      match route bytes with
      | none => pure (none, denied)
      | some kid => match server.records.server.peers kid with
        | none => pure (none, denied)
        | some peer => do
            let opened ← (RegistrationNativeReceiveOwner.raw setup wire erased peer.metadata bytes
              ⟨MldsaServerRouting.selected PqxdhRefinement.absBytes kid peer, server.records.rawAttempts⟩).run state.primitive
            pure (opened.1.1, { state with
              server := some { server with records :=
                ⟨RawCtxServerRouting.putPeer server.records.server kid peer opened.1.2.owner.kernel,
                  opened.1.2.rawAttempts⟩ }
              primitive := opened.2 })

/-- The original native routing callback exposes exactly its own raw-receive body. -/
theorem routing_raw (wire : Wire) (route : RawCtxServerRouting.SenderDecoder) (bytes : Pqxdh.Bytes)
    (server : PqxdhRecordLiftWorld.Server) :
    (MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _ => server.sender)
      route (ledgerCodec wire).frameRead (.inr bytes)).run server.records =
      MldsaServerRouting.receive PqxdhRefinement.absBytes route (ledgerCodec wire).frameRead bytes server.records := rfl

/-- The source-selected Server raw callback preserves its entire original peer map, counters, output and primitive state. -/
theorem server_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) (bytes : Pqxdh.Bytes) :
    serverRaw (n := n) setup wire erased route bytes =
      PqxdhRecordLiftWorld.serverStep setup (ledgerCodec wire) route (.inr bytes) := by
  funext before
  cases present : before.server with
  | none => simp only [serverRaw, PqxdhRecordLiftWorld.serverStep, present]
  | some server =>
      cases routed : route bytes with
      | none =>
          simp only [serverRaw, PqxdhRecordLiftWorld.serverStep, present,
            routing_raw, MldsaServerRouting.receive, routed,
            PqxdhDeploymentNative.logged_pure, simulateQ_pure, StateT.run_pure,
            PqxdhRecordLiftWorld.produce, List.map_nil, List.append_nil, pure_bind]
      | some kid =>
          cases found : server.records.server.peers kid with
          | none =>
              simp only [serverRaw, PqxdhRecordLiftWorld.serverStep, present,
                routing_raw, MldsaServerRouting.receive, routed, found,
                PqxdhDeploymentNative.logged_pure, simulateQ_pure, StateT.run_pure,
                PqxdhRecordLiftWorld.produce, List.map_nil, List.append_nil, pure_bind]
          | some peer =>
              simp only [serverRaw, PqxdhRecordLiftWorld.serverStep, present,
                routing_raw, MldsaServerRouting.receive, routed, found,
                RawCtxMixedOwner.ownerImpl, bind_pure_comp,
                PqxdhDeploymentNative.logged_map, simulateQ_map, StateT.run_map, Functor.map_map]
              rw [← RegistrationNativeReceiveOwner.raw_logged_native setup wire length erased
                peer.metadata bytes
                ⟨MldsaServerRouting.selected PqxdhRefinement.absBytes kid peer, server.records.rawAttempts⟩
                rfl before.primitive]
              simp only [Functor.map_map, Prod.map, PqxdhRecordLiftWorld.produce,
                List.map_nil, List.append_nil, id_eq]

/-- Absent and inactive owners retain their original distinct counter behavior; established owners provide the actual stored pin and AD. -/
noncomputable def beaconRaw (setup : Setup base KemSK) (wire : Wire)
    (erased : Array Std.U8 357#usize) (index : Nat) (bytes : Pqxdh.Bytes) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxWholeOwner.Decrypted) := fun state =>
  match state.owners[index]? with
  | none => pure (none, state)
  | some (.inactive phase) => pure (none, { state with
      owners := state.owners.set index (.inactive phase)
      ownerRaw := Function.update state.ownerRaw index (state.ownerRaw index + 1) })
  | some (.established shell kernel) => do
      let opened ← (RegistrationNativeReceiveOwner.raw setup wire erased shell.associatedData bytes
        ⟨⟨kernel, shell.control.server_binding.identity_key_id,
          PqxdhRefinement.absBytes shell.associatedData, ()⟩, state.ownerRaw index⟩).run state.primitive
      pure (opened.1.1, { state with
        owners := state.owners.set index (.established shell opened.1.2.owner.kernel)
        ownerRaw := Function.update state.ownerRaw index opened.1.2.rawAttempts
        primitive := opened.2 })

/-- The original inactive callback returns the actual rejection and increments only its existing raw-attempt counter. -/
theorem beacon_inactive (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (phase : PqxdhRecordLiftInterface.InactivePhase) (attempts : Nat) :
    (PqxdhRecordLiftBeacon.handler decode (.inr bytes)).run ⟨.inactive phase, attempts⟩ =
      pure (none, (⟨.inactive phase, attempts + 1⟩ : PqxdhRecordLiftBeacon.State)) := rfl

/-- The existing established callback exposes the same complete owner and literal optional raw reply before its native shell is reinstalled. -/
theorem beacon_established (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (shell : PqxdhRecordLiftInterface.BeaconShell) (kernel : ratchet.concrete.ConcreteRatchetKernel) (attempts : Nat) :
    (PqxdhRecordLiftBeacon.handler decode (.inr bytes)).run ⟨.established shell kernel, attempts⟩ =
      (fun result => (result.1,
        (⟨.established shell result.2.owner.kernel, result.2.rawAttempts⟩ : PqxdhRecordLiftBeacon.State))) <$>
        simulateQ RawCtxMixedOwner.receiveAdapter
          ((RawCtxWholeOwner.rawReceive decode bytes).run
            (⟨⟨kernel, shell.control.server_binding.identity_key_id,
              PqxdhRefinement.absBytes shell.associatedData, ()⟩, attempts⟩ : RawCtxWholeOwner.OwnerState Unit)) := by
  simp only [PqxdhRecordLiftBeacon.handler, StateT.run, RawCtxMixedOwner.ownerImpl, bind_pure_comp]
  rfl

/-- The source-selected Beacon raw callback retains its actual lifecycle shell, raw counter and complete primitive state. -/
theorem beacon_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (index : Nat) (bytes : Pqxdh.Bytes) :
    beaconRaw (n := n) setup wire erased index bytes =
      PqxdhRecordLiftWorld.beaconStep setup (ledgerCodec wire) index (.inr bytes) := by
  funext before
  cases found : before.owners[index]? with
  | none => simp only [beaconRaw, PqxdhRecordLiftWorld.beaconStep, found, PqxdhDeploymentNative.absent]
  | some phase =>
      cases phase with
      | inactive phase =>
          simp only [beaconRaw, PqxdhRecordLiftWorld.beaconStep, found, beacon_inactive,
            PqxdhDeploymentNative.logged_pure, simulateQ_pure, StateT.run_pure, pure_bind,
            PqxdhRecordLiftWorld.produce, List.map_nil, List.append_nil]
      | established shell kernel =>
          simp only [beaconRaw, PqxdhRecordLiftWorld.beaconStep, found, beacon_established,
            PqxdhDeploymentNative.logged_map, simulateQ_map, StateT.run_map,
            bind_pure_comp, Functor.map_map]
          rw [← RegistrationNativeReceiveOwner.raw_logged_native setup wire length erased
            shell.associatedData bytes
            (⟨⟨kernel, shell.control.server_binding.identity_key_id,
              PqxdhRefinement.absBytes shell.associatedData, ()⟩, before.ownerRaw index⟩ :
                RawCtxWholeOwner.OwnerState Unit) rfl before.primitive]
          simp only [Functor.map_map, Prod.map, PqxdhRecordLiftWorld.produce,
            List.map_nil, List.append_nil, id_eq]

/-- Only raw receive callbacks expand the extracted source loop; sends and all administrative services retain their original implementation. -/
noncomputable def handler (setup : Setup base KemSK) (wire : Wire)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inr (.inr (.inl (.inr bytes))) => serverRaw setup wire erased route bytes
  | .inr (.inr (.inr (index, .inr bytes))) => beaconRaw setup wire erased index bytes
  | query => PqxdhRecordLiftWorld.handler setup (ledgerCodec wire) route query

/-- This equality is on complete callbacks, with one shared World through every adaptive continuation. -/
theorem handler_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) :
    handler (n := n) setup wire erased route = PqxdhRecordLiftWorld.handler setup (ledgerCodec wire) route := by
  funext query
  rcases query with created | (effect | (server | ⟨index, beacon⟩))
  · rfl
  · rfl
  · cases server with
    | inl input => rfl
    | inr bytes => exact server_native setup wire length erased route bytes
  · cases beacon with
    | inl input => rfl
    | inr bytes => exact beacon_native setup wire length erased index bytes

/-- The original public transport refusal remains before the source-selected World callback. -/
noncomputable def guarded (setup : Setup base KemSK) (wire : Wire)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query state => match CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell state) with
  | some reply => pure (reply, state)
  | none => (handler setup wire erased route query).run state

/-- The source-selected guarded World equals the exact original admitted World, including every transport refusal. -/
theorem guarded_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) :
    guarded (n := n) setup wire erased route = CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route := by
  funext query state
  unfold guarded CborRecordWorldSimulation.guarded
  rw [handler_native setup wire length erased route]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.routing_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.routing_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.server_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_inactive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_established

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.beacon_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.handler_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.guarded_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch.guarded_native
