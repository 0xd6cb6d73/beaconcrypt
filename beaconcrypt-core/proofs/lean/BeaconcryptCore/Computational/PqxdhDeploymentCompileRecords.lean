-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompile

/-! Record commands of the CE-3 trial (items b and c of the compile lemma). A Server record command reads exactly one peer: its identity, kernel and the Server identity enter only through the 281-byte associated data and the selected kernel, and the Server key ID is the only metadata read. A Beacon record command reads exactly the outer key ID, the established control's expected sender, the stored associated data, the kernel and the raw-attempt counter; it never reads the identity seed, the pinned Server identity or any private Phase 1 field. Hence a local copy that agrees on these values has the same reply and the same returned kernel and counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentCompile (Kernel Identity serverTarget)
open PqxdhDeploymentRecordCache (localPrimitives)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The Server record core on one selected peer: the source send or raw receive of the whole owner built from the peer's kernel, its key ID, the associated data and the counter. -/
noncomputable def serverCore (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (kid : Std.U64)
    (ad : Pqxdh.Bytes) (kernel : Kernel) (raw : Nat) :
    (query : RawCtxServerMixed.SourceSpec.Domain) →
      OracleComp RawCtxMixedOwner.NativeSpec (RawCtxServerMixed.SourceSpec.Range query × (Kernel × Nat))
  | .inl (plaintext, _) => (fun result => (result.1, (result.2.owner.kernel, result.2.rawAttempts))) <$>
      simulateQ RawCtxMixedOwner.sendLift (simulateQ RawCtxSourceSeal.nativeAdapter
        ((RawCtxSourceSend.sendOwner sender plaintext).run ⟨⟨kernel, kid, ad, ()⟩, raw⟩))
  | .inr bytes => (fun result => (result.1, (result.2.owner.kernel, result.2.rawAttempts))) <$>
      simulateQ RawCtxMixedOwner.receiveAdapter ((RawCtxWholeOwner.rawReceive decode bytes).run ⟨⟨kernel, kid, ad, ()⟩, raw⟩)

/-- The rejection reply of a Server record command. -/
def serverReject : (query : RawCtxServerMixed.SourceSpec.Domain) → RawCtxServerMixed.SourceSpec.Range query
  | .inl _ => none
  | .inr _ => .None

/-- A rejected send leaves the counter; a rejected raw receive counts one attempt. -/
def rejectCount : RawCtxServerMixed.SourceSpec.Domain → Nat → Nat
  | .inl _, raw => raw
  | .inr _, raw => raw + 1

/-- A Server record command on an installed addressed peer is the record core on that peer, followed by publication of the returned kernel at the same key ID. -/
theorem serverImpl_peer (senderId : Unit → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State Unit Unit) (kid : Std.U64) (peer : RawCtxServerRouting.Peer Unit)
    (target : serverTarget route query = some kid) (found : state.server.peers kid = some peer) :
    (RawCtxServerMixed.serverImpl senderId route decode query).run state =
      (fun result => (result.1, (⟨RawCtxServerRouting.putPeer state.server kid peer result.2.1, result.2.2⟩ :
        RawCtxServerRouting.State Unit Unit))) <$>
        serverCore (senderId ()) decode kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity)
          peer.kernel state.rawAttempts query := by
  rcases query with ⟨plaintext, sent⟩ | bytes
  · simp only [serverTarget, Option.some.injEq] at target
    subst target
    simp only [StateT.run, RawCtxServerMixed.serverImpl, RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer,
      RawCtxServerRouting.peerAssociatedData, found, serverCore, RawCtxServerRouting.selectedOwner,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Functor.map_map, bind_pure_comp, simulateQ_map]
  · simp only [serverTarget] at target
    simp only [StateT.run, RawCtxServerMixed.serverImpl, RawCtxServerMixed.rawServer, target,
      RawCtxServerRouting.peerAssociatedData, found, serverCore, RawCtxServerRouting.selectedOwner,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Functor.map_map, bind_pure_comp]

/-- A Server record command whose addressed peer is absent, or whose raw bytes have no header route, is rejected before any primitive call; only a raw attempt is counted. -/
theorem serverImpl_absent (senderId : Unit → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State Unit Unit)
    (absent : ∀ kid, serverTarget route query = some kid → state.server.peers kid = none) :
    (RawCtxServerMixed.serverImpl senderId route decode query).run state =
      pure (serverReject query, ⟨state.server, rejectCount query state.rawAttempts⟩) := by
  rcases query with ⟨plaintext, kid⟩ | bytes
  · have missing := absent kid rfl
    simp only [StateT.run, RawCtxServerMixed.serverImpl, RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer,
      RawCtxServerRouting.peerAssociatedData, missing, Option.bind_eq_bind, Option.bind_none, simulateQ_pure,
      serverReject, rejectCount]
  · cases target : route bytes with
    | none => simp only [StateT.run, RawCtxServerMixed.serverImpl, RawCtxServerMixed.rawServer, target, serverReject,
        rejectCount]
    | some kid =>
        have missing := absent kid (by simpa only [serverTarget] using target)
        simp only [StateT.run, RawCtxServerMixed.serverImpl, RawCtxServerMixed.rawServer, target,
          RawCtxServerRouting.peerAssociatedData, missing, Option.bind_eq_bind, Option.bind_none, serverReject,
          rejectCount]

/-- The Beacon record core on an established owner: the whole-owner send or raw receive under the outer key ID, with the control's expected sender, the stored associated data, the kernel and the counter. -/
noncomputable def beaconCore (sender expected : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (associatedData : Std.Array Std.U8 281#usize) (kernel : Kernel) (raw : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) :
    OracleComp RawCtxMixedOwner.NativeSpec (RawCtxMixedOwner.SourceSpec.Range query × (Kernel × Nat)) :=
  (fun result => (result.1, (result.2.owner.kernel, result.2.rawAttempts))) <$>
    (RawCtxMixedOwner.ownerImpl sender decode query).run
      ⟨⟨kernel, expected, PqxdhRefinement.absBytes associatedData, ()⟩, raw⟩

/-- An established owner's record command is the Beacon record core; only the kernel and counter are reinstalled. It reads no identity, pinned Server identity or private Phase 1 field. -/
theorem beaconImpl_established {I D K : Type} (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : RawCtxBeaconLifecycle.State I D K)
    (control : beaconcrypt_core.pqxdh.BeaconEstablished) (associatedData : Std.Array Std.U8 281#usize)
    (kernel : Kernel) (phase : state.beacon.phase = .established control associatedData kernel) :
    (RawCtxBeaconLifecycle.beaconImpl decode query).run state =
      (fun result => (result.1, (⟨{ state.beacon with phase := .established control associatedData result.2.1 },
        result.2.2⟩ : RawCtxBeaconLifecycle.State I D K))) <$>
        beaconCore state.beacon.identityKeyId control.server_binding.identity_key_id decode associatedData kernel
          state.rawAttempts query := by
  rw [RawCtxBeaconLifecycle.established decode query state control associatedData kernel phase]
  simp only [beaconCore, Functor.map_map, bind_pure_comp]
  rfl

/-- The source14 Server reveal returns the installed kernel and changes nothing. -/
theorem reveal_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (kid : Std.U64) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (PqxdhDeploymentCompile.revealQuery kid)).run native =
      pure ((native.shared.2.server.server.peers kid).map RawCtxServerRouting.Peer.kernel, native) := by
  simp only [PqxdhDeploymentCompile.revealQuery, simulateQ_spec_query, PqxdhRegistrationJointRevealSchedule.native,
    PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.onShared_run, PqxdhServerAuthNative.localState,
    revealKernel, map_pure]

/-- The source14 established-kernel read returns the current established kernel of the addressed owner and changes nothing. -/
theorem kernel_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (PqxdhDeploymentCompile.kernelQuery index)).run native =
      pure ((native.owners[index]?).bind fun owner => PqxdhDeploymentCompile.phaseKernel owner.beacon.phase, native) := by
  simp only [PqxdhDeploymentCompile.kernelQuery, simulateQ_map, simulateQ_spec_query,
    PqxdhRegistrationJointRevealSchedule.native, StateT.run_map]
  change (fun result => _) <$> (pure (PqxdhRegistrationJointLiveRead.nativeStep (index, .kernel) native) : ProbComp _) = _
  simp only [map_pure, PqxdhRegistrationJointLiveRead.nativeStep]
  cases found : native.owners[index]? with
  | none => rfl
  | some owner =>
      cases phase : owner.beacon.phase <;>
        simp [PqxdhRegistrationJointLiveRead.value, PqxdhRegistrationJointLiveRead.localValue, phase,
          PqxdhDeploymentCompile.phaseKernel]

/-- Mapping a record program maps its result and keeps the same native poststate. -/
theorem record_map {Result Next : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (f : Result → Next) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (native : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhDeploymentNative.record setup codec (f <$> work)).run native =
      Prod.map f id <$> (PqxdhDeploymentNative.record setup codec work).run native := by
  simp only [PqxdhDeploymentNative.record_run, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- A pure record program changes nothing. -/
theorem record_pure {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (value : Result) (native : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhDeploymentNative.record setup codec (pure value)).run native = pure (value, native) := by
  simp only [PqxdhDeploymentNative.record_run, simulateQ_pure, StateT.run_pure, map_pure]

/-- The native Server record command as a mapped record program. -/
theorem serverStep_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.serverStep setup codec route query).run state =
      (fun result => (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) result.1.2
        (PqxdhDeploymentNative.withServer { state with native := result.2 } result.1.1.2))) <$>
        (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
          ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId state) route codec.frameRead query).run
            (PqxdhDeploymentNative.serverView state)))).run state.native := by
  simp only [PqxdhDeploymentNative.serverStep, StateT.run, bind_pure_comp]

/-- An unrouted compiled Server record command runs on the empty local Server and keeps only the counter. -/
theorem serverLocal_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (copies : PqxdhDeploymentCompile.Local) (target : serverTarget route query = none) :
    (PqxdhDeploymentCompile.serverLocal setup codec route query).run copies =
      (fun result => (result.1.1, ({ copies with serverRaw := result.1.2.rawAttempts } : PqxdhDeploymentCompile.Local).produce
        (PqxdhDeploymentNative.serverTag query) result.2)) <$>
        simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
          ((RawCtxServerMixed.serverImpl (fun _ => setup.serverKeyId) route codec.frameRead query).run
            (PqxdhDeploymentCompile.localServer codec copies.log 0#u64 none copies.serverRaw))) := by
  simp only [PqxdhDeploymentCompile.serverLocal, StateT.run, target, bind_pure_comp]

/-- A routed compiled Server record command obtains the addressed kernel, runs on the local Server and keeps the returned kernel and counter. -/
theorem serverLocal_some (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (copies : PqxdhDeploymentCompile.Local) (kid : Std.U64) (target : serverTarget route query = some kid) :
    (PqxdhDeploymentCompile.serverLocal setup codec route query).run copies =
      PqxdhDeploymentCompile.peerKernel copies kid >>= fun kernel =>
        (fun result => (result.1.1, ({ copies with
          peers := Function.update copies.peers kid ((result.1.2.server.peers kid).map RawCtxServerRouting.Peer.kernel)
          serverRaw := result.1.2.rawAttempts } : PqxdhDeploymentCompile.Local).produce
            (PqxdhDeploymentNative.serverTag query) result.2)) <$>
          simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
            ((RawCtxServerMixed.serverImpl (fun _ => setup.serverKeyId) route codec.frameRead query).run
              (PqxdhDeploymentCompile.localServer codec copies.log kid kernel copies.serverRaw))) := by
  simp only [PqxdhDeploymentCompile.serverLocal, StateT.run, target, bind_pure_comp]

/-- Merging a local kernel into a peer keeps the peer identity. -/
theorem mergePeer_identity (kernel : Option Kernel) (peer : RawCtxServerRouting.Peer Unit) :
    (PqxdhDeploymentCompile.mergePeer kernel peer).identity = peer.identity := by
  cases kernel <;> rfl

/-- The kernel of a merged peer is the local kernel if one exists. -/
theorem mergePeer_kernel (kernel : Option Kernel) (peer : RawCtxServerRouting.Peer Unit) :
    (PqxdhDeploymentCompile.mergePeer kernel peer).kernel = kernel.getD peer.kernel := by
  cases kernel <;> rfl

/-- Merging commutes with appending produced frames. -/
theorem merge_produce (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (tag : PqxdhDeploymentInterface.FrameTag) (frames : List PqxdhDeploymentNative.Frame) :
    PqxdhDeploymentCompile.merge (copies.produce tag frames) native =
      PqxdhDeploymentNative.produce tag frames (PqxdhDeploymentCompile.merge copies native) := rfl

/-- Merging after a cache update, a new local kernel at an installed peer and its produced frames is the native publication of that kernel at the same peer with the same frames. -/
theorem merge_put (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (kid : Std.U64) (peer : RawCtxServerRouting.Peer Unit) (kernel : Kernel) (raw : Nat)
    (cache : CtxRomAuth.CtxRO.QueryCache) (tag : PqxdhDeploymentInterface.FrameTag)
    (frames : List PqxdhDeploymentNative.Frame) (found : native.shared.2.server.server.peers kid = some peer) :
    PqxdhDeploymentCompile.merge
        (({ copies with peers := Function.update copies.peers kid (some kernel), serverRaw := raw } :
          PqxdhDeploymentCompile.Local).produce tag frames)
        (PqxdhDeploymentRecordCache.setCtx native cache) =
      PqxdhDeploymentNative.produce tag frames (PqxdhDeploymentNative.withServer
        { PqxdhDeploymentCompile.merge copies native with
          native := PqxdhDeploymentRecordCache.setCtx (PqxdhDeploymentCompile.merge copies native).native cache }
        ⟨RawCtxServerRouting.putPeer (PqxdhDeploymentCompile.merge copies native).native.shared.2.server.server kid
          (PqxdhDeploymentCompile.mergePeer (copies.peers kid) peer) kernel, raw⟩) := by
  have peers : (fun other => (native.shared.2.server.server.peers other).map
      (PqxdhDeploymentCompile.mergePeer (Function.update copies.peers kid (some kernel) other))) =
      Function.update (fun other => (native.shared.2.server.server.peers other).map
        (PqxdhDeploymentCompile.mergePeer (copies.peers other)))
        kid (some { PqxdhDeploymentCompile.mergePeer (copies.peers kid) peer with kernel := kernel }) := by
    funext other
    by_cases same : other = kid
    · subst same
      cases copies.peers other <;> simp [found, PqxdhDeploymentCompile.mergePeer]
    · simp only [Function.update_of_ne same]
  simp only [PqxdhDeploymentCompile.merge, PqxdhDeploymentNative.withServer, PqxdhDeploymentRecordCache.setCtx,
    RawCtxServerRouting.putPeer, peers, PqxdhDeploymentCompile.Local.produce, PqxdhDeploymentNative.produce]

/-- Server record commands (item b of the compile lemma): when the Server key ID is the public one, every locally copied peer is installed, and every installed peer is publicly reconstructible, the compiled command run on the source14 state has, after merging, exactly the native command's reply and deployment poststate. -/
theorem server_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (query : RawCtxServerMixed.SourceSpec.Domain) (copies : PqxdhDeploymentCompile.Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (installed : ∀ kid current, copies.peers kid = some current → native.shared.2.server.server.peers kid ≠ none)
    (visible : ∀ kid peer, native.shared.2.server.server.peers kid = some peer →
      PqxdhDeploymentCompile.peerView codec copies.log kid = some (native.shared.2.server.server.identity, peer.identity)) :
    (fun result => (result.1.1, PqxdhDeploymentCompile.merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
        ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies)).run native =
      (PqxdhDeploymentNative.serverStep setup codec route query).run (PqxdhDeploymentCompile.merge copies native) := by
  rw [serverStep_run]
  cases target : serverTarget route query with
  | none =>
      rw [serverLocal_none setup codec route query copies target,
        serverImpl_absent (fun _ => setup.serverKeyId) route codec.frameRead query _
          (fun kid found => by simp only [target, reduceCtorEq] at found),
        serverImpl_absent _ route codec.frameRead query _ (fun kid found => by simp only [target, reduceCtorEq] at found),
        PqxdhDeploymentNative.logged_pure, PqxdhDeploymentNative.logged_pure, record_pure]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | some kid =>
      rw [serverLocal_some setup codec route query copies kid target]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map, map_bind]
      cases found : native.shared.2.server.server.peers kid with
      | none =>
          have noCopy : copies.peers kid = none := by
            cases copied : copies.peers kid with
            | none => rfl
            | some current => exact absurd found (installed kid current copied)
          have localAbsent : (PqxdhDeploymentCompile.localServer codec copies.log kid none copies.serverRaw).server.peers kid = none := by
            simp only [PqxdhDeploymentCompile.localServer, ite_true, Option.bind_eq_bind, Option.bind_none]
          simp only [PqxdhDeploymentCompile.peerKernel, noCopy, reveal_run, found, Option.map_none, pure_bind]
          rw [serverImpl_absent (fun _ => setup.serverKeyId) route codec.frameRead query _
              (fun other routed => by simp only [target, Option.some.injEq] at routed; subst routed; exact localAbsent),
            serverImpl_absent _ route codec.frameRead query _
              (fun other routed => by
                simp only [target, Option.some.injEq] at routed
                subst routed
                simp only [PqxdhDeploymentNative.serverView, PqxdhDeploymentCompile.merge, found, Option.map_none]),
            PqxdhDeploymentNative.logged_pure, PqxdhDeploymentNative.logged_pure, record_pure]
          simp only [simulateQ_pure, StateT.run_pure, map_pure, localAbsent, Option.map_none]
          rw [← noCopy, Function.update_eq_self]
          rfl
      | some peer =>
          have kernelRun : (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
              (PqxdhDeploymentCompile.peerKernel copies kid)).run native =
              pure (some ((copies.peers kid).getD peer.kernel), native) := by
            cases copied : copies.peers kid with
            | none => simp only [PqxdhDeploymentCompile.peerKernel, copied, reveal_run, found, Option.map_some,
                Option.getD_none]
            | some current => simp only [PqxdhDeploymentCompile.peerKernel, copied, simulateQ_pure, StateT.run_pure,
                Option.getD_some]
          rw [kernelRun, pure_bind]
          have view := visible kid peer found
          have localFound : (PqxdhDeploymentCompile.localServer codec copies.log kid
              (some ((copies.peers kid).getD peer.kernel)) copies.serverRaw).server.peers kid =
              some ⟨peer.identity, (copies.peers kid).getD peer.kernel, ()⟩ := by
            simp [PqxdhDeploymentCompile.localServer, view]
          have mergedFound : (PqxdhDeploymentNative.serverView (PqxdhDeploymentCompile.merge copies native)).server.peers kid =
              some (PqxdhDeploymentCompile.mergePeer (copies.peers kid) peer) := by
            simp [PqxdhDeploymentNative.serverView, PqxdhDeploymentCompile.merge, found]
          rw [serverImpl_peer _ route codec.frameRead query _ kid _ target localFound,
            serverImpl_peer _ route codec.frameRead query _ kid _ target mergedFound,
            PqxdhDeploymentNative.logged_map, PqxdhDeploymentNative.logged_map]
          have localIdentity : (PqxdhDeploymentCompile.localServer codec copies.log kid
              (some ((copies.peers kid).getD peer.kernel)) copies.serverRaw).server.identity =
              native.shared.2.server.server.identity := by
            simp [PqxdhDeploymentCompile.localServer, view]
          have core : serverCore (PqxdhDeploymentNative.senderId (PqxdhDeploymentCompile.merge copies native) ())
              codec.frameRead kid
              (RawCtxServerRouting.associatedBytes
                (PqxdhDeploymentNative.serverView (PqxdhDeploymentCompile.merge copies native)).server.identity
                (PqxdhDeploymentCompile.mergePeer (copies.peers kid) peer).identity)
              (PqxdhDeploymentCompile.mergePeer (copies.peers kid) peer).kernel
              (PqxdhDeploymentNative.serverView (PqxdhDeploymentCompile.merge copies native)).rawAttempts query =
              serverCore setup.serverKeyId codec.frameRead kid
                (RawCtxServerRouting.associatedBytes native.shared.2.server.server.identity peer.identity)
                ((copies.peers kid).getD peer.kernel) copies.serverRaw query := by
            simp only [PqxdhDeploymentNative.senderId, PqxdhDeploymentNative.serverView, PqxdhDeploymentCompile.merge,
              keyId, mergePeer_identity, mergePeer_kernel]
          rw [core, localIdentity, PqxdhDeploymentRecordCache.local_record, record_map, record_map,
            PqxdhDeploymentNative.record_run, PqxdhDeploymentNative.record_run]
          simp only [Functor.map_map]
          congr 1
          funext reply
          simp only [Prod.map, id, RawCtxServerRouting.putPeer_selected, Option.map_some]
          exact Prod.ext rfl (merge_put copies native kid peer reply.1.1.2.1 reply.1.1.2.2 reply.2.2
            (PqxdhDeploymentNative.serverTag query) reply.1.2 found)

/-- An uncreated owner handle is rejected locally without any source14 query. -/
theorem beaconLocal_absent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : PqxdhDeploymentCompile.Local)
    (outside : ¬ index < copies.log.owners.length) :
    (PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies =
      pure (PqxdhDeploymentNative.absent query, copies) := by
  simp only [PqxdhDeploymentCompile.beaconLocal, StateT.run, outside, ite_false]

/-- A created owner handle obtains the owner's kernel, runs on the local owner and keeps the returned kernel and counter. -/
theorem beaconLocal_present (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : PqxdhDeploymentCompile.Local)
    (inside : index < copies.log.owners.length) :
    (PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies =
      PqxdhDeploymentCompile.ownerKernel copies index >>= fun kernel =>
        (fun result => (result.1.1, ({ copies with
          owners := Function.update copies.owners index (PqxdhDeploymentCompile.phaseKernel result.1.2.beacon.phase)
          ownerRaw := Function.update copies.ownerRaw index result.1.2.rawAttempts } : PqxdhDeploymentCompile.Local).produce
            (PqxdhDeploymentNative.beaconTag index) result.2)) <$>
          simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
            ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
              (PqxdhDeploymentCompile.localOwner codec copies.log index kernel (copies.ownerRaw index)))) := by
  simp only [PqxdhDeploymentCompile.beaconLocal, StateT.run, inside, ite_true, bind_pure_comp]

/-- The native Beacon record command on a present owner as a mapped record program. -/
theorem beaconStep_present (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.native.owners[index]? = some owner) :
    (PqxdhDeploymentNative.beaconStep setup codec index query).run state =
      (fun result => (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.beaconTag index)
        result.1.2 { state with
          native := { result.2 with owners := result.2.owners.set index { owner with beacon := result.1.1.2.beacon } }
          ownerRaw := Function.update state.ownerRaw index result.1.1.2.rawAttempts })) <$>
        (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
          ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
          ⟨owner.beacon, state.ownerRaw index⟩))).run state.native := by
  simp only [PqxdhDeploymentNative.beaconStep, StateT.run, found, bind_pure_comp]

/-- The native Beacon record command on a missing owner changes nothing. -/
theorem beaconStep_absent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (missing : state.native.owners[index]? = none) :
    (PqxdhDeploymentNative.beaconStep setup codec index query).run state =
      pure (PqxdhDeploymentNative.absent query, state) := by
  simp only [PqxdhDeploymentNative.beaconStep, StateT.run, missing]

/-- The merged owners read through the list index. -/
theorem merge_owner (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (index : Nat) :
    (PqxdhDeploymentCompile.merge copies native).native.owners[index]? =
      (native.owners[index]?).map (PqxdhDeploymentCompile.mergeOwner (copies.owners index)) := by
  simp only [PqxdhDeploymentCompile.merge, List.getElem?_mapIdx]

/-- Merging after a cache update, a new local kernel and counter of an established owner and its produced frames is the native reinstallation of that owner with the same frames. -/
theorem merge_owner_put (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (kernel : Option Kernel) (raw : Nat)
    (cache : CtxRomAuth.CtxRO.QueryCache) (replacement : PqxdhRegistrationSchedule.Owner KemSK)
    (tag : PqxdhDeploymentInterface.FrameTag) (frames : List PqxdhDeploymentNative.Frame)
    (found : native.owners[index]? = some owner)
    (same : replacement = PqxdhDeploymentCompile.mergeOwner kernel owner) :
    PqxdhDeploymentCompile.merge
        (({ copies with
          owners := Function.update copies.owners index kernel
          ownerRaw := Function.update copies.ownerRaw index raw } : PqxdhDeploymentCompile.Local).produce tag frames)
        (PqxdhDeploymentRecordCache.setCtx native cache) =
      PqxdhDeploymentNative.produce tag frames { PqxdhDeploymentCompile.merge copies native with
        native := { PqxdhDeploymentRecordCache.setCtx (PqxdhDeploymentCompile.merge copies native).native cache with
          owners := (PqxdhDeploymentCompile.merge copies native).native.owners.set index replacement }
        ownerRaw := Function.update copies.ownerRaw index raw } := by
  have owners : native.owners.mapIdx (fun position current =>
      PqxdhDeploymentCompile.mergeOwner (Function.update copies.owners index kernel position) current) =
      (native.owners.mapIdx fun position current =>
        PqxdhDeploymentCompile.mergeOwner (copies.owners position) current).set index replacement := by
    apply List.ext_getElem?
    intro position
    rw [List.getElem?_mapIdx, List.getElem?_set, List.getElem?_mapIdx, List.length_mapIdx]
    by_cases equal : index = position
    · subst equal
      have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
      simp only [found, Option.map_some, Function.update_self, same, ite_true, bound]
    · simp only [equal, ite_false, Function.update_of_ne (Ne.symm equal)]
  simp only [PqxdhDeploymentCompile.merge, PqxdhDeploymentRecordCache.setCtx, owners, PqxdhDeploymentCompile.Local.produce,
    PqxdhDeploymentNative.produce]

/-- Merging a local kernel into an owner keeps its outer key ID. -/
theorem mergeOwner_identityKeyId (kernel : Option Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (PqxdhDeploymentCompile.mergeOwner kernel owner).beacon.identityKeyId = owner.beacon.identityKeyId := by
  unfold PqxdhDeploymentCompile.mergeOwner
  split <;> rfl

/-- Merging a local kernel into an owner keeps its registry raw-attempt field. -/
theorem mergeOwner_rawAttempts (kernel : Option Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (PqxdhDeploymentCompile.mergeOwner kernel owner).rawAttempts = owner.rawAttempts := by
  unfold PqxdhDeploymentCompile.mergeOwner
  split <;> rfl

/-- Beacon record commands (item c of the compile lemma): when the log counts every created owner, every locally copied owner is established, and every established owner is publicly reconstructible, the compiled command run on the source14 state has, after merging, exactly the native command's reply and deployment poststate. -/
theorem beacon_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (count : copies.log.owners.length = native.owners.length)
    (copied : ∀ position current, copies.owners position = some current →
      ∃ owner control associatedData kernel, native.owners[position]? = some owner ∧
        owner.beacon.phase = .established control associatedData kernel)
    (visible : ∀ position owner control associatedData kernel, native.owners[position]? = some owner →
      owner.beacon.phase = .established control associatedData kernel →
      PqxdhDeploymentCompile.ownerView codec copies.log position =
        some (owner.beacon.identityKeyId, control, associatedData)) :
    (fun result => (result.1.1, PqxdhDeploymentCompile.merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
        ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies)).run native =
      (PqxdhDeploymentNative.beaconStep setup codec index query).run (PqxdhDeploymentCompile.merge copies native) := by
  by_cases inside : index < copies.log.owners.length
  · obtain ⟨owner, found⟩ : ∃ owner, native.owners[index]? = some owner :=
      ⟨native.owners[index]'(count ▸ inside), List.getElem?_eq_getElem (count ▸ inside)⟩
    have mergedFound : (PqxdhDeploymentCompile.merge copies native).native.owners[index]? =
        some (PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner) := by
      rw [merge_owner, found, Option.map_some]
    rw [beaconLocal_present setup codec index query copies inside,
      beaconStep_present setup codec index query _ _ mergedFound]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map, map_bind]
    by_cases active : ∃ control associatedData kernel, owner.beacon.phase = .established control associatedData kernel
    · obtain ⟨control, associatedData, kernel, phase⟩ := active
      have kernelRun : (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (PqxdhDeploymentCompile.ownerKernel copies index)).run native =
          pure (some ((copies.owners index).getD kernel), native) := by
        cases copiedKernel : copies.owners index with
        | none => simp only [PqxdhDeploymentCompile.ownerKernel, copiedKernel, kernel_run, found, Option.bind_some,
            phase, PqxdhDeploymentCompile.phaseKernel, Option.getD_none]
        | some current => simp only [PqxdhDeploymentCompile.ownerKernel, copiedKernel, simulateQ_pure, StateT.run_pure,
            Option.getD_some]
      rw [kernelRun, pure_bind]
      have view := visible index owner control associatedData kernel found phase
      have localPhase : (PqxdhDeploymentCompile.localOwner codec copies.log index (some ((copies.owners index).getD kernel))
          (copies.ownerRaw index)).beacon.phase = .established control associatedData ((copies.owners index).getD kernel) := by
        simp only [PqxdhDeploymentCompile.localOwner, view]
      have mergedPhase : (PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).beacon.phase =
          .established control associatedData ((copies.owners index).getD kernel) := by
        cases copies.owners index <;> simp [PqxdhDeploymentCompile.mergeOwner, phase]
      rw [beaconImpl_established codec.frameRead query _ control associatedData _ localPhase,
        beaconImpl_established codec.frameRead query
          ⟨(PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).beacon,
            (PqxdhDeploymentCompile.merge copies native).ownerRaw index⟩ control associatedData _ mergedPhase]
      have localKey : (PqxdhDeploymentCompile.localOwner codec copies.log index (some ((copies.owners index).getD kernel))
          (copies.ownerRaw index)).beacon.identityKeyId = owner.beacon.identityKeyId := by
        simp only [PqxdhDeploymentCompile.localOwner, view]
      have localRaw : (PqxdhDeploymentCompile.localOwner codec copies.log index (some ((copies.owners index).getD kernel))
          (copies.ownerRaw index)).rawAttempts = copies.ownerRaw index := by
        simp only [PqxdhDeploymentCompile.localOwner, view]
      simp only [localKey, localRaw, mergeOwner_identityKeyId]
      rw [PqxdhDeploymentNative.logged_map, PqxdhDeploymentNative.logged_map, PqxdhDeploymentRecordCache.local_record, record_map, record_map, PqxdhDeploymentNative.record_run,
        PqxdhDeploymentNative.record_run]
      simp only [Functor.map_map]
      congr 1
      funext reply
      exact Prod.ext rfl (merge_owner_put copies native index owner (some reply.1.1.2.1) reply.1.1.2.2 reply.2.2 _
        (PqxdhDeploymentNative.beaconTag index) reply.1.2 found
        (by cases copies.owners index <;> simp [PqxdhDeploymentCompile.mergeOwner, phase]))
    · have noCopy : copies.owners index = none := by
        cases copiedKernel : copies.owners index with
        | none => rfl
        | some current =>
            obtain ⟨other, control, associatedData, kernel, otherFound, phase⟩ := copied index current copiedKernel
            rw [found, Option.some.injEq] at otherFound
            subst otherFound
            exact absurd ⟨control, associatedData, kernel, phase⟩ active
      have inactivePhase : PqxdhDeploymentCompile.phaseKernel owner.beacon.phase = none := by
        cases phase : owner.beacon.phase <;> simp_all [PqxdhDeploymentCompile.phaseKernel]
      have kernelRun : (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (PqxdhDeploymentCompile.ownerKernel copies index)).run native = pure (none, native) := by
        simp only [PqxdhDeploymentCompile.ownerKernel, noCopy, kernel_run, found, Option.bind_some, inactivePhase]
      rw [kernelRun, pure_bind]
      have mergedOwner : PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner = owner := by
        rw [noCopy]
        rfl
      have localInactive : ¬ RawCtxBeaconLifecycle.Established
          (PqxdhDeploymentCompile.localOwner codec copies.log index none (copies.ownerRaw index)).beacon.phase := by
        simp [PqxdhDeploymentCompile.localOwner, RawCtxBeaconLifecycle.Established]
      have mergedInactive : ¬ RawCtxBeaconLifecycle.Established
          (PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).beacon.phase := by
        rw [mergedOwner]
        intro established
        cases phase : owner.beacon.phase <;> simp_all [RawCtxBeaconLifecycle.Established]
      rw [RawCtxBeaconLifecycle.inactive codec.frameRead query _ localInactive,
        RawCtxBeaconLifecycle.inactive codec.frameRead query
          ⟨(PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).beacon,
            (PqxdhDeploymentCompile.merge copies native).ownerRaw index⟩ mergedInactive,
        PqxdhDeploymentNative.logged_pure, PqxdhDeploymentNative.logged_pure, record_pure]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      have same : (⟨(PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).beacon,
          (PqxdhDeploymentCompile.mergeOwner (copies.owners index) owner).rawAttempts⟩ :
          PqxdhRegistrationSchedule.Owner KemSK) = PqxdhDeploymentCompile.mergeOwner none owner := by
        rw [mergedOwner]
        rfl
      rcases query with plaintext | raw
      · exact congrArg pure (Prod.ext rfl (merge_owner_put copies native index owner none (copies.ownerRaw index)
          native.shared.2.ctx _ _ [] found same))
      · exact congrArg pure (Prod.ext rfl (merge_owner_put copies native index owner none (copies.ownerRaw index + 1)
          native.shared.2.ctx _ _ [] found same))
  · have missing : (PqxdhDeploymentCompile.merge copies native).native.owners[index]? = none := by
      rw [merge_owner, List.getElem?_eq_none (by omega), Option.map_none]
    rw [beaconLocal_absent setup codec index query copies inside, beaconStep_absent setup codec index query _ missing]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]

end BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverImpl_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverImpl_peer

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverImpl_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverImpl_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconImpl_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconImpl_established

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.reveal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.reveal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.kernel_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.kernel_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.record_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.record_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.record_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.record_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverStep_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverLocal_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverLocal_none

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverLocal_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.serverLocal_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergePeer_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergePeer_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergePeer_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergePeer_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_produce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_produce

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_put

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.server_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.server_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconLocal_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconLocal_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconLocal_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconLocal_present

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconStep_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconStep_present

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconStep_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beaconStep_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_owner_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.merge_owner_put

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergeOwner_identityKeyId' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergeOwner_identityKeyId

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergeOwner_rawAttempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.mergeOwner_rawAttempts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beacon_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords.beacon_record
