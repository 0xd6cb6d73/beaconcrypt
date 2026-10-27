-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompiler
import BeaconcryptCore.Computational.CborAdmissionCachedBudget

/-! The public admission compiler prefetches one Server peer kernel, checks the complete CBOR frame length, and runs the existing local record operation only when admitted. The simulation preserves the exact reply and complete merged deployment state, retains the full compiler invariant including the public assignment counter, and issues at most the original one peer reveal plus one commitment hash. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionServerCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open CborAdmissionCompiler (Local Good merge nativeHandler serverSend)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

theorem step_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (keyId : Std.U64)
    (plaintext : Pqxdh.Bytes) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((serverSend setup codec route keyId plaintext).run memory)).run native =
      (nativeHandler setup codec checks route seed (.inr (.serverSend keyId plaintext))).run (merge memory native) := by
  change (fun result => (result.1.1, merge result.1.2 result.2)) <$>
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      (CborAdmissionCompiler.serverSend setup codec route keyId plaintext memory)).run native = _
  simp only [serverSend, simulateQ_bind, StateT.run_bind]
  rw [CborAdmissionPreload.peer_read_run setup codec checks seed memory.copies native good.nativeGood keyId,
    pure_bind]
  cases found : (PqxdhDeploymentCompile.merge memory.copies native).native.shared.2.server.server.peers keyId
  case some peer =>
    simp only [Option.map_some]
    have selected : ((PqxdhDeploymentCompile.merge memory.copies native).native.shared.2.server.server.peers keyId).map
        RawCtxServerRouting.Peer.kernel = some peer.kernel :=
      congrArg (Option.map RawCtxServerRouting.Peer.kernel) found
    have present : native.shared.2.server.server.peers keyId ≠ none := by
      simpa only [PqxdhDeploymentCompile.merge, ne_eq, Option.map_eq_none_iff] using
        (Option.ne_none_iff_exists'.mpr ⟨peer, found⟩)
    have loadedGood := CborAdmissionPreload.preload_peer_good setup codec memory.copies native
      good.nativeGood keyId peer.kernel present
    have preserved := CborAdmissionPreload.peer_merge memory.copies native keyId peer.kernel selected
    change _ = if CborProductionBoundary.allowed (.inr (.serverSend keyId plaintext)) (merge memory native) then
      (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.serverSend keyId plaintext))).run
        (merge memory native)
      else pure (CborProductionBoundary.reject (.inr (.serverSend keyId plaintext)) (merge memory native))
    have identity : (PqxdhDeploymentCompile.merge memory.copies native).native.shared.2.server.identityKeyId =
        setup.serverKeyId := good.nativeGood.keyId
    simp only [CborProductionBoundary.allowed, merge, found, identity]
    split_ifs with fits
    case pos =>
      have old := PqxdhDeploymentCompileRecords.server_record setup codec checks route seed
        (.inl (plaintext, keyId))
        { memory.copies with peers := Function.update memory.copies.peers keyId (some peer.kernel) }
        native loadedGood.keyId loadedGood.installed loadedGood.serverVisible
      rw [preserved] at old
      simpa only [simulateQ_map, StateT.run_map, Functor.map_map, PqxdhDeploymentNative.handler] using old
    case neg =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure, CborProductionBoundary.reject, preserved]
  case none =>
    simp only [Option.map_none, simulateQ_pure, StateT.run_pure, map_pure]
    simp only [nativeHandler, CborCommandFilter.handler, StateT.run,
      CborProductionBoundary.allowed, merge, found, ite_true, PqxdhDeploymentNative.handler,
      PqxdhDeploymentNative.serverStep, RawCtxServerMixed.serverImpl, RawCtxServerMixed.sendServer,
      RawCtxServerSend.sendServer, PqxdhDeploymentNative.serverView, RawCtxServerRouting.peerAssociatedData,
      Option.bind_eq_bind, Option.bind_none, simulateQ_pure, PqxdhDeploymentNative.logged_pure,
      PqxdhDeploymentNative.record, PqxdhRegistrationSchedule.onShared, PqxdhServerAuthNative.nativeCtx,
      PqxdhDeploymentNative.withServer, PqxdhDeploymentNative.produce]
    simp only [StateT.monad_pure_def, StateT.pure, map_pure, pure_bind, List.map_nil, List.append_nil]

theorem good_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (keyId : Std.U64)
    (plaintext : Pqxdh.Bytes) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native)
    (result : (Option RawCtxSourceSend.Encrypted × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((serverSend setup codec route keyId plaintext).run memory)).run native)) :
    Good setup codec result.1.2 result.2 := by
  change result ∈ support ((simulateQ
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
    (CborAdmissionCompiler.serverSend setup codec route keyId plaintext memory)).run native) at supported
  simp only [serverSend, simulateQ_bind, StateT.run_bind] at supported
  rw [CborAdmissionPreload.peer_read_run setup codec checks seed memory.copies native good.nativeGood keyId,
    pure_bind] at supported
  cases found : (PqxdhDeploymentCompile.merge memory.copies native).native.shared.2.server.server.peers keyId
  case some peer =>
    simp only [found, Option.map_some] at supported
    have present : native.shared.2.server.server.peers keyId ≠ none := by
      simpa only [PqxdhDeploymentCompile.merge, ne_eq, Option.map_eq_none_iff] using
        (Option.ne_none_iff_exists'.mpr ⟨peer, found⟩)
    have loadedGood := CborAdmissionPreload.preload_peer_good setup codec memory.copies native
      good.nativeGood keyId peer.kernel present
    split_ifs at supported with fits
    case pos =>
      simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
      obtain ⟨reached, supported, rfl⟩ := supported
      refine ⟨PqxdhDeploymentCompileInvariant.good_server_record setup codec checks route seed
        (.inl (plaintext, keyId)) _ native loadedGood reached supported, ?_⟩
      obtain ⟨⟨cache, preserved⟩, _⟩ := PqxdhDeploymentCompileInvariant.serverLocal_support
        setup codec checks route seed (.inl (plaintext, keyId)) _ native reached supported
      simpa only [preserved, PqxdhDeploymentRecordCache.setCtx] using good.lastId
    case neg =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨loadedGood, good.lastId⟩
  case none =>
    simp only [found, Option.map_none, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    simpa only [supported] using good

theorem source_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : PqxdhRegistrationJointRevealCosts.SourceKind)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (memory : Local) :
    ((serverSend setup codec route keyId plaintext).run memory).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = kind)
      (PqxdhDeploymentCompileBudget.unit kind (.inl 8) + PqxdhDeploymentCompileBudget.unit kind (.inl 7)) := by
  change (CborAdmissionCompiler.serverSend setup codec route keyId plaintext memory).IsQueryBoundP _ _
  unfold CborAdmissionCompiler.serverSend
  refine isQueryBoundP_bind (PqxdhDeploymentCompileBudget.peerKernel_bound kind memory.copies keyId)
    fun kernel _ => ?_
  cases kernel
  case some current cachedSupport =>
    dsimp only
    split_ifs
    case pos =>
      rw [isQueryBoundP_map_iff]
      exact CborAdmissionCachedBudget.server_cached setup codec route kind (.inl (plaintext, keyId))
        { memory.copies with peers := Function.update memory.copies.peers keyId (some current) }
        keyId current rfl (Function.update_self ..)
    case neg => trivial
  case none => trivial

end BeaconcryptCore.Computational.CborAdmissionServerCompiler

/-- info: 'BeaconcryptCore.Computational.CborAdmissionServerCompiler.step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionServerCompiler.step_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionServerCompiler.good_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionServerCompiler.good_support
/-- info: 'BeaconcryptCore.Computational.CborAdmissionServerCompiler.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionServerCompiler.source_bound
