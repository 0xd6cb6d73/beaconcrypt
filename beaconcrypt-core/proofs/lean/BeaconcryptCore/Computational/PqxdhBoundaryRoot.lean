-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationSchedule
import BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts

/-! The extracted 192-byte request at the existing R1 interpreter, with real Expand and the complete shared state. This is an operational boundary, not a fixed-HKDF/random-table security claim. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRoot
open PqxdhSecretInputKdf PqxdhServerAuthNative
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhBeaconPhase2Preparation (Word32)
variable {Reader Response KemSK ι : Type} {baseSpec : OracleSpec ι}

/-- The extracted builder's successful value has the literal padding and all five contributions in source order. No assumption about their independence is made. -/
theorem built_input (secrets : pqxdh.PqxdhSharedSecrets) (input : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input secrets = ok (.Ok input)) :
    absBytes input.bytes = Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
      (absBytes secrets.dh3) (absBytes secrets.dh4) (absBytes secrets.kem_shared_secret) := by
  classical
  by_cases valid : Pqxdh.dhNonZero (absBytes secrets.dh1, absBytes secrets.dh2,
      absBytes secrets.dh3, absBytes secrets.dh4)
  · obtain ⟨actual, generated, bytes⟩ := (build_root_key_input_abs secrets).1 valid
    rw [built] at generated
    cases generated
    exact bytes
  · have rejected := (build_root_key_input_abs secrets).2 valid
    rw [built] at rejected
    cases rejected

/-- Every supplied native root request is exactly 192 bytes, including requests on rejection paths that reach the callback. -/
theorem input_length (input : pqxdh.RootKeyInput) : (absBytes input.bytes).length = 192 := by
  simp

/-- The unlogged native root callback queries the existing Extract table at the exact source-built bytes and keeps the original complete state. -/
theorem source_built (hmac : HmacSha512) (secrets : pqxdh.PqxdhSharedSecrets)
    (input : pqxdh.RootKeyInput) (built : pqxdh.build_root_key_input secrets = ok (.Ok input))
    (state : NativeState KemSK) :
    sourceRoot hmac input state =
      (fun result => (some (PqxdhRootTableInitialization.rootArray (expandRoot hmac result.1)),
        ({ state.1 with cache := result.2 }, state.2))) <$>
      (HmacOracle.randomOracle (Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
        (absBytes secrets.dh3) (absBytes secrets.dh4) (absBytes secrets.kem_shared_secret))).run state.1.cache := by
  unfold sourceRoot
  rw [built_input secrets input built]

/-- The actual registration tail dispatches its root request directly to the same native interpreter. -/
theorem tail_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : pqxdh.RootKeyInput) :
    PqxdhServerAuthNative.sourceBeaconTail setup codec (.inr (.root input)) =
      sourceRoot setup.hmac input := by
  rfl

/-- The owner scheduler forwards the same root input without reconstructing it from public transcript fields. -/
theorem scheduler_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : pqxdh.RootKeyInput) :
    PqxdhRegistrationSchedule.callbacks setup codec (.inr (.inr (.root input))) =
      sourceRoot setup.hmac input := by
  rfl

/-- Exact source request transport remains valid for an arbitrary complete continuation, including one observing cache/history and every private native field. -/
theorem source_complete {Result : Type} (hmac : HmacSha512)
    (secrets : pqxdh.PqxdhSharedSecrets) (input : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input secrets = ok (.Ok input)) (state : NativeState KemSK)
    (next : Option Word32 × NativeState KemSK → ProbComp Result) :
    sourceRoot hmac input state >>= next =
      (HmacOracle.randomOracle (Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
        (absBytes secrets.dh3) (absBytes secrets.dh4) (absBytes secrets.kem_shared_secret))).run state.1.cache >>=
      fun result => next (some (PqxdhRootTableInitialization.rootArray (expandRoot hmac result.1)),
        ({ state.1 with cache := result.2 }, state.2)) := by
  rw [source_built hmac secrets input built, bind_map_left]

/-- The Server root callback retains both family history entries and its session touch in the same joint distribution as the returned 32-byte root. -/
theorem logged_complete {Result : Type} (hmac : HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (original : pqxdh.PendingServerRegistration) (state : NativeState KemSK)
    (next : RootOutput × NativeState KemSK → ProbComp Result) :
    loggedRoot hmac index input original state >>= next =
      (HmacOracle.randomOracle (absBytes original.root_key_input.bytes)).run state.1.cache >>=
      fun result => next (expandRoot hmac result.1,
        ((⟨state.1.history ++ [.derive (PqxdhServerRelatedRootConsumer.nativeMessage input) (some result.1),
          .publicHmac result.1 rootExpandInput (hmac.eval result.1 rootExpandInput)], result.2⟩ :
          PqxdhJointDhExtractFamily.State),
        { state.2 with ghost := { state.2.ghost with touches := state.2.ghost.touches ++
          [.session index (PqxdhServerRelatedRootConsumer.nativeMessage input) (some (expandRoot hmac result.1))] } })) := by
  change ((loggedRoot hmac index input original).run state >>= next) = _
  simp only [loggedRoot, StateT.run_bind, StateT.run_map, romRoot, nativeTouch,
    bind_map_left, bind_assoc, bind_pure_comp]
  simp only [StateT.run, romRootBytes, localState, bind_map_left, pure_bind]

/-- The same complete logged Server continuation is reached at the extracted builder's exact six-block input, not at a transcript-reconstructed address. -/
theorem logged_built_complete {Result : Type} (hmac : HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (original : pqxdh.PendingServerRegistration) (secrets : pqxdh.PqxdhSharedSecrets)
    (built : pqxdh.build_root_key_input secrets = ok (.Ok original.root_key_input))
    (state : NativeState KemSK) (next : RootOutput × NativeState KemSK → ProbComp Result) :
    loggedRoot hmac index input original state >>= next =
      (HmacOracle.randomOracle (Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
        (absBytes secrets.dh3) (absBytes secrets.dh4) (absBytes secrets.kem_shared_secret))).run state.1.cache >>=
      fun result => next (expandRoot hmac result.1,
        ((⟨state.1.history ++ [.derive (PqxdhServerRelatedRootConsumer.nativeMessage input) (some result.1),
          .publicHmac result.1 rootExpandInput (hmac.eval result.1 rootExpandInput)], result.2⟩ :
          PqxdhJointDhExtractFamily.State),
        { state.2 with ghost := { state.2.ghost with touches := state.2.ghost.touches ++
          [.session index (PqxdhServerRelatedRootConsumer.nativeMessage input) (some (expandRoot hmac result.1))] } })) := by
  rw [logged_complete, built_input secrets original.root_key_input built]

/-- The concrete scheduler root callback costs at most the existing 64 byte draws for one table miss; real Expand and native bookkeeping are retained local work. -/
theorem scheduler_root_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : pqxdh.RootKeyInput) (state : NativeState KemSK) :
    ((PqxdhRegistrationSchedule.callbacks setup codec (.inr (.inr (.root input)))).run state).IsTotalQueryBound 64 := by
  rw [scheduler_root]
  simp only [sourceRoot, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  exact PqxdhServerAuthNativeUniformCosts.extract_table_uniform _ _

/-- The next initial-ratchet request uses the returned root at the real 64-byte symmetric KDF interface, preserving both complete caches and every native field. -/
theorem initial_complete {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (root : Word32) (state : NativeState KemSK)
    (next : pqxdh.concrete.InitialRatchetKdfResponse × NativeState KemSK → ProbComp Result) :
    (PqxdhRegistrationSchedule.callbacks setup codec (.inr (.inr
      (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request)))).run state >>= next =
      next (RawCtxSourceHkdf.initialResponse setup.source.crypto ⟨root, ratchet.SYM_RATCHET_INFO⟩, state) := by
  rfl

/-- The concrete initial reply has the same 64-byte prefix as the real 76-byte ratchet response at that input and label; projections are not independent samples. -/
theorem initial_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (root : Word32) (state : NativeState KemSK) :
    (fun result => (absBytes result.1.bytes, result.2)) <$>
      (PqxdhRegistrationSchedule.callbacks setup codec (.inr (.inr
        (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request)))).run state =
      pure ((absBytes (RawCtxSourceHkdf.response setup.source.crypto ⟨root, ratchet.SYM_RATCHET_INFO⟩).bytes).take 64, state) := by
  change (pure (absBytes (RawCtxSourceHkdf.initialResponse setup.source.crypto
    ⟨root, ratchet.SYM_RATCHET_INFO⟩).bytes, state) : ProbComp (Pqxdh.Bytes × NativeState KemSK)) = _
  rw [RawCtxSourceHkdf.initialResponse_prefix]

end BeaconcryptCore.Computational.PqxdhBoundaryRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.built_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.built_input

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.input_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.input_length

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.source_built' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.source_built

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.tail_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.tail_root

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.scheduler_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.scheduler_root

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.source_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.logged_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.logged_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.logged_built_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.logged_built_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.scheduler_root_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.scheduler_root_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.initial_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.initial_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRoot.initial_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRoot.initial_prefix
