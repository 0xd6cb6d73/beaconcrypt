import BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap

/-!
The original selected KDF frame receives the actual full76 response and runs its saved source continuations through the owner, Server or Beacon, entire family and original LIVE history. The same execution is obtained from the material-only stopped context by interpreting its hidden chain privately. Every original field and shared primitive effect is retained. The correspondence is proved from the concrete pending frame constructors, not assumed for an arbitrary continuation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext
open RawCtxSelectedFamilyContext RawCtxSelectedParentCalls RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedParentFamilyMap
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
variable {M P I D K A Result : Type} {S B : Nat}

noncomputable def ownerReply (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (context : OwnerContext M Result) (output : FullOutput) :
    (PrimitiveSpec RatchetChain).Range (ownerFrame sender decode context).1 :=
  match context with
  | .receive _ _ _ | .send _ _ _ => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)

noncomputable def serverReply (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : ServerContext M P Result) (output : FullOutput) :
    (PrimitiveSpec RatchetChain).Range (serverFrame sender route decode context).1 :=
  match context with
  | .owner _ before _ _ _ inner => ownerReply (sender before.server.metadata) decode inner output

noncomputable def familyReply (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : FamilyContext M P I D K Result S B) (output : FullOutput) :
    (PrimitiveSpec RatchetChain).Range (familyFrame sender route decode context).1 :=
  match context with
  | .server _ _ _ _ inner => serverReply sender route decode inner output
  | .beacon _ before index _ _ _ inner => ownerReply (before.2 index).beacon.identityKeyId decode inner output

noncomputable def reply (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B) (output : FullOutput) :
    (LivePrimitiveSpec RatchetChain S B).Range (frame sender route decode context).1 :=
  match context with
  | .family _ _ _ inner => familyReply sender route decode inner output

/-- The original pending owner frame receives the actual native response and finishes its complete original outside client from the material-only stopped context. -/
theorem owner_cut (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (context : OwnerContext M Result) (output : FullOutput) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior
      (fromOutput (ownerAddress context) output) (nextChain output))
      ((ownerFrame sender decode context).2 (ownerReply sender decode context output)) =
      Prod.map id (RawCtxSelectedParentOwner.mapOwner (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (ownerAddress context) output)
          (childResponse prior (fromOutput (ownerAddress context) output) (nextChain output)))
          (ownerStopped sender decode context (material output)) := by
  cases context with
  | receive before outside pending =>
      exact (RawCtxSelectedParentNativeContext.receive_tail source writer prior sender decode before outside pending output).trans
        (RawCtxSelectedParentOwnerCut.receive_cut source writer prior sender decode before outside pending output)
  | send before outside pending =>
      exact (RawCtxSelectedParentNativeContext.send_tail source writer prior sender decode before outside pending output).trans
        (RawCtxSelectedParentOwnerCut.send_cut source writer prior sender decode before outside pending output)

private theorem known_kernel (target : RootOutput) (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain) :
    nativeKernel target (knownKernel kernel) = kernel := by
  simp only [nativeKernel, knownKernel, RawCtxChainInterpretation.mapChains, RawCtxSelectedChain.interpret]

private theorem known_peer (target : RootOutput) (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P) :
    mapPeer (nativeKernel target) (mapPeer knownKernel peer) = peer := by
  simp only [mapPeer, known_kernel]

private theorem known_server (target : RootOutput) (state : NativeServer M P) :
    mapServer (nativeKernel target) (mapServer knownKernel state) = state := by
  simp [mapServer, Option.map_map, Function.comp_def, known_peer]

/-- The exact assigned-peer publication and saved original Server continuation preserve the native owner result and every other peer. -/
theorem server_cut (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : ServerContext M P Result) (output : FullOutput) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior
      (fromOutput (serverAddress context) output) (nextChain output))
      ((serverFrame sender route decode context).2 (serverReply sender route decode context output)) =
      Prod.map id (mapServer (nativeKernel (nextChain output))) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (serverAddress context) output)
          (childResponse prior (fromOutput (serverAddress context) output) (nextChain output)))
          (serverStopped sender route decode context (material output)) := by
  cases context with
  | owner request before kid peer outside inner =>
      simp only [serverFrame, serverReply, serverAddress, serverStopped,
        RawCtxPendingServerTails.liftOwner, simulateQ_bind]
      rw [owner_cut]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro result
      have published := RawCtxGenericServer.put_map (nativeKernel (nextChain output))
        (mapServer knownKernel before) kid (mapPeer knownKernel peer) result.2.kernel result.2.rawAttempts
      rw [known_server, known_peer] at published
      simp only [RawCtxPendingServerTails.afterOwner, Prod.map_def, id_eq,
        RawCtxSelectedParentOwner.mapOwner, RawCtxGenericOwnerMap.mapOwner]
      rw [← published]
      exact server_program source writer prior (fromOutput (ownerAddress inner) output) (nextChain output)
        sender route decode (outside result.1) _

private theorem known_beacon (target : RootOutput)
    (state : RawCtxGenericRoleStorage.BeaconState (RawCtxPendingOwnerQueries.Kernel RatchetChain) I D K) :
    mapBeacon (nativeKernel target) (mapBeacon knownKernel state) = state := by
  cases phase : state.beacon.phase <;>
    simp [mapBeacon, mapPhase, phase, known_kernel]
  all_goals rw [← phase]

private theorem updated_server (target : RootOutput) (before : NativeFamily M P I D K S B)
    (index : Fin S) (state : RawCtxPendingServerTails.State RawCtxSelectedChain.Slot M P) :
    mapRoles (nativeKernel target)
      (Function.update (mapRoles knownKernel before).1 index state, (mapRoles knownKernel before).2) =
      (Function.update before.1 index (mapServer (nativeKernel target) state), before.2) := by
  apply Prod.ext
  · funext other
    by_cases same : other = index
    · subst other
      simp only [mapRoles, Function.update_self]
    · simp only [mapRoles, Function.update_of_ne same, known_server]
  · funext other
    exact known_beacon target (before.2 other)

private theorem updated_beacon (target : RootOutput) (before : NativeFamily M P I D K S B)
    (index : Fin B) (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (owner : RawCtxPendingOwnerTails.Owner RawCtxSelectedChain.Slot Unit) :
    mapRoles (nativeKernel target)
      ((mapRoles knownKernel before).1, Function.update (mapRoles knownKernel before).2 index
        (RawCtxGenericBeacon.reinstall ((mapRoles knownKernel before).2 index) control associatedData owner)) =
      (before.1, Function.update before.2 index (RawCtxGenericBeacon.reinstall (before.2 index) control associatedData
        (RawCtxSelectedParentOwner.mapOwner target owner))) := by
  apply Prod.ext
  · funext other
    exact known_server target (before.1 other)
  · funext other
    by_cases same : other = index
    · subst other
      simp only [mapRoles, Function.update_self]
      rfl
    · simp only [mapRoles, Function.update_of_ne same, known_beacon]

/-- The saved Server or Beacon frame reinstalls its actual returned state and preserves the entire original family continuation. -/
theorem family_cut (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : FamilyContext M P I D K Result S B) (output : FullOutput) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior
      (fromOutput (familyAddress context) output) (nextChain output))
      ((familyFrame sender route decode context).2 (familyReply sender route decode context output)) =
      Prod.map id (mapRoles (nativeKernel (nextChain output))) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (familyAddress context) output)
          (childResponse prior (fromOutput (familyAddress context) output) (nextChain output)))
          (familyStopped sender route decode context (material output)) := by
  cases context with
  | server request before index outside inner =>
      simp only [familyFrame, familyReply, familyAddress, familyStopped,
        RawCtxPendingFamilyTails.liftServer, simulateQ_bind]
      rw [server_cut]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro result
      simp only [RawCtxPendingFamilyTails.afterServer, Prod.map_def, id_eq]
      rw [← updated_server (nextChain output) before index result.2]
      exact family_program source writer prior (fromOutput (serverAddress inner) output) (nextChain output)
        sender route decode (outside result.1) _
  | beacon request before index control associatedData outside inner =>
      simp only [familyFrame, familyReply, familyAddress, familyStopped,
        RawCtxPendingFamilyTails.liftBeacon, simulateQ_bind]
      rw [owner_cut]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro result
      simp only [RawCtxPendingFamilyTails.afterBeacon, Prod.map_def, id_eq]
      rw [← updated_beacon (nextChain output) before index control associatedData result.2]
      exact family_program source writer prior (fromOutput (ownerAddress inner) output) (nextChain output)
        sender route decode (outside result.1) _

/-- The actual selected complete LIVE frame receives the same native full response and preserves all family fields and actual read history under the material-only source cut. -/
theorem frame_cut (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (output : FullOutput) :
    simulateQ (nativeLive (A := A) source writer prior (fromOutput (address context) output) (nextChain output))
      ((frame sender route decode context).2 (reply sender route decode context output)) =
      Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel (nextChain output))) <$>
        simulateQ (labelLive source writer prior (fromOutput (address context) output) (nextChain output))
          (stopped sender route decode context (material output)) := by
  cases context with
  | family request history outside inner =>
      simp only [frame, reply, address, stopped, RawCtxPendingFamilyLiveTails.liftFamily, simulateQ_bind,
        ← QueryImpl.simulateQ_compose, nativeLive, labelLive, RawCtxPendingFamilyLiveQueries.primitive_handler]
      rw [family_cut]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro result
      exact live_program source writer prior (fromOutput (familyAddress inner) output) (nextChain output)
        sender route decode (outside result.1) (result.2, RawCtxProtocolReveals.tick history)

/-- Evaluating the complete source cut preserves the entire mutable shared primitive state; only private kernel representation is mapped. -/
theorem frame_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (output : FullOutput) (state : RawCtxSharedPrimitive.SharedState A) :
    (simulateQ (nativeLive source writer prior (fromOutput (address context) output) (nextChain output))
      ((frame sender route decode context).2 (reply sender route decode context output))).run state =
      Prod.map (Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel (nextChain output)))) id <$>
        (simulateQ (labelLive source writer prior (fromOutput (address context) output) (nextChain output))
          (stopped sender route decode context (material output))).run state := by
  rw [frame_cut, StateT.run_map]
  rfl

end BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.owner_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.owner_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.server_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.server_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.family_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.family_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.frame_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.frame_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext.frame_run
