import BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler
import BeaconcryptCore.Computational.RawCtxForwardRoleScope
import BeaconcryptCore.Computational.PqxdhInitialPostCertificates

/-!
The literal saved record descriptor finishes its pending owner and reinstalls that result through the same Server peer, Beacon phase and indexed role family. The inner source continuations are quiet because this descriptor belongs to one original record request. The outer adaptive Post continuation is kept separate.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedFamilyContext RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open RawCtxSelectedReceiveCompiler (State project evaluated)
variable {A M P I D K Result : Type} {S B : Nat}

noncomputable def quietValue {ι : Type} {spec : OracleSpec ι} {Value : Type}
    (client : OracleComp spec Value) (quiet : client.IsTotalQueryBound 0) : Value :=
  (RawCtxQuietOwnerTails.zero_pure client quiet).choose

def materialKnown : RawCtxPendingOwnerQueries.Kernel RatchetChain → RawCtxSelectedMessageReveals.Kernel :=
  RawCtxMaterialInterpretation.mapRefined Slot.known

private theorem known_peer (key : RootOutput) (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P) :
    mapPeer (RawCtxMaterialInterpretation.mapRefined (interpret key)) (mapPeer materialKnown peer) = peer := by
  cases peer
  simp only [mapPeer, materialKnown, known_kernel]

private theorem known_server (key : RootOutput) (before : NativeServer M P) :
    mapServer (RawCtxMaterialInterpretation.mapRefined (interpret key)) (mapServer materialKnown before) = before := by
  cases before
  simp only [mapServer, Option.map_map, Function.comp_def, known_peer, Option.map_id']

private theorem known_beacon (key : RootOutput)
    (before : BeaconState (RawCtxPendingOwnerQueries.Kernel RatchetChain) I D K) :
    mapBeacon (RawCtxMaterialInterpretation.mapRefined (interpret key)) (mapBeacon materialKnown before) = before := by
  cases phase : before.beacon.phase <;>
    simp only [mapBeacon, mapPhase, phase, materialKnown, known_kernel]
  all_goals rw [← phase]

private theorem updated_beacon (key : RootOutput) (before : NativeFamily M P I D K S B)
    (index : Fin B) (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Unit) :
    mapRoles (RawCtxMaterialInterpretation.mapRefined (interpret key))
      ((mapRoles materialKnown before).1, Function.update (mapRoles materialKnown before).2 index
        (RawCtxGenericBeacon.reinstall ((mapRoles materialKnown before).2 index) control associatedData owner)) =
      (before.1, Function.update before.2 index (RawCtxGenericBeacon.reinstall (before.2 index) control associatedData
        (RawCtxGenericOwnerMap.mapOwner (RawCtxMaterialInterpretation.mapRefined (interpret key)) owner))) := by
  apply Prod.ext
  · funext other
    exact known_server key (before.1 other)
  · funext other
    by_cases same : other = index
    · subst other
      simp only [mapRoles, Function.update_self]
      rfl
    · simpa only [mapRoles, Function.update_of_ne same] using known_beacon key (before.2 other)

private theorem updated_server (key : RootOutput) (before : NativeFamily M P I D K S B)
    (index : Fin S) (server : ServerState RawCtxSelectedMessageReveals.Kernel M P) :
    mapRoles (RawCtxMaterialInterpretation.mapRefined (interpret key))
      (Function.update (mapRoles materialKnown before).1 index server, (mapRoles materialKnown before).2) =
      (Function.update before.1 index (mapServer (RawCtxMaterialInterpretation.mapRefined (interpret key)) server), before.2) := by
  apply Prod.ext
  · funext other
    by_cases same : other = index
    · subst other
      simp only [mapRoles, Function.update_self]
    · simpa only [mapRoles, Function.update_of_ne same] using known_server key (before.1 other)
  · funext other
    exact known_beacon key (before.2 other)

def serverEntry (context : ServerContext M P Result) (value : PqxdhOrderedChainHybrids.Material) : Entry :=
  ⟨serverAddress context, value⟩

private theorem quiet_server {Chain : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxPendingServerTails.SourceSpec Result) (quiet : client.IsTotalQueryBound 0)
    (before : RawCtxPendingServerTails.State Chain M P) :
    RawCtxPendingServerTails.program sender route read client before = pure (quietValue client quiet, before) :=
  congrArg (fun work => RawCtxPendingServerTails.program sender route read work before)
    (RawCtxQuietOwnerTails.zero_pure client quiet).choose_spec

noncomputable def server (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : ServerContext M P Result)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : RawCtxQuietServerTails.Quiet context) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Result × ServerState RawCtxSelectedMessageReveals.Kernel M P) :=
  match context with
  | .owner _ before kid peer outside inner =>
      (fun result => (quietValue (outside result.1) (quiet.1 result.1),
        ⟨RawCtxGenericServer.putPeer (mapServer materialKnown before).server kid (mapPeer materialKnown peer)
          result.2.kernel, result.2.rawAttempts⟩)) <$>
        RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner value quiet.2

/-- The entire saved Server frame consumes its literal response, publishes the same assigned peer and retains the original quiet outside result and full shared source state. -/
theorem server_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (context : ServerContext M P Result) (value : PqxdhOrderedChainHybrids.Material)
    (state : State A) (quiet : RawCtxQuietServerTails.Quiet context)
    (admitted : RawCtxForwardRoleScope.ServerValid read context) :
    (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) (serverEntry context value) target)
      ((serverFrame sender route read context).2
        (RawCtxSelectedFamilyNativeContext.serverReply sender route read context (realize (serverEntry context value) target)))).run
      (project state) =
      (fun result => ((result.1.1, mapServer (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (server source writer prior target nonce next read context value quiet)).run state := by
  cases context with
  | owner request before kid peer outside inner =>
      simp only [serverFrame, RawCtxSelectedFamilyNativeContext.serverReply,
        RawCtxPendingServerTails.liftOwner, simulateQ_bind, StateT.run_bind]
      have owned := RawCtxSelectedPendingOwnerCompiler.owner_source source writer prior key target nonce next
        read (sender before.server.metadata) inner value state quiet.2 admitted
      simp only [serverEntry, serverAddress, RawCtxSelectedPendingOwnerCompiler.entry] at owned ⊢
      rw [owned]
      simp only [bind_map_left, server, RawCtxSelectedReceiveCompiler.evaluated_map,
        StateT.run_map, Functor.map_map]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      simp only [RawCtxPendingServerTails.afterOwner, quiet_server sender route read _ (quiet.1 _),
        simulateQ_pure, StateT.run_pure, Function.comp_apply, RawCtxGenericOwnerMap.mapOwner]
      rw [RawCtxGenericServer.put_map]
      rw [known_server, known_peer]

def familyEntry (context : FamilyContext M P I D K Result S B) (value : PqxdhOrderedChainHybrids.Material) : Entry :=
  ⟨familyAddress context, value⟩

private theorem quiet_family {Chain : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) Result) (quiet : client.IsTotalQueryBound 0)
    (before : RawCtxPendingFamilyTails.State Chain M P I D K S B) :
    RawCtxPendingFamilyTails.program sender route read client before = pure (quietValue client quiet, before) :=
  congrArg (fun work => RawCtxPendingFamilyTails.program sender route read work before)
    (RawCtxQuietOwnerTails.zero_pure client quiet).choose_spec

noncomputable def family (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : FamilyContext M P I D K Result S B)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : RawCtxQuietFamilyTails.Quiet context) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Result × Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) :=
  match context with
  | .server _ before index outside inner =>
      (fun result => (quietValue (outside result.1) (quiet.1 result.1),
        (Function.update (mapRoles materialKnown before).1 index result.2, (mapRoles materialKnown before).2))) <$>
        server source writer prior target nonce next read inner value quiet.2
  | .beacon _ before index control associatedData outside inner =>
      (fun result => (quietValue (outside result.1) (quiet.1 result.1),
        ((mapRoles materialKnown before).1, Function.update (mapRoles materialKnown before).2 index
          (RawCtxGenericBeacon.reinstall ((mapRoles materialKnown before).2 index) control associatedData result.2)))) <$>
        RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner value quiet.2

/-- The actual saved Server or Beacon operation reinstalls precisely its returned role and retains every other peer, phase and source-cache field. -/
theorem family_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (context : FamilyContext M P I D K Result S B) (value : PqxdhOrderedChainHybrids.Material)
    (state : State A) (quiet : RawCtxQuietFamilyTails.Quiet context)
    (admitted : RawCtxForwardRoleScope.FamilyValid read context) :
    (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) (familyEntry context value) target)
      ((familyFrame sender route read context).2
        (RawCtxSelectedFamilyNativeContext.familyReply sender route read context (realize (familyEntry context value) target)))).run
      (project state) =
      (fun result => ((result.1.1, mapRoles (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (family source writer prior target nonce next read context value quiet)).run state := by
  cases context
  case beacon request before index control associatedData outside inner =>
    simp only [familyFrame, RawCtxSelectedFamilyNativeContext.familyReply,
      RawCtxPendingFamilyTails.liftBeacon, simulateQ_bind, StateT.run_bind]
    have owned := RawCtxSelectedPendingOwnerCompiler.owner_source source writer prior key target nonce next
      read (before.2 index).beacon.identityKeyId inner value state quiet.2 admitted
    simp only [familyEntry, familyAddress, RawCtxSelectedPendingOwnerCompiler.entry] at owned ⊢
    rw [owned]
    simp only [bind_map_left, family, RawCtxSelectedReceiveCompiler.evaluated_map,
      StateT.run_map, Functor.map_map]
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    simp only [RawCtxPendingFamilyTails.afterBeacon, quiet_family sender route read _ (quiet.1 _),
      simulateQ_pure, StateT.run_pure, Function.comp_apply]
    rw [updated_beacon]
  case server request before index outside inner =>
    simp only [familyFrame, RawCtxSelectedFamilyNativeContext.familyReply,
      RawCtxPendingFamilyTails.liftServer, simulateQ_bind, StateT.run_bind]
    have served := server_source source writer prior key target nonce next
      sender route read inner value state quiet.2 admitted
    simp only [familyEntry, familyAddress, serverEntry] at served ⊢
    rw [served]
    simp only [bind_map_left, family, RawCtxSelectedReceiveCompiler.evaluated_map,
      StateT.run_map, Functor.map_map]
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    simp only [RawCtxPendingFamilyTails.afterServer, quiet_family sender route read _ (quiet.1 _),
      simulateQ_pure, StateT.run_pure, Function.comp_apply]
    rw [updated_server]

def liveEntry (context : Context M P I D K Result S B) (value : PqxdhOrderedChainHybrids.Material) : Entry :=
  ⟨address context, value⟩

private theorem quiet_live {Chain : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxPendingFamilyLiveTails.SourceSpec S B) Result) (quiet : client.IsTotalQueryBound 0)
    (before : RawCtxPendingFamilyLiveQueries.State Chain M P I D K S B) :
    RawCtxPendingFamilyLiveTails.program sender route read client before = pure (quietValue client quiet, before) :=
  congrArg (fun work => RawCtxPendingFamilyLiveTails.program sender route read work before)
    (RawCtxQuietOwnerTails.zero_pure client quiet).choose_spec

noncomputable def live (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : PqxdhInitialPostCertificates.LiveQuiet context) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Result × RawCtxGenericFamilyLive.State RawCtxSelectedMessageReveals.Kernel M P I D K S B) :=
  match context with
  | .family _ history outside inner =>
      (fun result => (quietValue (outside result.1) (quiet.1 result.1),
        (result.2, RawCtxProtocolReveals.tick history))) <$>
        family source writer prior target nonce next read inner value quiet.2

/-- Completing the literal record descriptor preserves its actual family and advances the saved LIVE history once, before returning the original quiet continuation's result. -/
theorem live_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (value : PqxdhOrderedChainHybrids.Material)
    (state : State A) (quiet : PqxdhInitialPostCertificates.LiveQuiet context)
    (admitted : RawCtxForwardRoleScope.LiveValid read context) :
    (simulateQ (RawCtxSelectedParentFamilyMap.nativeLive source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) (liveEntry context value) target)
      ((frame sender route read context).2
        (RawCtxSelectedFamilyNativeContext.reply sender route read context (realize (liveEntry context value) target)))).run
      (project state) =
      (fun result => ((result.1.1, RawCtxGenericFamilyLive.mapState
        (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (live source writer prior target nonce next read context value quiet)).run state := by
  cases context with
  | family request history outside inner =>
      simp only [frame, RawCtxSelectedFamilyNativeContext.reply, RawCtxPendingFamilyLiveTails.liftFamily,
        simulateQ_bind, ← QueryImpl.simulateQ_compose, RawCtxSelectedParentFamilyMap.nativeLive,
        RawCtxPendingFamilyLiveQueries.primitive_handler, StateT.run_bind]
      have completed := family_source source writer prior key target nonce next
        sender route read inner value state quiet.2 admitted
      simp only [liveEntry, address, familyEntry] at completed ⊢
      rw [completed]
      simp only [bind_map_left, live, RawCtxSelectedReceiveCompiler.evaluated_map,
        StateT.run_map, Functor.map_map]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      simp only [RawCtxPendingFamilyLiveTails.afterFamily, quiet_live sender route read _ (quiet.1 _),
        simulateQ_pure, StateT.run_pure, Function.comp_apply, RawCtxGenericFamilyLive.mapState]

/-- Reinstalling the exact peer and returning its quiet continuation adds no dynamic requests to the complete pending-owner allowance. -/
theorem server_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : ServerContext M P Result)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : RawCtxQuietServerTails.Quiet context) :
    (server source writer prior target nonce next read context value quiet).IsTotalQueryBound 1 := by
  cases context with
  | owner request before kid peer outside inner =>
      simpa only [server, IsTotalQueryBound, isQueryBound_map_iff] using
        RawCtxSelectedPendingOwnerCompiler.owner_queries source writer prior target nonce next read inner value quiet.2

/-- Either saved role operation has at most one dynamic request under every reply, including its exact role-family publication. -/
theorem family_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : FamilyContext M P I D K Result S B)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : RawCtxQuietFamilyTails.Quiet context) :
    (family source writer prior target nonce next read context value quiet).IsTotalQueryBound 1 := by
  cases context
  case server request before index outside inner =>
    simpa only [family, IsTotalQueryBound, isQueryBound_map_iff] using
      server_queries source writer prior target nonce next read inner value quiet.2
  case beacon request before index control associatedData outside inner =>
    simpa only [family, IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedPendingOwnerCompiler.owner_queries source writer prior target nonce next read inner value quiet.2

/-- The complete saved single-record LIVE frame retains the one-request dynamic cap; prefix lookup costs and the later adaptive Post program remain separate bills. -/
theorem live_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B)
    (value : PqxdhOrderedChainHybrids.Material) (quiet : PqxdhInitialPostCertificates.LiveQuiet context) :
    (live source writer prior target nonce next read context value quiet).IsTotalQueryBound 1 := by
  cases context with
  | family request history outside inner =>
      simpa only [live, IsTotalQueryBound, isQueryBound_map_iff] using
        family_queries source writer prior target nonce next read inner value quiet.2

end BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.server_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.family_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.family_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.live_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.live_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.server_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.server_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.family_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.family_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.live_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler.live_queries
