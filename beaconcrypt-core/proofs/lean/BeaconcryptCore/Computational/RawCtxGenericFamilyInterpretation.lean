import BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend
import BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation

/-!
The same oracle interpreter commutes with the original generic Server, Beacon and full finite-family frontends. Its receive/send and public programs retain all replies and complete effects. These equations only reorganize the same source interpretation and introduce no callback-compatibility, freshness or security premise. They let the original pending/live compiler retain an entire family through concrete primitive forwarding.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxGenericOwnerInterpretation

private theorem server_raw {Kernel Metadata PeerMetadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ primitive (RawCtxGenericServer.rawServer calls route decode raw state) =
      RawCtxGenericServer.rawServer (interpretedCalls primitive calls) route decode raw state := by
  cases routed : route raw with
  | some kid =>
    cases found : state.server.peers kid <;>
      simp [RawCtxGenericServer.rawServer, routed, RawCtxGenericServer.peerAssociatedData, found,
        RawCtxGenericOwnerInterpretation.raw_interpretation]
  | none => simp [RawCtxGenericServer.rawServer, routed]

private theorem server_send {Kernel Metadata PeerMetadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (sender : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ primitive (RawCtxGenericServer.sendServer calls sender plaintext kid state) =
      RawCtxGenericServer.sendServer (interpretedCalls primitive calls) sender plaintext kid state := by
  cases found : state.server.peers kid <;>
    simp [RawCtxGenericServer.sendServer, RawCtxGenericServer.peerAssociatedData, found,
      RawCtxGenericOwnerInterpretation.send_interpretation]

/-- The original Server frontend commutes with the same complete receive/send interpreter without a compatibility premise. -/
theorem server_interpretation {Kernel Metadata PeerMetadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ primitive ((RawCtxGenericServer.serverImpl calls sender route decode query).run state) =
      (RawCtxGenericServer.serverImpl (interpretedCalls primitive calls) sender route decode query).run state := by
  cases query with
  | inl request => exact server_send primitive calls sender request.1 request.2 state
  | inr raw => exact server_raw primitive calls route decode raw state

/-- The same interpreter preserves every active or inactive original Beacon branch and complete optional result. -/
theorem beacon_interpretation {Kernel Identity DhPair KemPair ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    simulateQ primitive ((RawCtxGenericBeacon.impl calls decode query).run state) =
      (RawCtxGenericBeacon.impl (interpretedCalls primitive calls) decode query).run state := by
  cases phase : state.beacon.phase
  case established control associatedData kernel =>
    have interpreted := RawCtxGenericOwnerInterpretation.owner_interpretation primitive calls
      state.beacon.identityKeyId decode query (RawCtxGenericBeacon.selected state control associatedData kernel)
    simp only [StateT.run] at interpreted
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, bind_pure_comp, simulateQ_map]
    rw [interpreted]
  all_goals simp [RawCtxGenericBeacon.impl, StateT.run, phase]

/-- One indexed role or public operation interprets exactly the same callbacks and preserves the entire family. -/
theorem step_interpretation {Kernel Metadata PeerMetadata Identity DhPair KemPair ι : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ primitive ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run state) =
      (RawCtxGenericFamilyFrontend.impl (interpretedCalls primitive calls)
        (fun request => simulateQ primitive (publicCalls request)) sender route decode query).run state := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · have interpreted := server_interpretation primitive calls sender route decode request (state.1 index)
    simp only [StateT.run] at interpreted
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp, simulateQ_map]
    rw [interpreted]
  · have interpreted := beacon_interpretation primitive calls decode request (state.2 index)
    simp only [StateT.run] at interpreted
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp, simulateQ_map]
    rw [interpreted]
  · simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp, simulateQ_map]

/-- The complete adaptive role/public client uses the same separately interpreted callbacks before any state or result projection. -/
theorem schedule_interpretation {Kernel Metadata PeerMetadata Identity DhPair KemPair Result ι : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl spec m) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec serverCount beaconCount) Result)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ primitive ((simulateQ (RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode) client).run state) =
      (simulateQ (RawCtxGenericFamilyFrontend.impl (interpretedCalls primitive calls)
        (fun request => simulateQ primitive (publicCalls request)) sender route decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [step_interpretation]
    exact bind_congr fun result => ih result.1 result.2

end BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.server_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.server_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.beacon_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.beacon_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.step_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.step_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation.schedule_interpretation
