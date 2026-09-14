import BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails
import BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut

/-!
A concrete selected context retains the original owner, Server, entire role family and live-history continuations as typed original source clients. Its pending receive/send is obtained from the actual source grammar. The stopped program accepts only the retained material coordinate: it retags all saved pre-draw kernels as known and installs the new hidden chain only at the selected pending resume. No arbitrary native function, target value or target-free family-state premise is stored in the context.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedChain
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

abbrev OwnerSpec := RawCtxSelectedPublicTrace.SourceSpec
abbrev ServerSpec := RawCtxServerMixed.SourceSpec
abbrev FamilySpec := RawCtxProtocolRoles.SourceSpec
abbrev LiveSpec := RawCtxProtocolReveals.SourceSpec
abbrev PrimitiveSpec := RawCtxPendingOwnerQueries.Spec
abbrev LivePrimitiveSpec := RawCtxPendingFamilyLiveQueries.Spec
abbrev NativeOwner := RawCtxPendingOwnerTails.Owner RatchetChain
abbrev NativeServer := RawCtxPendingServerTails.State RatchetChain
abbrev NativeFamily := RawCtxPendingFamilyTails.State RatchetChain
abbrev NativeLive := RawCtxPendingFamilyLiveQueries.State RatchetChain

inductive OwnerContext (Metadata Result : Type) : Type where
  | receive (before : NativeOwner Metadata)
      (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp OwnerSpec Result)
      (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
  | send (before : NativeOwner Metadata)
      (outside : Option RawCtxSourceSend.Encrypted → OracleComp OwnerSpec Result)
      (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)

inductive ServerContext (Metadata PeerMetadata Result : Type) : Type where
  | owner (request : RawCtxMixedOwner.SourceSpec.Domain)
      (before : NativeServer Metadata PeerMetadata) (kid : Std.U64)
      (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) PeerMetadata)
      (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp ServerSpec Result)
      (inner : OwnerContext PeerMetadata (RawCtxMixedOwner.SourceSpec.Range request))

inductive FamilyContext (Metadata PeerMetadata Identity DhPair KemPair Result : Type) (serverCount beaconCount : Nat) : Type where
  | server (request : ServerSpec.Domain)
      (before : NativeFamily Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin serverCount)
      (outside : ServerSpec.Range request → OracleComp (FamilySpec serverCount beaconCount) Result)
      (inner : ServerContext Metadata PeerMetadata (ServerSpec.Range request))
  | beacon (request : RawCtxMixedOwner.SourceSpec.Domain)
      (before : NativeFamily Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin beaconCount)
      (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
      (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (FamilySpec serverCount beaconCount) Result)
      (inner : OwnerContext Unit (RawCtxMixedOwner.SourceSpec.Range request))

inductive Context (Metadata PeerMetadata Identity DhPair KemPair Result : Type) (serverCount beaconCount : Nat) : Type where
  | family (request : (FamilySpec serverCount beaconCount).Domain)
      (history : RawCtxProtocolReveals.History serverCount beaconCount)
      (outside : (FamilySpec serverCount beaconCount).Range request → OracleComp (LiveSpec serverCount beaconCount) Result)
      (inner : FamilyContext Metadata PeerMetadata Identity DhPair KemPair
        ((FamilySpec serverCount beaconCount).Range request) serverCount beaconCount)

abbrev OwnerFrame (Metadata Result : Type) :=
  Σ query, (PrimitiveSpec RatchetChain).Range query → OracleComp (PrimitiveSpec RatchetChain) (Result × NativeOwner Metadata)
abbrev ServerFrame (Metadata PeerMetadata Result : Type) :=
  Σ query, (PrimitiveSpec RatchetChain).Range query → OracleComp (PrimitiveSpec RatchetChain) (Result × NativeServer Metadata PeerMetadata)
abbrev FamilyFrame (Metadata PeerMetadata Identity DhPair KemPair Result : Type) (serverCount beaconCount : Nat) :=
  Σ query, (PrimitiveSpec RatchetChain).Range query → OracleComp (PrimitiveSpec RatchetChain)
    (Result × NativeFamily Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
abbrev Frame (Metadata PeerMetadata Identity DhPair KemPair Result : Type) (serverCount beaconCount : Nat) :=
  Σ query, (LivePrimitiveSpec RatchetChain serverCount beaconCount).Range query →
    OracleComp (LivePrimitiveSpec RatchetChain serverCount beaconCount)
      (Result × NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)

noncomputable def ownerFrame {Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    OwnerContext Metadata Result → OwnerFrame Metadata Result
  | .receive before outside pending => ⟨.inl (.inl pending), RawCtxPendingOwnerTails.receiveTail sender decode before outside pending⟩
  | .send before outside pending => ⟨.inr (.inl (.inl pending)), RawCtxPendingOwnerTails.sendTail sender decode before outside pending⟩

noncomputable def serverFrame {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    ServerContext Metadata PeerMetadata Result → ServerFrame Metadata PeerMetadata Result
  | .owner _ before kid peer outside inner =>
      let saved := ownerFrame (sender before.server.metadata) decode inner
      ⟨saved.1, fun reply => RawCtxPendingServerTails.liftOwner sender route decode before kid peer outside (saved.2 reply)⟩

noncomputable def familyFrame {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    FamilyContext Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount →
      FamilyFrame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount
  | .server _ before index outside inner =>
      let saved := serverFrame sender route decode inner
      ⟨saved.1, fun reply => RawCtxPendingFamilyTails.liftServer sender route decode before index outside (saved.2 reply)⟩
  | .beacon _ before index control associatedData outside inner =>
      let saved := ownerFrame (before.2 index).beacon.identityKeyId decode inner
      ⟨saved.1, fun reply => RawCtxPendingFamilyTails.liftBeacon sender route decode before index control associatedData outside (saved.2 reply)⟩

noncomputable def frame {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount →
      Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount
  | .family _ history outside inner =>
      let saved := familyFrame sender route decode inner
      ⟨.inl saved.1, fun reply => RawCtxPendingFamilyLiveTails.liftFamily sender route decode history outside (saved.2 reply)⟩

def ownerAddress {Metadata Result : Type} : OwnerContext Metadata Result → JointKdfAddress
  | .receive _ _ pending => RawCtxSelectedPendingCut.requestAddress pending.request
  | .send _ _ pending => RawCtxSelectedPendingCut.requestAddress pending.request

def serverAddress {Metadata PeerMetadata Result : Type} : ServerContext Metadata PeerMetadata Result → JointKdfAddress
  | .owner _ _ _ _ _ inner => ownerAddress inner

def familyAddress {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat} :
    FamilyContext Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount → JointKdfAddress
  | .server _ _ _ _ inner => serverAddress inner
  | .beacon _ _ _ _ _ _ inner => ownerAddress inner

def address {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat} :
    Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount → JointKdfAddress
  | .family _ _ _ inner => familyAddress inner

def knownKernel : RawCtxPendingOwnerQueries.Kernel RatchetChain → RawCtxPendingOwnerQueries.Kernel Slot := RawCtxChainInterpretation.mapChains Slot.known Slot.known

noncomputable def ownerStopped {Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (context : OwnerContext Metadata Result) (value : Material) :
    OracleComp (PrimitiveSpec Slot) (Result × RawCtxPendingOwnerTails.Owner Slot Metadata) :=
  match context with
  | .receive before outside pending => RawCtxSelectedParentOwnerCut.receiveStop sender decode before outside pending value
  | .send before outside pending => RawCtxSelectedParentOwnerCut.sendStop sender decode before outside pending value

noncomputable def serverStopped {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : ServerContext Metadata PeerMetadata Result) (value : Material) :
    OracleComp (PrimitiveSpec Slot) (Result × RawCtxPendingServerTails.State Slot Metadata PeerMetadata) :=
  match context with
  | .owner _ before kid peer outside inner =>
      RawCtxPendingServerTails.liftOwner sender route decode (mapServer knownKernel before) kid (mapPeer knownKernel peer) outside
        (ownerStopped (sender before.server.metadata) decode inner value)

noncomputable def familyStopped {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : FamilyContext Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) (value : Material) :
    OracleComp (PrimitiveSpec Slot)
      (Result × RawCtxPendingFamilyTails.State Slot Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  match context with
  | .server _ before index outside inner =>
      RawCtxPendingFamilyTails.liftServer sender route decode (mapRoles knownKernel before) index outside
        (serverStopped sender route decode inner value)
  | .beacon _ before index control associatedData outside inner =>
      RawCtxPendingFamilyTails.liftBeacon sender route decode (mapRoles knownKernel before) index control associatedData outside
        (ownerStopped (before.2 index).beacon.identityKeyId decode inner value)

noncomputable def stopped {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) (value : Material) :
    OracleComp (LivePrimitiveSpec Slot serverCount beaconCount)
      (Result × RawCtxPendingFamilyLiveQueries.State Slot Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  match context with
  | .family _ history outside inner =>
      RawCtxPendingFamilyLiveTails.liftFamily sender route decode history outside (familyStopped sender route decode inner value)

/-- Every selected tail of the original complete LIVE family program has a context made solely from its original typed source frames. -/
theorem tail_context {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (LivePrimitiveSpec RatchetChain serverCount beaconCount).Domain)
    (next : (LivePrimitiveSpec RatchetChain serverCount beaconCount).Range query →
      OracleComp (LivePrimitiveSpec RatchetChain serverCount beaconCount)
        (Result × NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (tail : RawCtxPendingFamilyLiveTails.Tail sender route decode query next) :
    ∃ context : Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        frame sender route decode context := by
  cases tail with
  | original familyRequest history liveOutside query familyNext familyOrigin =>
    cases familyOrigin with
    | server serverRequest beforeFamily index familyOutside query serverNext serverOrigin =>
      cases serverOrigin with
      | original ownerRequest beforeServer kid peer serverOutside query ownerNext ownerOrigin =>
        cases ownerOrigin with
        | receive beforeOwner ownerOutside pending =>
          exact ⟨.family familyRequest history liveOutside
            (.server serverRequest beforeFamily index familyOutside
              (.owner ownerRequest beforeServer kid peer serverOutside
                (.receive beforeOwner ownerOutside pending))), rfl⟩
        | send beforeOwner ownerOutside pending =>
          exact ⟨.family familyRequest history liveOutside
            (.server serverRequest beforeFamily index familyOutside
              (.owner ownerRequest beforeServer kid peer serverOutside
                (.send beforeOwner ownerOutside pending))), rfl⟩
    | beacon ownerRequest beforeFamily index control associatedData familyOutside query ownerNext ownerOrigin =>
      cases ownerOrigin with
      | receive beforeOwner ownerOutside pending =>
        exact ⟨.family familyRequest history liveOutside
          (.beacon ownerRequest beforeFamily index control associatedData familyOutside
            (.receive beforeOwner ownerOutside pending)), rfl⟩
      | send beforeOwner ownerOutside pending =>
        exact ⟨.family familyRequest history liveOutside
          (.beacon ownerRequest beforeFamily index control associatedData familyOutside
            (.send beforeOwner ownerOutside pending)), rfl⟩

def primitiveAddress : (PrimitiveSpec RatchetChain).Domain → Option JointKdfAddress
  | .inl (.inl pending) => some (RawCtxSelectedPendingCut.requestAddress pending.request)
  | .inr (.inl (.inl pending)) => some (RawCtxSelectedPendingCut.requestAddress pending.request)
  | _ => none

def queryAddress {serverCount beaconCount : Nat} : (LivePrimitiveSpec RatchetChain serverCount beaconCount).Domain → Option JointKdfAddress
  | .inl query => primitiveAddress query
  | .inr _ => none

/-- The context address is the same complete original request carried by its saved source frame. -/
theorem frame_address {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) :
    queryAddress (frame sender route decode context).1 = some (address context) := by
  cases context with
  | family request history outside inner =>
    cases inner with
    | server request before index outside inner =>
      cases inner with
      | owner request before kid peer outside inner => cases inner <;> rfl
    | beacon request before index control associatedData outside inner => cases inner <;> rfl

/-- A supported original-index scan of the actual complete LIVE family source derives its concrete material-only context and original pending address, retaining the same reached mutable backend state. -/
theorem reached_context {Metadata PeerMetadata Identity DhPair KemPair Result PrimitiveState : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (LiveSpec serverCount beaconCount) Result)
    (state : NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (impl : QueryImpl (LivePrimitiveSpec RatchetChain serverCount beaconCount) (StateT PrimitiveState ProbComp))
    (index : Nat) (initial reached : PrimitiveState)
    (query : (LivePrimitiveSpec RatchetChain serverCount beaconCount).Domain)
    (next : (LivePrimitiveSpec RatchetChain serverCount beaconCount).Range query →
      OracleComp (LivePrimitiveSpec RatchetChain serverCount beaconCount)
        (Result × NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxPendingMixedPrefix.scan RawCtxPendingFamilyLiveTails.selected impl
        (RawCtxPendingFamilyLiveTails.program sender route decode client state) index initial)) :
    ∃ context : Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        frame sender route decode context ∧ queryAddress query = some (address context) := by
  obtain ⟨context, same⟩ := tail_context sender route decode query next
    (RawCtxPendingFamilyLiveTails.reached_tail sender route decode client state impl index initial reached query next supported)
  refine ⟨context, same, ?_⟩
  have sameQuery := congrArg Sigma.fst same
  change query = (frame sender route decode context).1 at sameQuery
  rw [sameQuery]
  exact frame_address sender route decode context

end BeaconcryptCore.Computational.RawCtxSelectedFamilyContext

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.tail_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.tail_context
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.frame_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.frame_address
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyContext.reached_context
