import BeaconcryptCore.Computational.RawCtxPendingNativeCalls
import BeaconcryptCore.Computational.RawCtxGenericFamilyNative
import BeaconcryptCore.Computational.RawCtxSelectedFamilyContext

/-!
The original complete native family and live-reveal source is exactly the enriched pending program under any mutable native backend. All original roles, optional replies and reveal history survive the native/refined projection, while the backend retains its entire private table, cursor, hash cache and other state. No fixed-source consistency or pending-call realization premise is supplied. The material-only context and state-dependent selected sampler are subsequent consumers of this exact execution equality.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingFamilyNative

noncomputable def handler {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m]
    (backend : QueryImpl RawCtxServerServices.BackendSpec m) :=
  RawCtxPendingFamilyLiveQueries.handler
    (RawCtxPendingNativeCalls.pending (backend ∘ₛ RawCtxServerServices.nativeLift)
      (backend ∘ₛ RawCtxServerServices.publicLift))
    (RawCtxGenericFamilyRead.nativeReader (serverCount := serverCount) (beaconCount := beaconCount) ConcreteRatchetKernel.mk)

/-- The enriched complete family program runs the exact native calls, public services and original optional live reader in the same arbitrary backend monad. -/
theorem program_interpretation {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxPendingFamilyLiveQueries.State RatchetChain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ (handler backend) (RawCtxPendingFamilyLiveTails.program sender route decode client state) =
      (simulateQ (RawCtxGenericFamilyLive.impl
        (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift))
        (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
        sender route decode) client).run state := by
  have actual := RawCtxPendingFamilyLiveQueries.program_interpretation
    (RawCtxPendingNativeCalls.pending (backend ∘ₛ RawCtxServerServices.nativeLift)
      (backend ∘ₛ RawCtxServerServices.publicLift))
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode client state
  rw [RawCtxPendingNativeCalls.calls_interpretation, RawCtxPendingNativeCalls.public_interpretation] at actual
  exact actual

/-- The actual original full live source equals the same enriched source execution, preserving the complete native family and all mutable backend effects. -/
theorem actual {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ backend ((simulateQ (RawCtxProtocolReveals.protocolImpl serverCount beaconCount sender route decode) client).run state) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk) <$>
        simulateQ (handler backend) (RawCtxPendingFamilyLiveTails.program sender route decode client
          (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)) := by
  rw [program_interpretation]
  exact RawCtxGenericFamilyNative.actual backend sender route decode client state

end BeaconcryptCore.Computational.RawCtxPendingFamilyNative

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyNative.program_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyNative.program_interpretation
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyNative.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyNative.actual
