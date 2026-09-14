import BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation
import BeaconcryptCore.Computational.RawCtxGenericFamilyRead
import BeaconcryptCore.Computational.RawCtxGenericFamilyLive
import BeaconcryptCore.Computational.RawCtxPendingFamilyTails

/-!
The actual whole-family live client forwards complete original role programs through one enriched pending primitive interface. A live-read query contains the original request and actual optional selected kernel; its original optional response is recorded in the unchanged timestamped history. Only private query arguments carry kernels. No unavailable target is added to the client, and these operational equations do not assert freshness or secrecy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries
open RawCtxGenericRoleFamily RawCtxGenericFamilyRead RawCtxProtocolReveals

abbrev Kernel := RawCtxPendingOwnerQueries.Kernel
abbrev Spec (Chain : Type) (serverCount beaconCount : Nat) :=
  RawCtxPendingOwnerQueries.Spec Chain + ReadSpec (Kernel Chain) serverCount beaconCount
abbrev State (Chain Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  RawCtxPendingFamilyTails.State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
    History serverCount beaconCount

def primitiveForward {Chain : Type} {serverCount beaconCount : Nat} :
    QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (OracleComp (Spec Chain serverCount beaconCount)) :=
  fun query => (Spec Chain serverCount beaconCount).query (.inl query)

noncomputable def compiler {Chain Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec serverCount beaconCount)
      (StateT (State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
        (OracleComp (Spec Chain serverCount beaconCount))) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ primitiveForward
        ((RawCtxGenericFamilyFrontend.impl RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward
          sender route decode request).run state.1)
      pure (result.1, (result.2, tick state.2))
  | .inr request => do
      let reply ← (Spec Chain serverCount beaconCount).query
        (.inr (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1))
      pure (reply, (state.1, note ⟨request, reply⟩ state.2))

def handler {Chain : Type} {serverCount beaconCount : Nat} {m : Type → Type*}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (ReadSpec (Kernel Chain) serverCount beaconCount) m) :
    QueryImpl (Spec Chain serverCount beaconCount) m
  | .inl query => primitive query
  | .inr query => reader query

/-- Forwarding a private role callback preserves that exact callback, including its complete ambient effect. -/
theorem primitive_handler {Chain : Type} {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (ReadSpec (Kernel Chain) serverCount beaconCount) m) :
    handler primitive reader ∘ₛ primitiveForward = primitive := by
  funext query
  simp [QueryImpl.compose, primitiveForward, handler, OracleSpec.query]

/-- One whole original live operation uses the same interpreted pending calls and reader while preserving complete role state and original history. -/
theorem step_interpretation {Chain Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (ReadSpec (Kernel Chain) serverCount beaconCount) m)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ (handler primitive reader) ((compiler sender route decode query).run state) =
      (RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
        sender route decode query).run state := by
  cases query with
  | inl request =>
    simp only [compiler, RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp, simulateQ_map]
    rw [← QueryImpl.simulateQ_compose, primitive_handler]
    have interpreted := RawCtxGenericFamilyInterpretation.step_interpretation primitive
      RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward sender route decode request state.1
    simp only [StateT.run] at interpreted
    rw [interpreted]
  | inr request =>
    simp only [compiler, RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, handler]
    rfl

/-- Every complete adaptive role/public/live-read execution retains its original optional replies, full family, history and shared callback effects. -/
theorem program_interpretation {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (ReadSpec (Kernel Chain) serverCount beaconCount) m)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ (handler primitive reader) ((simulateQ (compiler sender route decode) client).run state) =
      (simulateQ (RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
        sender route decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [step_interpretation]
    exact bind_congr fun result => ih result.1 result.2

end BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.primitive_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.primitive_handler

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.step_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.step_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.program_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.program_interpretation
