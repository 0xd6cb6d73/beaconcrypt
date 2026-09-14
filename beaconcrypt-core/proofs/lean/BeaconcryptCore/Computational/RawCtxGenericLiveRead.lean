import BeaconcryptCore.Computational.RawCtxPendingLiveQueries

/-!
The same live read frontend is parameterized by the private current-chain representation. It retains the original optional native-chain/material reply types, complete owner and history state, and a supplied operational exposure test. Native-byte and selected-slot instantiations use the same source query schedule; the selected exposure test does not become a secret-byte argument to the frontend. This module establishes exact interfaces and source-read equations, not a security or freshness assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericLiveRead
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace

abbrev ReadInput (Chain : Type) := Read × Option (RawCtxPendingOwnerQueries.Kernel Chain)
def ReadQueries (Chain : Type) : OracleSpec (ReadInput Chain) := fun query => ReadSpec.Range query.1
abbrev Spec (Chain : Type) := RawCtxPendingOwnerQueries.Spec Chain + ReadQueries Chain
abbrev OuterState (Chain Metadata : Type) (serverCount beaconCount : Nat) :=
  (RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) Metadata ×
    RawCtxProtocolReveals.History serverCount beaconCount) × Bool
abbrev Reader (Chain : Type) := (read : Read) → Option (RawCtxPendingOwnerQueries.Kernel Chain) → ReadSpec.Range read
abbrev Exposure (Chain : Type) := Read → Option (RawCtxPendingOwnerQueries.Kernel Chain) → Bool

def primitiveForward {Chain : Type} : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (OracleComp (Spec Chain)) :=
  fun query => (Spec Chain).query (.inl query)

noncomputable def compiler {Chain Metadata : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (OuterState Chain Metadata serverCount beaconCount) (OracleComp (Spec Chain))) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ primitiveForward ((RawCtxPendingOwnerQueries.compiler sender decode request).run state.1.1)
      pure (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))
  | .inr read => do
      let entry := some state.1.1.kernel
      let reply ← (Spec Chain).query (.inr (read, entry))
      pure (reply, ((state.1.1, RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
        state.2 || exposure read entry))

/-- Instantiating private selected slots gives exactly the existing retained live frontend, including its exposure bit. -/
theorem slot_compiler {Metadata : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    compiler (Metadata := Metadata) RawCtxSelectedLiveRead.exposed sender decode owner =
      RawCtxPendingLiveQueries.compiler sender decode owner := by
  rfl

noncomputable def nativeReader : Reader RatchetChain :=
  fun read entry => nativeRead read (entry.map (fun kernel => (⟨kernel⟩ : ConcreteRatchetKernel)))

/-- Native-byte kernels retain the exact existing optional chain/skipped-material lookup, including malformed slots. -/
theorem native_reader (read : Read) (entry : Option ConcreteRatchetKernel) :
    nativeReader read (entry.map ConcreteRatchetKernel.refined) = nativeRead read entry := by
  cases entry <;> rfl

/-- The generic native reader is exactly the actual selected-role source read with its original history and full shared poststate. -/
theorem native_source_forward {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (read : Read)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) ∘ₛ
      RawCtxSelectedLiveRead.forward owner) read).run state =
      pure (nativeReader read ((RawCtxProtocolReveals.selectedKernel owner state.1.1).map ConcreteRatchetKernel.refined),
        ((state.1.1, RawCtxProtocolReveals.note (observation owner read
          (nativeReader read ((RawCtxProtocolReveals.selectedKernel owner state.1.1).map ConcreteRatchetKernel.refined)))
          state.1.2), state.2)) := by
  simpa only [native_reader] using RawCtxSelectedLiveRead.source_forward source writer senderId route decode owner read state

noncomputable def handler {Chain Base : Type}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (StateT Base ProbComp))
    (reader : Reader Chain) : QueryImpl (Spec Chain) (StateT Base ProbComp)
  | .inl query => primitive query
  | .inr query => pure (reader query.1 query.2)

/-- One compiled read retains the actual reply, complete owner/history state and the operational exposure bit. -/
theorem read_step {Chain Metadata Base : Type} {serverCount beaconCount : Nat}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (StateT Base ProbComp))
    (reader : Reader Chain) (exposure : Exposure Chain) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (read : Read) (state : OuterState Chain Metadata serverCount beaconCount) :
    simulateQ (handler primitive reader) ((compiler exposure sender decode owner (.inr read)).run state) =
      pure (reader read (some state.1.1.kernel),
        ((state.1.1, RawCtxProtocolReveals.note (observation owner read (reader read (some state.1.1.kernel))) state.1.2),
          state.2 || exposure read (some state.1.1.kernel))) := by
  simp [compiler, handler, StateT.run, OracleSpec.query]

/-- Adding live reads leaves every full pending primitive callback and all of its effects unchanged. -/
theorem primitive_handler {Chain Base : Type}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (StateT Base ProbComp))
    (reader : Reader Chain) : handler primitive reader ∘ₛ primitiveForward = primitive := by
  funext query
  exact _root_.simulateQ_spec_query (handler primitive reader) (.inl query)

/-- Every attempted live read issues exactly its one typed callback; optional rejection does not remove the attempt. -/
theorem read_total {Chain Metadata : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (read : Read)
    (state : OuterState Chain Metadata serverCount beaconCount) :
    ((compiler exposure sender decode owner (.inr read)).run state).IsTotalQueryBound 1 := by
  exact ⟨Nat.zero_lt_succ 0, fun _ => trivial⟩

/-- The read interpreter makes no uniform request; native lookup, comparison, logging and copying remain deterministic local work. -/
theorem read_uniform {Chain Base : Type}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (StateT Base ProbComp))
    (reader : Reader Chain) (query : ReadInput Chain) (state : Base) :
    ((handler primitive reader (.inr query)).run state).IsTotalQueryBound 0 := by
  trivial

/-- Every original public/record step retains the complete pending-owner computation and advances only the live-history timestamp. -/
theorem original_step {Chain Metadata Base : Type} {serverCount beaconCount : Nat}
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (StateT Base ProbComp))
    (reader : Reader Chain) (exposure : Exposure Chain) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (request : RawCtxSelectedPublicTrace.SourceSpec.Domain)
    (state : OuterState Chain Metadata serverCount beaconCount) :
    simulateQ (handler primitive reader) ((compiler exposure sender decode owner (.inl request)).run state) =
      (fun result => (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$>
        simulateQ primitive ((RawCtxPendingOwnerQueries.compiler sender decode request).run state.1.1) := by
  simp only [compiler, StateT.run, bind_pure_comp, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, primitive_handler]
  rfl

end BeaconcryptCore.Computational.RawCtxGenericLiveRead

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.slot_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.slot_compiler

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.native_reader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.native_reader

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.native_source_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.native_source_forward

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.primitive_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.primitive_handler

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_total

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.read_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericLiveRead.original_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericLiveRead.original_step
