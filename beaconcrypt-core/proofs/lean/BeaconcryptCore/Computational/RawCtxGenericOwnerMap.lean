import BeaconcryptCore.Computational.RawCtxChainOwner

/-!
Changing only the private kernel representation commutes with the original established-owner adapter whenever the two concrete receive and send calls commute with that representation. The hypotheses are complete functional call equations in the same lawful monad, preserving all callback effects and optional replies; they are not distribution, freshness or security assumptions. The consuming retained-parent interpreter discharges these equations using its actual source calls. Empty sends, all raw rejection paths, successful publication, metadata, associated data, expected sender and attempted-receive counts remain present.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericOwnerMap
open RawCtxChainOwner

def mapOwner {Kernel Other Metadata : Type} (interpret : Kernel → Other)
    (state : State Kernel Metadata) : State Other Metadata :=
  ⟨interpret state.kernel, state.expectedSender, state.associatedData, state.metadata, state.rawAttempts⟩

/-- Every raw rejection and publication path changes only the kernel representation, retaining the actual attempts and complete effects. -/
theorem raw_map {Kernel Other Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : Calls Kernel m) (otherCalls : Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : State Kernel Metadata) :
    (rawReceive otherCalls decode raw).run (mapOwner interpret state) =
      Prod.map id (mapOwner interpret) <$> (rawReceive calls decode raw).run state := by
  simp only [rawReceive, mapOwner, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp only [empty, ite_true, map_pure, publish, Prod.map_def, id_eq, mapOwner]
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : decode raw with
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
      · simp only [valid, ite_true, bind_pure_comp]
        rw [receiveMap, Functor.map_map, Functor.map_map]
        rfl
      · simp only [valid, ite_false, map_pure, publish, Prod.map_def, id_eq, mapOwner]
    | none => simp only [map_pure, publish, Prod.map_def, id_eq, mapOwner]

/-- Empty sends reject before callbacks; all other send outcomes retain their actual post-kernel and every owner field. -/
theorem send_map {Kernel Other Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : Calls Kernel m) (otherCalls : Calls Other m)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (state : State Kernel Metadata) :
    (sendOwner otherCalls sender plaintext).run (mapOwner interpret state) =
      Prod.map id (mapOwner interpret) <$> (sendOwner calls sender plaintext).run state := by
  simp only [sendOwner, mapOwner, StateT.run]
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, ite_true, map_pure, Prod.map_def, id_eq, mapOwner]
  · simp only [empty, Bool.false_eq_true, ite_false, bind_pure_comp]
    rw [sendMap, Functor.map_map, Functor.map_map]
    rfl

/-- The original mixed send/raw query and optional response types are unchanged under the private owner map. -/
theorem owner_map {Kernel Other Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : Calls Kernel m) (otherCalls : Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Kernel Metadata) :
    (ownerImpl otherCalls sender decode query).run (mapOwner interpret state) =
      Prod.map id (mapOwner interpret) <$> (ownerImpl calls sender decode query).run state := by
  cases query with
  | inl plaintext => exact send_map interpret calls otherCalls sendMap sender plaintext state
  | inr raw => exact raw_map interpret calls otherCalls receiveMap decode raw state

/-- The complete adaptive mixed-owner continuation commutes with the same kernel map and original replies. -/
theorem schedule_map {Kernel Other Metadata Result : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : Calls Kernel m) (otherCalls : Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Kernel Metadata) :
    (simulateQ (ownerImpl otherCalls sender decode) client).run (mapOwner interpret state) =
      Prod.map id (mapOwner interpret) <$> (simulateQ (ownerImpl calls sender decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq (ownerImpl calls sender decode)
    (ownerImpl otherCalls sender decode) (mapOwner interpret)
    (fun query state => (owner_map interpret calls otherCalls receiveMap sendMap sender decode query state).symm)
    client state).symm

/-- Public callbacks share the same ambient effects and never reinterpret owner metadata. -/
noncomputable def publicOwner {Kernel Metadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] (calls : Calls Kernel m) (publicImpl : QueryImpl spec m)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxMixedOwner.SourceSpec + spec) (StateT (State Kernel Metadata) m) :=
  fun query state => match query with
  | .inl request => (ownerImpl calls sender decode request).run state
  | .inr request => do
      let reply ← publicImpl request
      pure (reply, state)

/-- Arbitrary interleaving with unchanged public callbacks preserves all source replies and the complete mapped owner. -/
theorem public_schedule_map {Kernel Other Metadata Result ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : Calls Kernel m) (otherCalls : Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (publicImpl : QueryImpl spec m) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxMixedOwner.SourceSpec + spec) Result) (state : State Kernel Metadata) :
    (simulateQ (publicOwner otherCalls publicImpl sender decode) client).run (mapOwner interpret state) =
      Prod.map id (mapOwner interpret) <$>
        (simulateQ (publicOwner calls publicImpl sender decode) client).run state := by
  apply Eq.symm
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query state
  cases query with
  | inl request => exact (owner_map interpret calls otherCalls receiveMap sendMap sender decode request state).symm
  | inr request =>
    simp only [publicOwner, StateT.run, bind_pure_comp, Functor.map_map]
    rfl

end BeaconcryptCore.Computational.RawCtxGenericOwnerMap

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerMap.raw_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerMap.raw_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerMap.send_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerMap.send_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerMap.owner_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerMap.owner_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerMap.schedule_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerMap.schedule_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerMap.public_schedule_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerMap.public_schedule_map
