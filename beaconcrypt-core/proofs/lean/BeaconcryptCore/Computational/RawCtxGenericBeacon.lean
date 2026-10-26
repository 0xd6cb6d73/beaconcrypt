import BeaconcryptCore.Computational.RawCtxGenericRoleStorage

/-!
The actual Beacon record frontend uses the same original phase admission, outer sender identifier, pinned server, associated data and whole-owner calls with a generic private kernel representation. Every inactive phase retains its private fields. Successful or failed source callbacks preserve their full optional result and advanced or restored kernel before original publication. The kernel map and native equations are operational; the concrete retained-table interpreter must discharge their call equations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericBeacon
open RawCtxGenericRoleStorage

def selected {Kernel Identity DhPair KemPair : Type} (state : BeaconState Kernel Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize) (kernel : Kernel) :
    RawCtxChainOwner.State Kernel Unit :=
  ⟨kernel, control.server_binding.identity_key_id, PqxdhRefinement.absBytes associatedData, (), state.rawAttempts⟩

def reinstall {Kernel Identity DhPair KemPair : Type} (state : BeaconState Kernel Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (owner : RawCtxChainOwner.State Kernel Unit) : BeaconState Kernel Identity DhPair KemPair :=
  ⟨{ state.beacon with phase := .established control associatedData owner.kernel }, owner.rawAttempts⟩

def rejected {Kernel Identity DhPair KemPair : Type} (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    RawCtxMixedOwner.SourceSpec.Range query × BeaconState Kernel Identity DhPair KemPair :=
  match query with
  | .inl _ => (none, state)
  | .inr _ => (.None, { state with rawAttempts := state.rawAttempts + 1 })

noncomputable def impl {Kernel Identity DhPair KemPair : Type} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (BeaconState Kernel Identity DhPair KemPair) m) :=
  fun query state => match state.beacon.phase with
  | .established control associatedData kernel => do
      let result ← (RawCtxChainOwner.ownerImpl calls state.beacon.identityKeyId decode query).run
        (selected state control associatedData kernel)
      pure (result.1, reinstall state control associatedData result.2)
  | _ => pure (rejected query state)

/-- Source owner selection reads the same native target, associated data, kernel and attempted-receive count. -/
theorem native_selected {Kernel Identity DhPair KemPair : Type}
    (interpret : Kernel → ConcreteRatchetKernel) (state : BeaconState Kernel Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize) (kernel : Kernel) :
    RawCtxBeaconLifecycle.selected (nativeBeacon interpret state) control associatedData (interpret kernel) =
      RawCtxChainOwner.nativeState interpret (selected state control associatedData kernel) := by
  rfl

/-- Publication reinterprets only the returned kernel and preserves the source phase, identities and exact attempt count. -/
theorem native_reinstall {Kernel Identity DhPair KemPair : Type}
    (interpret : Kernel → ConcreteRatchetKernel) (state : BeaconState Kernel Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (owner : RawCtxChainOwner.State Kernel Unit) :
    RawCtxBeaconLifecycle.reinstall (nativeBeacon interpret state) control associatedData
      (RawCtxChainOwner.nativeState interpret owner) =
      nativeBeacon interpret (reinstall state control associatedData owner) := by
  rfl

/-- The complete original Beacon frontend is the generic-kernel execution when its actual receive and send calls realize that kernel representation. -/
theorem native_step {Kernel Identity DhPair KemPair : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    simulateQ native ((RawCtxBeaconLifecycle.beaconImpl decode query).run (nativeBeacon interpret state)) =
      Prod.map id (nativeBeacon interpret) <$> (impl calls decode query).run state := by
  cases phase : state.beacon.phase
  case established control associatedData kernel =>
    rw [RawCtxBeaconLifecycle.established decode query (nativeBeacon interpret state)
      control associatedData (interpret kernel) (by simp [nativeBeacon, mapPhase, phase])]
    simp only [native_selected, bind_pure_comp, simulateQ_map]
    rw [RawCtxChainOwner.owner_native interpret calls native receiveRealized sendRealized]
    simp [impl, StateT.run, phase, Functor.map_map, Prod.map_def,
      nativeBeacon, mapPhase, RawCtxChainOwner.nativeState, RawCtxBeaconLifecycle.reinstall, reinstall]
  all_goals cases query <;> simp [RawCtxBeaconLifecycle.beaconImpl, impl, StateT.run,
    nativeBeacon, mapPhase, phase, rejected, RawCtxBeaconLifecycle.rejected]

/-- Established dispatch uses the exact selected owner and reinstalls its whole returned kernel. -/
theorem established {Kernel Identity DhPair KemPair : Type} {m : Type → Type*} [Monad m]
    (calls : RawCtxChainOwner.Calls Kernel m) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : BeaconState Kernel Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize) (kernel : Kernel)
    (phase : state.beacon.phase = .established control associatedData kernel) :
    (impl calls decode query).run state = (do
      let result ← (RawCtxChainOwner.ownerImpl calls state.beacon.identityKeyId decode query).run
        (selected state control associatedData kernel)
      pure (result.1, reinstall state control associatedData result.2)) := by
  simp only [impl, StateT.run, phase]

/-- Changing only the installed kernel representation preserves the complete Beacon API step and all callback effects. -/
theorem step_map {Kernel Other Identity DhPair KemPair : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    (impl otherCalls decode query).run (mapBeacon interpret state) =
      Prod.map id (mapBeacon interpret) <$> (impl calls decode query).run state := by
  cases phase : state.beacon.phase
  case established control associatedData kernel =>
    rw [established otherCalls decode query (mapBeacon interpret state) control associatedData
      (interpret kernel) (by simp [mapBeacon, mapPhase, phase]),
      established calls decode query state control associatedData kernel phase]
    have mapped := RawCtxGenericOwnerMap.owner_map interpret calls otherCalls receiveMap sendMap
      state.beacon.identityKeyId decode query (selected state control associatedData kernel)
    change (RawCtxChainOwner.ownerImpl otherCalls (mapBeacon interpret state).beacon.identityKeyId decode query).run
      (selected (mapBeacon interpret state) control associatedData (interpret kernel)) = _ at mapped
    rw [mapped]
    simp [bind_pure_comp, Functor.map_map, Prod.map_def, mapBeacon, mapPhase,
      RawCtxGenericOwnerMap.mapOwner, reinstall]
  all_goals cases query <;> simp [impl, StateT.run, mapBeacon, mapPhase, phase, rejected]

/-- The same representation law covers the complete adaptive Beacon schedule and every optional reply. -/
theorem schedule_map {Kernel Other Identity DhPair KemPair Result : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (sendMap : ∀ entry context, otherCalls.send (interpret entry) context =
      Prod.map interpret id <$> calls.send entry context)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    (simulateQ (impl otherCalls decode) client).run (mapBeacon interpret state) =
      Prod.map id (mapBeacon interpret) <$> (simulateQ (impl calls decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq (impl calls decode) (impl otherCalls decode)
    (mapBeacon interpret)
    (fun query state => (step_map interpret calls otherCalls receiveMap sendMap decode query state).symm)
    client state).symm

end BeaconcryptCore.Computational.RawCtxGenericBeacon

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.native_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.native_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.native_reinstall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.native_reinstall

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.native_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.established

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.step_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.step_map

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericBeacon.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericBeacon.schedule_map
