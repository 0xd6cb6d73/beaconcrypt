import BeaconcryptCore.Computational.PqxdhInitialGenericPublication
import BeaconcryptCore.Computational.RawCtxGenericFamilyNative

/-!
The source protocol state changes only its private ratchet representation. Every role, registration control, consumed identifier, reveal history and shared primitive state remains present. Publication and Beacon installation commute with native interpretation, including the original attempted-receive counters and history tick. The original record interface is interpreted in the same ambient state monad.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericProtocol
variable {Kernel M P I D K A Result : Type} {S B : Nat}

structure State (Kernel M P I D K A : Type) (S B : Nat) where
  roles : RawCtxGenericFamilyLive.State Kernel M P I D K S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes
  primitive : RawCtxSharedPrimitive.SharedState A

def native (interpret : Kernel → ConcreteRatchetKernel) (state : State Kernel M P I D K A S B) :
    PqxdhRegistrationProtocolState.State M P I D K A S B :=
  ⟨RawCtxGenericFamilyLive.nativeState interpret state.roles, state.controls, state.consumed, state.primitive⟩

def fromNative (represent : ConcreteRatchetKernel → Kernel)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) : State Kernel M P I D K A S B :=
  ⟨(RawCtxGenericRoleFamily.fromRoles represent state.roles.1, state.roles.2), state.controls, state.consumed, state.primitive⟩

def selected (senderId : M → Std.U64) (index : Fin S) (state : State Kernel M P I D K A S B) :
    PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes) :=
  ⟨(state.roles.1.1 index).server, senderId (state.roles.1.1 index).server.metadata, state.controls index, state.consumed index⟩

def install (index : Fin S) (state : State Kernel M P I D K A S B)
    (updated : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState A) : State Kernel M P I D K A S B :=
  { roles := ((Function.update state.roles.1.1 index { state.roles.1.1 index with server := updated.server }, state.roles.1.2), state.roles.2)
    controls := Function.update state.controls index updated.control
    consumed := Function.update state.consumed index updated.consumed
    primitive := primitive }

def consume (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State Kernel M P I D K A S B) :
    State Kernel M P I D K A S B :=
  { state with consumed := Function.update state.consumed index ready.consumed.consumed }

def finishInstall (index : Fin B) (state : State Kernel M P I D K A S B)
    (updated : RawCtxGenericRoleStorage.BeaconState Kernel I D K)
    (primitive : RawCtxSharedPrimitive.SharedState A) : State Kernel M P I D K A S B :=
  { state with
    roles := ((state.roles.1.1, Function.update state.roles.1.2 index updated), RawCtxProtocolReveals.tick state.roles.2)
    primitive := primitive }

/-- Native representation reconstructs the whole current source state when it reconstructs each private kernel. -/
theorem roundtrip (represent : ConcreteRatchetKernel → Kernel) (interpret : Kernel → ConcreteRatchetKernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    native interpret (fromNative represent state) = state := by
  simp only [native, fromNative, RawCtxGenericFamilyLive.nativeState,
    RawCtxGenericRoleFamily.roundtrip represent interpret inverse]

/-- The selected builder reads the original current identity, sender, peers and registration controls. -/
theorem selected_native (interpret : Kernel → ConcreteRatchetKernel) (senderId : M → Std.U64)
    (index : Fin S) (metadata : P) (state : State Kernel M P I D K A S B) :
    PqxdhInitialGenericPublication.native interpret (selected senderId index state) =
      (PqxdhRegistrationProtocolState.input senderId index metadata (native interpret state)).state := rfl

/-- The exact consumed-registration update is independent of private ratchet representation. -/
theorem consume_native (interpret : Kernel → ConcreteRatchetKernel) (index : Fin S)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State Kernel M P I D K A S B) :
    native interpret (consume index ready state) = PqxdhRegistrationProtocolState.consume index ready (native interpret state) := rfl

/-- Whole Server reinstallation commutes with interpretation and preserves the original selected raw-attempt count. -/
theorem install_native (interpret : Kernel → ConcreteRatchetKernel) (index : Fin S)
    (state : State Kernel M P I D K A S B)
    (updated : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState A) :
    native interpret (install index state updated primitive) =
      PqxdhRegistrationProtocolState.install index (native interpret state)
        (PqxdhInitialGenericPublication.native interpret updated) primitive := by
  simp only [native, install, PqxdhRegistrationProtocolState.install,
    RawCtxGenericFamilyLive.nativeState, RawCtxGenericRoleFamily.nativeRoles,
    PqxdhInitialGenericPublication.native]
  congr 1
  exact congrArg (fun servers => ((servers, fun j => RawCtxGenericRoleStorage.nativeBeacon interpret (state.roles.1.2 j)), state.roles.2))
    (Function.comp_update (RawCtxGenericRoleStorage.nativeServer interpret) state.roles.1.1 index
      { state.roles.1.1 index with server := updated.server })

/-- Beacon completion installs the original optional owner result, retains all other roles and ticks the same history once. -/
theorem finish_native (interpret : Kernel → ConcreteRatchetKernel) (index : Fin B)
    (state : State Kernel M P I D K A S B)
    (updated : RawCtxGenericRoleStorage.BeaconState Kernel I D K)
    (primitive : RawCtxSharedPrimitive.SharedState A) :
    native interpret (finishInstall index state updated primitive) =
      PqxdhPhase2LiveFinish.install index (native interpret state)
        (RawCtxGenericRoleStorage.nativeBeacon interpret updated) primitive := by
  simp only [native, finishInstall, PqxdhPhase2LiveFinish.install,
    RawCtxGenericFamilyLive.nativeState, RawCtxGenericRoleFamily.nativeRoles]
  congr 1
  exact congrArg (fun beacons => ((fun j => RawCtxGenericRoleStorage.nativeServer interpret (state.roles.1.1 j), beacons), RawCtxProtocolReveals.tick state.roles.2))
    (Function.comp_update (RawCtxGenericRoleStorage.nativeBeacon interpret) state.roles.1.2 index updated)

def reinstall (index : Fin S) (state : State Kernel M P I D K A S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) × RawCtxSharedPrimitive.SharedState A) :
    RustM (Option PqxdhServerRegistrationPublication.Response) × State Kernel M P I D K A S B :=
  match result.1 with
  | .ok value => (.ok value.1, install index state value.2 result.2)
  | .fail error => (.fail error, { state with primitive := result.2 })
  | .div => (.div, { state with primitive := result.2 })

/-- Ordinary results and diagnostic branches retain the same complete primitive poststate under the source representation map. -/
theorem reinstall_native (interpret : Kernel → ConcreteRatchetKernel) (index : Fin S)
    (state : State Kernel M P I D K A S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) × RawCtxSharedPrimitive.SharedState A) :
    Prod.map id (native interpret) (reinstall index state result) =
      PqxdhRegistrationProtocolState.reinstall index (native interpret state)
        ((Prod.map id (PqxdhInitialGenericPublication.native interpret) <$> result.1), result.2) := by
  cases original : result.1 <;> simp only [reinstall, PqxdhRegistrationProtocolState.reinstall, original,
    Prod.map_apply, id_eq, install_native] <;> rfl

end BeaconcryptCore.Computational.PqxdhInitialGenericProtocol

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.roundtrip
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.selected_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.selected_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.consume_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.consume_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.install_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.install_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.finish_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.reinstall_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericProtocol.reinstall_native
