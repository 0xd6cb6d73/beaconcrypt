-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! The selected-KEM client's executable state has no KEM secret or private pool coordinate. Its exact source join keeps that private pool separately. The sole source projection additionally forgets the proved private uniform accounting coordinate, retaining all native capabilities, populated AD, cache, signing/record logs, owner handles and parsed-accept counter. -/
open CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerState
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}

structure State (n : Nat) (mlSource : RegistrationNativeMldsa.Source) where
  server : RegistrationServerFrontendCompiler.State n
  beacons : RegistrationNativeBeaconFrontend.State mlSource
  parsedAccepts : Nat

def ofNative (native : RegistrationNativeExperiment.State n KemSK mlSource) : State n mlSource :=
  ⟨native.server, native.beacons, native.parsedAccepts⟩

def toNative (state : State n mlSource) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeExperiment.State n KemSK mlSource :=
  ⟨state.server, state.beacons, pool, state.parsedAccepts⟩

def maskServer (server : RegistrationServerFrontendCompiler.State n) :
    RegistrationServerFrontendCompiler.State n :=
  { server with world := { server.world with world :=
    (RegistrationNativeKemWorldUniform.mask server.world.world.1, server.world.world.2) } }

def mask (state : State n mlSource) : State n mlSource := { state with server := maskServer state.server }
def project (native : RegistrationNativeExperiment.State n KemSK mlSource) : State n mlSource := mask (ofNative native)

/-- Removing and restoring the separate private pool changes no source state coordinate. -/
theorem native_roundtrip (native : RegistrationNativeExperiment.State n KemSK mlSource) :
    toNative (ofNative native) native.pool = native := rfl

/-- The executable client state does not depend on the private pool or its secret-key type. -/
theorem client_roundtrip (state : State n mlSource) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    ofNative (toNative state pool) = state := rfl

/-- Applying the uniform-only analysis projection twice has no additional effect. -/
theorem mask_idempotent (state : State n mlSource) : mask (mask state) = mask state := rfl

/-- Reassembling the projected client with its entire original private pool changes only the native uniform analysis coordinate. -/
theorem project_join (native : RegistrationNativeExperiment.State n KemSK mlSource) :
    toNative (project native) native.pool = { native with server := maskServer native.server } := rfl

end BeaconcryptCore.Computational.RegistrationNativeKemServerState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerState.native_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerState.native_roundtrip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerState.client_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerState.client_roundtrip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerState.mask_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerState.mask_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerState.project_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerState.project_join
