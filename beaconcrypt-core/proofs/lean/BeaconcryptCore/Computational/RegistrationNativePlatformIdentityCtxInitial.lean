-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm
/-! Actual native startup supplies the empty Beacon roster, genuine generated ownership and exact warm physical hash cache. Its one known ML-public-key journal entry is retained as the initial private backend provenance. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
open RegistrationNativePlatformIdentityCtxMain (Full)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native)
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

def fromInitial (initial : RegistrationNativeExperiment.Initial n KemSK source) (previous : Platform)
    (pool : PqxdhDynamicIdentityPool.SourceState) : Full n KemSK Platform source :=
  ((RegistrationNativeIdentityMainProfile.fromInitial initial, previous),
    (pool, (RegistrationNativeWorldCache.cache initial.state, [PqxdhRefinement.absBytes initial.credential.publicKey])))

/-- Generated ownership starts internally from the actual empty Beacon roster for every independent private service table. -/
theorem initial_owned (joint : PqxdhJointIdentity.Primitives) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (previous : Platform) (pool : PqxdhDynamicIdentityPool.SourceState) : Owned joint (fromInitial initial previous pool) :=
  RegistrationNativeIdentityMainProfile.initial_owned joint initial pool

/-- Restoring the physical backend gives exactly the complete actual initial native and P state. -/
theorem initial_native (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (empty : initial.state.beacons = []) (previous : Platform) (pool : PqxdhDynamicIdentityPool.SourceState) :
    native (fromInitial initial previous pool) = (initial.state, previous) := by
  rcases initial with ⟨created, credential, state⟩
  rcases state with ⟨server, owners, kem, parsed⟩
  dsimp only at empty
  subst owners
  rfl

/-- The literal startup journal retains its known anchor and exact warm cache rather than resetting it. -/
theorem initial_warm {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) (previous : Platform)
    (pool : PqxdhDynamicIdentityPool.SourceState)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    RegistrationNativePlatformCtxBirthdayCache.Warm (fromInitial initial previous pool).2.2.1 :=
  RegistrationNativeIdentityStartupWarm.start setup ensureInit identityIndex serverKeyId initial reached
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_warm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial.initial_warm
