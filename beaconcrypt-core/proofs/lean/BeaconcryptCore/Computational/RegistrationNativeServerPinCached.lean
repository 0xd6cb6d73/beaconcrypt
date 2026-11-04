-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute

/-! The pin-cache receipt needed by the deployed repeated fingerprint is established by actual initialized startup and preserved by every original logical-native typed callback. The proof uses only literal cache extension and immutable Server-pin fields, without a source-security or desired-correspondence premise. The repeated request still carries its separate hash-effect bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinCached
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeServerPinRecompute (Cached)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem extend (pin : session.ServerAuthenticationPin) (before after : CtxRomAuth.CtxRO.QueryCache)
    (cached : Cached pin before) (extension : before ≤ after) : Cached pin after := by
  obtain ⟨digest, reached, fingerprint⟩ := cached
  exact ⟨digest, extension reached, fingerprint⟩

theorem frontend (created : PqxdhLiveServerConstruction.Created Unit) (publicKey : Std.Array U8 1952#usize)
    (auxiliary : Auxiliary) (before after : PqxdhRecordLiftWorld.State n)
    (native : RegistrationWorldServerFrontend.State n Auxiliary)
    (supported : (.ok (.Some native), after) ∈ support
      ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before)) :
    Cached native.pin native.global.2.world.1.primitive.2 := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨installed, _installed, pinned, pinnedAt, returned⟩ := supported
  cases answered : pinned.1 with
  | fail error | div => simp only [answered] at returned; cases returned
  | ok value => cases value with
    | none => simp only [answered] at returned; cases returned
    | some pin =>
      simp only [answered] at returned
      cases returned
      apply RegistrationNativeServerPinRecompute.initialize_cached _ publicKey _ _ pin
      have shape : pinned = (.ok (.Some pin), pinned.2) := by rw [← answered]
      rw [← shape]
      exact pinnedAt

/-- The actual generated initialized state has its stored Server pin fingerprint in its single shared cache. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Cached initial.state.server.pin (RegistrationNativeWorldCache.cache initial.state) := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
    simp only [built, mem_support_bind_iff] at continued
    obtain ⟨generated, _generated, continued⟩ := continued
    cases chosen : generated.1 with
    | none => simp only [chosen, mem_support_pure_iff] at continued; cases continued
    | some credential =>
      simp only [chosen, mem_support_bind_iff] at continued
      obtain ⟨initialized, reached, returned⟩ := continued
      cases native : initialized.1 with
      | fail error | div => simp only [native, mem_support_pure_iff] at returned; cases returned
      | ok reply => cases reply with
        | none => simp only [native, mem_support_pure_iff] at returned; cases returned
        | some state =>
          simp only [native, mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          have shape : initialized = (.ok (.Some state), initialized.2) := by rw [← native]
          exact frontend created credential.publicKey RegistrationServerRoleBackend.empty generated.2 initialized.2 state
            (by rw [← shape]; exact reached)

/-- Original typed callbacks retain the pin receipt through all successful and failed control-flow prefixes. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : Cached before.server.pin (RegistrationNativeWorldCache.cache before))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Cached result.2.server.pin (RegistrationNativeWorldCache.cache result.2) := by
  rw [RegistrationNativeServerPinTrace.handler_pin setup checks wire route representation created credential query before result supported]
  exact extend _ _ _ cached
    (RegistrationNativeHandlerCache.handler setup checks wire route representation created credential query before result supported)

theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : Cached before.server.pin (RegistrationNativeWorldCache.cache before))
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    Cached result.2.server.pin (RegistrationNativeWorldCache.cache result.2) := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    (fun current => Cached current.server.pin (RegistrationNativeWorldCache.cache current))
    (fun query current prior next reached => handler setup checks wire route representation created credential query current prior next reached)
    work before cached result supported

/-- The receipt at every reached original typed-program cut is derived from actual startup, rather than supplied as an invariant premise. -/
theorem initialized_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    Cached result.2.server.pin (RegistrationNativeWorldCache.cache result.2) :=
  program setup checks wire route representation initial.created initial.credential work initial.state
    (start setup ensureInit identityIndex serverKeyId initial initialized) result supported

/-- Actual initialization and immutable Server-pin fields identify the recomputed binding and displayed ML public key at every reached original cut. -/
theorem initialized_fields (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    result.2.server.pin.binding = ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ ∧
      result.2.server.pin.public_key = initial.credential.publicKey := by
  rw [RegistrationNativeServerPinTrace.program_pin setup checks wire route representation initial.created initial.credential work initial.state result supported]
  exact RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial initialized

/-- Recomputing the configured Server pin at an actual reached original execution cut is a literal cache hit with one additional hash-effect charge. -/
theorem initialized_hit (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    (RegistrationNativeServerPinRecompute.native
      ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey).run
        result.2.server.world.world.1 =
      pure (.ok (.Some result.2.server.pin), PqxdhRecordLiftWorld.chargeEffect
        (.inr (.hash (PqxdhRefinement.absBytes initial.credential.publicKey))) result.2.server.world.world.1) := by
  obtain ⟨binding, key⟩ := initialized_fields setup checks wire route representation ensureInit identityIndex serverKeyId initial initialized work result supported
  simpa only [binding, key] using
    RegistrationNativeServerPinRecompute.native_hit result.2.server.pin result.2.server.world.world.1
      (initialized_program setup checks wire route representation ensureInit identityIndex serverKeyId initial initialized work result supported)

end BeaconcryptCore.Computational.RegistrationNativeServerPinCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.extend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.frontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_hit
