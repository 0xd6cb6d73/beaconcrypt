-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaProfile

/-! Reached private table states restore the actual native controller state. The restored evaluator retains source randomness and all counters; only private key-table representation and its duplicate signing log are erased. Actual controller query laws discharge the live-signing obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open RegistrationNativeMldsaTableSign (Valid SignOnly)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)

def observe (fallback : Credential source)
    (result : (Value × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source) :
    Value × RegistrationNativeExperiment.State n KemSK source :=
  (result.1.1, nativeState (restore source fallback result.2) result.1.2)

private theorem valid_only (before : Pool source) (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain)
    (valid : Valid source before query) : SignOnly source query := by
  cases query with
  | inl coin => trivial
  | inr query => cases query with
    | generate => exact valid
    | sign _ _ => trivial

/-- A generation-free reached program keeps exactly the private key rows used by its native-state restoration. -/
theorem program_keys (before : Pool source)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (allowed : work.AllQueriesSatisfy (Valid source before)) (result : Value × Pool source)
    (supported : result ∈ support (evaluate source work before)) : result.2.keys = before.keys :=
  RegistrationNativeMldsaTableSign.program_keys source work
    (allowed.mono (valid_only source before)) before result supported

/-- Restoring each actual final private table agrees with restoring the fixed rows of the generation-free source program. -/
theorem program (fallback : Credential source) (before : Pool source)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))
      (Value × RegistrationNativeExperiment.State n KemSK (handleSource source)))
    (allowed : work.AllQueriesSatisfy (Valid source before)) :
    observe source fallback <$> evaluate source work before =
      RegistrationNativeMldsaProgram.evaluate
        (Prod.map id (nativeState (restore source fallback before)) <$>
          RegistrationNativeMldsaSignMap.transform (restore source fallback before) work) := by
  have fixed : observe source fallback <$> evaluate source work before =
      (fun result => Prod.map id (nativeState (restore source fallback before)) result.1) <$>
        evaluate source work before := by
    simp only [map_eq_pure_bind]
    apply bind_congr_of_forall_mem_support
    intro result supported
    have keys := program_keys source before work allowed result supported
    have mapping : restore source fallback result.2 = restore source fallback before := by
      unfold restore
      rw [keys]
    rw [observe, mapping]
    rfl
  rw [fixed]
  have actual := RegistrationNativeMldsaTableSign.program_source source fallback before work allowed before rfl
  have mapped := congrArg (fun action => Prod.map id (nativeState (restore source fallback before)) <$> action) actual
  simp only [Functor.map_map] at mapped
  rw [mapped]
  simp only [RegistrationNativeMldsaProgram.evaluate, simulateQ_map,
    RegistrationNativeMldsaSignMap.transform, ← QueryImpl.simulateQ_compose,
    RegistrationNativeMldsaTableSign.target]

/-- Actual opaque Init execution restores the original real-key native source body, with all optional failures and poststate. -/
theorem bundle (fallback : Credential source) (pool : Pool source)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    :
    observe source fallback <$> runState source
      (RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index) before pool =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run
          (nativeState (restore source fallback pool) before) := by
  rw [runState, program source fallback pool _
    (RegistrationNativeMldsaControllerValid.Bundle.sourceBundle source pool setup checks representation created wire index before),
    RegistrationNativeMldsaBundleMap.sourceBundle_natural]
  exact congrFun (RegistrationNativeMldsaBundle.eval_sourceBundle setup checks wire representation created index) _

private theorem server_map (mapping : RegistrationNativeMldsaMap.Map (handleSource source) source)
    (credential : Credential (handleSource source)) (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    Prod.map id (nativeState mapping) <$>
      RegistrationNativeMldsaSignMap.transform mapping
        ((RegistrationNativeMldsaProfile.server
          (RegistrationNativeMldsaServer.build (handleSource source) credential setup
            (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application)).run before) =
      (RegistrationNativeMldsaProfile.server
        (RegistrationNativeMldsaServer.build source (RegistrationNativeMldsaMap.credential mapping credential) setup
          (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application)).run
        (nativeState mapping before) := by
  have build := congrFun (RegistrationNativeMldsaServerMap.build mapping credential setup
    (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application) before.server
  simp only [RegistrationNativeMldsaSignMap.transformState, StateT.run] at build
  simp only [RegistrationNativeMldsaProfile.server, StateT.run,
    RegistrationNativeMldsaSignMap.transform, simulateQ_map, Functor.map_map]
  simp only [RegistrationNativeMldsaSignMap.transform] at build
  rw [build]
  rfl

/-- Actual opaque Server build execution restores the original real owned signer and complete native state. -/
theorem build (fallback : Credential source) (pool : Pool source)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : Credential (handleSource source)) (live : RegistrationNativeMldsaPoolMap.CredentialLive source pool credential)
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    observe source fallback <$> runState source
      (RegistrationNativeMldsaProfile.server
        (RegistrationNativeMldsaServer.build (handleSource source) credential setup
          (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application)) before pool =
      (RegistrationNativeExperiment.server
        (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks
          (RegistrationNativeMldsa.owned source (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential))
          wire.encodeResponse handle application)).run (nativeState (restore source fallback pool) before) := by
  have allowed := RegistrationNativeMldsaControllerValid.Server.build source pool credential live setup
    (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application before.server
  have outer : ((RegistrationNativeMldsaProfile.server
      (RegistrationNativeMldsaServer.build (handleSource source) credential setup
        (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application)).run before).AllQueriesSatisfy (Valid source pool) := by
    simp only [RegistrationNativeMldsaProfile.server, StateT.run, map_eq_pure_bind]
    exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)
  rw [runState, program source fallback pool _ outer, server_map]
  exact congrFun (RegistrationNativeMldsaProfile.eval_server
    (RegistrationNativeMldsaServer.build source _ setup (RegistrationNativeWire.ledgerCodec wire) checks
      wire.encodeResponse handle application)) _ |>.trans
    (congrFun (congrArg RegistrationNativeExperiment.server
      (RegistrationNativeMldsaServer.eval_build source _ setup (RegistrationNativeWire.ledgerCodec wire) checks
        wire.encodeResponse handle application)) _)
end BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.program_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore.build
