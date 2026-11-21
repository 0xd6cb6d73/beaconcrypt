-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerMap

/-! Generation-free private-table evaluation restores the exact native state and retains the complete shared external platform poststate. The syntactic live-signing condition is discharged from the actual controllers at their call sites. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaTableProgram (evaluate)
open RegistrationNativeMldsaTableSign (Valid)
variable {n : Nat} {KemSK Platform Value : Type} (source : Source)

def observe (fallback : Credential source)
    (result : ((Value × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source) :
    (Value × RegistrationNativeExperiment.State n KemSK source) × Platform :=
  ((result.1.1.1, nativeState (restore source fallback result.2) result.1.1.2), result.1.2)

/-- Actual table evaluation keeps the full native and platform result while restoring only the private signing-key representation. -/
theorem program (fallback : Credential source) (before : Pool source)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))
      ((Value × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform))
    (allowed : work.AllQueriesSatisfy (Valid source before)) :
    observe source fallback <$> evaluate source work before =
      RegistrationNativeMldsaProgram.evaluate
        (Prod.map (Prod.map id (nativeState (restore source fallback before))) id <$>
          RegistrationNativeMldsaSignMap.transform (restore source fallback before) work) := by
  have fixed : observe source fallback <$> evaluate source work before =
      (fun result => Prod.map (Prod.map id (nativeState (restore source fallback before))) id result.1) <$>
        evaluate source work before := by
    simp only [map_eq_pure_bind]
    apply bind_congr_of_forall_mem_support
    intro result supported
    have keys := RegistrationNativeMldsaTableRestore.program_keys source before work allowed result supported
    have mapping : restore source fallback result.2 = restore source fallback before := by
      unfold restore
      rw [keys]
    rw [observe, mapping]
    rfl
  rw [fixed]
  have actual := RegistrationNativeMldsaTableSign.program_source source fallback before work allowed before rfl
  have mapped := congrArg (fun action => Prod.map (Prod.map id (nativeState (restore source fallback before))) id <$> action) actual
  simp only [Functor.map_map] at mapped
  rw [mapped]
  simp only [RegistrationNativeMldsaProgram.evaluate, simulateQ_map,
    RegistrationNativeMldsaSignMap.transform, ← QueryImpl.simulateQ_compose,
    RegistrationNativeMldsaTableSign.target]

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι E : Type} {base : OracleSpec ι}

/-- The actual table-backed source bundle restores its literal real-key source execution and the complete platform poststate. -/
theorem bundle (fallback : Credential source) (pool : Pool source)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) :
    observe source fallback <$> evaluate source
      (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run before).run previous) pool =
      (((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins
        setup checks representation created source writer index).run
          (nativeState (restore source fallback pool) before)).run previous) := by
  rw [program source fallback pool _
    (RegistrationNativePlatformMldsaControllerValid.Bundle.sourceBundle source pool setup checks representation created writer index before previous),
    RegistrationNativePlatformMldsaBundleMap.sourceBundle_natural]
  exact congrFun (congrFun (RegistrationNativePlatformMldsaBundle.evaluate_sourceBundle
    (source := source) setup checks representation created writer index)
      (nativeState (restore source fallback pool) before)) previous


private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := bind_pure_comp _ _

private theorem evaluate_server {ml : Source}
    (work : StateT (RegistrationServerFrontendCompiler.State n) (RegistrationNativePlatformMldsaProgram.M ml Platform) Value) :
    RegistrationNativePlatformMldsaProgram.evaluate
      (RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := ml) work) =
      RegistrationNativePlatformExperiment.server (RegistrationNativePlatformMldsaProgram.evaluate work) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.evaluate, RegistrationNativePlatformExperiment.server,
    RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run, map_apply, simulateQ_map]

variable [primitive : AdapterSealPrimitive.Operations]
private theorem server_map {Reader Response : Type} (mapping : RegistrationNativeMldsaMap.Map (handleSource source) source)
    (credential : Credential (handleSource source)) (setup : Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) :
    Prod.map (Prod.map id (nativeState mapping)) id <$>
      RegistrationNativeMldsaSignMap.transform mapping
        (((RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := handleSource source)
          (RegistrationNativePlatformMldsaServer.build (handleSource source) credential setup codec view failure allocation
            erased reservePeer helper writer handle application)).run before).run previous) =
      (((RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := source)
        (RegistrationNativePlatformMldsaServer.build source (RegistrationNativeMldsaMap.credential mapping credential)
          setup codec view failure allocation erased reservePeer helper writer handle application)).run
            (nativeState mapping before)).run previous) := by
  have build := congrFun (congrFun (RegistrationNativePlatformMldsaServerMap.build mapping credential setup codec
    view failure allocation erased reservePeer helper writer handle application) before.server) previous
  simp only [RegistrationNativePlatformMldsaSignMap.transform, RegistrationNativeMldsaSignMap.transform, StateT.run] at build
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply,
    RegistrationNativeMldsaSignMap.transform, simulateQ_map, Functor.map_map]
  rw [build]
  rfl

/-- The actual full source build restores the reached owned signer and retains source allocation, publication and installation poststates. -/
theorem build {Reader Response : Type} (fallback : Credential source) (pool : Pool source)
    (credential : Credential (handleSource source)) (live : RegistrationNativeMldsaPoolMap.CredentialLive source pool credential)
    (setup : Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) :
    observe source fallback <$> evaluate source
      (((RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := handleSource source)
        (RegistrationNativePlatformMldsaServer.build (handleSource source) credential setup codec view failure allocation
          erased reservePeer helper writer handle application)).run before).run previous) pool =
      (((RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := source)
        (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation
          erased reservePeer (RegistrationNativeMldsa.owned source (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential))
          helper writer handle application)).run (nativeState (restore source fallback pool) before)).run previous) := by
  have valid : (((RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := handleSource source)
      (RegistrationNativePlatformMldsaServer.build (handleSource source) credential setup codec view failure allocation
        erased reservePeer helper writer handle application)).run before).run previous).AllQueriesSatisfy (Valid source pool) := by
    simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, map_eq_pure_bind]
    exact allQueriesSatisfy_bind
      (RegistrationNativePlatformMldsaControllerValid.Server.build source pool credential live setup codec view failure allocation
        erased reservePeer helper writer handle application before.server previous)
      (fun _ => allQueriesSatisfy_pure _ _)
  rw [program source fallback pool _ valid, server_map]
  change (((RegistrationNativePlatformMldsaProgram.evaluate
    (RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := source)
      (RegistrationNativePlatformMldsaServer.build source (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential)
        setup codec view failure allocation erased reservePeer helper writer handle application))).run
          (nativeState (restore source fallback pool) before)).run previous) = _
  rw [evaluate_server, RegistrationNativePlatformMldsaServer.evaluate_build]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore.build
