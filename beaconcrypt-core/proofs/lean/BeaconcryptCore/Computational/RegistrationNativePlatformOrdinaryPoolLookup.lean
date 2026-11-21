-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedPoolLookup
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal

/-! The single actual runtime profile preserves the exact pair at every existing recipient handle across all dynamic record writer outcomes and every typed registration callback. Same-run paths retain that literal row up to the final private pool. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin

/-- Actual full runtime callbacks preserve each old handle's complete pair without projecting any private counts. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : Native) (previous next : Platform) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous))
    (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (found : before.pool.keys[handle]? = some pair) : after.pool.keys[handle]? = some pair := by
  have packed : (reply, (after, next)) ∈ support ((RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query)).run (before, previous)) := by
    simp only [RegistrationNativePlatformPackedState.pack, StateT.run, support_map]
    exact ⟨_, supported, rfl⟩
  have interpreted : (reply, RegistrationNativePlatformKemCountedBundle.project (after, next)) ∈ support
      ((RegistrationNativePlatformKemCountedProgram.execute setup
        (RegistrationNativePlatformOrdinaryKemHandler.handler setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer query)).run
            (RegistrationNativePlatformKemCountedBundle.project (before, previous))) := by
    rw [RegistrationNativePlatformOrdinaryKemHandler.query_source, support_map]
    exact ⟨_, packed, rfl⟩
  simp only [RegistrationNativePlatformKemCountedProgram.execute, StateT.run, support_map] at interpreted
  obtain ⟨⟨⟨⟨actualReply, actualState⟩, actualPlatform⟩, actualPool⟩, ran, same⟩ := interpreted
  have poolEq : actualPool = after.pool := congrArg (fun result => result.2.2) same
  rw [← poolEq]
  exact RegistrationNativeKemCountedPoolLookup.program setup _ before.pool actualPool ((actualReply, actualState), actualPlatform) ran handle pair found

/-- The exact packed source callback keeps all prior handle rows. -/
theorem callback (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call)
    (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (found : call.before.1.pool.keys[handle]? = some pair) : call.after.1.pool.keys[handle]? = some pair := by
  simp only [Executed, RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack,
    StateT.run, support_map] at called
  obtain ⟨⟨⟨value, native⟩, platform⟩, supported, same⟩ := called
  have replyEq : value = call.reply := congrArg Prod.fst same
  have nativeEq : native = call.after.1 := congrArg (fun result => result.2.1) same
  have platformEq : platform = call.after.2 := congrArg (fun result => result.2.2) same
  rw [replyEq, nativeEq, platformEq] at supported
  exact handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer call.query call.before.1 call.after.1 call.before.2 call.after.2 call.reply supported handle pair found

/-- Every intermediate actual source row remains at the same handle in the final pool of this same runtime path. -/
theorem path {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after) (handle : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (found : before.1.pool.keys[handle]? = some pair) : after.1.pool.keys[handle]? = some pair := by
  induction reached with
  | nil => exact found
  | cons call called rest last following ih =>
      exact ih (callback setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer call called handle pair found)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPoolLookup.path
