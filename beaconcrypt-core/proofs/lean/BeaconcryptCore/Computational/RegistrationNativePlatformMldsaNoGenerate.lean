-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety
/-! The corrected source bundle and Server build cannot generate an ML credential. This syntactic proof covers arbitrary external allocator state, optional primitive failures, failed source writers and later installation failures. It supplies a generation bill without any success, signer or live-key premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate
open RegistrationNativePlatformQuerySafety
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaNoGenerate (Allowed)
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {source : RegistrationNativeMldsa.Source} {Platform State Value : Type} {n : Nat}
variable {E Auxiliary Encoded Reader Response ι KemSK : Type} {base : OracleSpec ι}

private theorem ordinary (work : StateT State (StateT Platform ProbComp) Value) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaProgram.lift work) :=
  lift_safe (Allowed source) (fun _ => trivial) work

namespace Server
variable (source) (credential : RegistrationNativeMldsa.Credential source)

theorem outgoing (query : RegistrationSigningShared.Spec.Domain) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaServer.outgoing (n := n) (Auxiliary := Auxiliary) (Platform := Platform) source credential query) := by
  unfold RegistrationNativePlatformMldsaServer.outgoing
  apply inject_safe
  intro before
  simp only [StateT.run]
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind (RegistrationNativeMldsaNoGenerate.Server.outgoing source credential query before.world)
    (fun _ => allQueriesSatisfy_pure _ _)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

omit primitive in
theorem afterRecord
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaServer.afterRecord (n := n) source credential writer control hashed) := by
  unfold RegistrationNativePlatformMldsaServer.afterRecord
  apply bind_safe (Allowed source) _ _
    (RegistrationNativePlatformQuerySafety.Server.program (Allowed source) _ (outgoing source credential) _ (fun _ => ordinary _) hashed)
  intro published
  cases published with
  | fail error | div => exact pure_safe (Allowed source) _
  | ok answer => cases answer with
    | Err prior => exact pure_safe (Allowed source) _
    | Ok ready => exact ordinary _

theorem finish (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaServer.finish (n := n) source credential setup codec view failure allocation erased helper writer control initial) := by
  unfold RegistrationNativePlatformMldsaServer.finish
  apply bind_safe (Allowed source) _ _ (ordinary _)
  intro recorded
  cases recorded with
  | fail error | div => exact pure_safe (Allowed source) _
  | ok answer => cases answer with
    | Err prior => exact pure_safe (Allowed source) _
    | Ok hashed => exact afterRecord source credential writer control hashed

theorem build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaServer.build (n := n) source credential setup codec view failure allocation erased reservePeer helper writer handle application) := by
  unfold RegistrationNativePlatformMldsaServer.build
  exact RegistrationNativePlatformSdkQuerySafety.build (Allowed source) _ (ordinary _) _ (ordinary _)
    _ (fun _ => ordinary _) _ (finish source credential setup codec view failure allocation erased helper writer) handle application
end Server

namespace Bundle
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)

theorem outgoing (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaBundle.outgoing (n := n) (Platform := Platform) setup checks representation created index owner query) := by
  unfold RegistrationNativePlatformMldsaBundle.outgoing
  exact inject_safe (Allowed source) _
    (RegistrationNativeMldsaNoGenerate.Bundle.outgoing source setup checks representation created index owner query)

theorem bundle
    (encode : registration.SignedInitView → RegistrationNativePlatformBundleLower.Front n KemSK source (StateT Platform ProbComp) (RustM (Option Encoded)))
    (index : Nat) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaBundle.bundle setup checks representation created encode index) := by
  unfold RegistrationNativePlatformMldsaBundle.bundle
  apply bind_safe (Allowed source) _ _ (ordinary _)
  intro owners
  cases found : owners[index]? with
  | none => exact pure_safe (Allowed source) _
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals try exact pure_safe (Allowed source) _
      all_goals
        apply bind_safe (Allowed source) _ _ (by first | exact pure_safe (Allowed source) _ | exact ordinary _)
        intro oneTime
        apply bind_safe (Allowed source) _ _
          (RegistrationNativePlatformQuerySafety.Beacon.begin (Allowed source) _
            (outgoing setup checks representation created index owner) _ (fun _ => ordinary _) _ _ _ _ _)
        intro published
        cases published with
        | fail error | div => exact pure_safe (Allowed source) _
        | ok answer => cases answer with
          | Err prior => exact pure_safe (Allowed source) _
          | Ok finished =>
              simp only
              exact bind_safe (Allowed source) _ _ (ordinary _)
                (fun _ => bind_safe (Allowed source) _ _ (ordinary _) (fun _ => pure_safe (Allowed source) _))

theorem sourceBundle
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Safe (Allowed source) (RegistrationNativePlatformMldsaBundle.sourceBundle (n := n) (source := source) setup checks representation created writer index) := by
  intro before previous
  unfold RegistrationNativePlatformMldsaBundle.sourceBundle
  simp only [StateT.run]
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind (bundle setup checks representation created _ index _ previous)
    (fun _ => allQueriesSatisfy_pure _ _)
end Bundle
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.afterRecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.afterRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Server.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate.Bundle.sourceBundle
