-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative
/-! The earlier-root public build marginal is the actual build branch of the final dynamic ordinary runtime profile. The comparison uses the same public platform state and the explicit Native accounting view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildRuntime
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativePublicSourceState (roots restore nativeView)
variable {n : Nat} {E Platform I KemSK : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]

omit primitive in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem server_map {A B : Type}
    (render : A → B) (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) A)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (((render <$> RegistrationNativePlatformExperiment.server work).run before).run previous) =
      (fun result => ((render result.1.1, { before with server := result.1.2 }), result.2)) <$>
        ((work.run before.server).run previous) := by
  simp only [StateT.run, RegistrationNativePlatformExperiment.server, map_apply, Functor.map_map]
  rfl

attribute [local irreducible] RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformSourceBuild.buildSource

/-- Every actual final-runtime build branch has the same new public earlier-root source interpretation, without an earlier-profile equality premise. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup created.seed scalar before.2.roots) :
    RegistrationNativePlatformPublicBuildNative.restored (roots setup created.seed scalar) scalar <$>
      (Prod.map id RegistrationNativePlatformPublicBuildJoint.stateView <$>
        (execute setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
          (RegistrationNativePlatformPublicFrontend.executeLocal
            (RegistrationNativePlatformPublicFrontend.build setup (RegistrationNativeMldsa.owned source credential)
              view failure allocation erased helper writer reservePeer handle application source))).run before) =
    (fun (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativeExperiment.State n KemSK source) × Platform) => (result.1.1, (nativeView result.1.2, result.2))) <$>
      (((RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application)) :
        StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp) (RustM (Option (U64 × Pqxdh.Bytes)))).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2) := by
  have actual := RegistrationNativePlatformPublicBuildNative.build_source setup (canonicalWire wire) route
    (RegistrationNativeMldsa.owned source credential) created.seed scalar view failure allocation erased helper writer reservePeer handle application before live correct
  have branch : (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application)) :
      StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp) (RustM (Option (U64 × Pqxdh.Bytes)))) =
      RegistrationNativePlatformPublicFrontend.responseBytes <$>
        RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (canonicalWire wire)) view failure allocation erased reservePeer
          (RegistrationNativeMldsa.owned source credential) helper writer handle application) := rfl
  rw [actual, branch, server_map, Functor.map_map]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildRuntime.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildRuntime.build
