-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety
import BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid

/-! Every actual free source signing request uses a reached live owned credential. Source platform strategies contribute only ordinary randomness; all raw optional signing replies and private draw counts are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaPoolMap (CredentialLive OwnersLive)
open RegistrationNativeMldsaTableSign (Valid)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformQuerySafety (Safe pure_safe bind_safe map_safe inject_safe lift_safe frame_safe)
variable {n : Nat} {KemSK Platform Encoded Value ι : Type} {base : OracleSpec ι}
variable (source : Source) (pool : Pool source)

namespace Bundle
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeBeaconFrontend (Owner)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)

private theorem native
    (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaProgram.lift
      (RegistrationNativePlatformBundleLower.native (m := StateT Platform ProbComp)
        RegistrationNativePlatformMldsaProgram.coins setup checks representation created work)) :=
  lift_safe (Valid source pool) (fun _ => trivial) _

private theorem outgoing (index : Nat) (owner : Owner (handleSource source))
    (live : CredentialLive source pool owner.mldsa) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaBundle.outgoing (n := n) (Platform := Platform)
      setup checks representation created index owner query) :=
  inject_safe (Valid source pool) _
    (RegistrationNativeMldsaControllerValid.Bundle.outgoing source pool setup checks representation created index owner live query)

private theorem published (index : Nat) (owner : Owner (handleSource source))
    (live : CredentialLive source pool owner.mldsa) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (encode : registration.SignedInitView → RegistrationNativePlatformBundleLower.Front n KemSK (handleSource source)
      (StateT Platform ProbComp) (RustM (Option Encoded))) :
    Safe (Valid source pool) (do
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index owner)
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower (encode view)))
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        RegistrationNativePlatformMldsaProgram.lift (source := handleSource source) (RegistrationNativePlatformBundleLower.native
          RegistrationNativePlatformMldsaProgram.coins setup checks representation created
          (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)))
        let _ ← RegistrationNativePlatformMldsaProgram.lift (source := handleSource source) (RegistrationNativePlatformBundleLower.native
          RegistrationNativePlatformMldsaProgram.coins setup checks representation created
          (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))))
        pure (.ok (some finished.encoded)) : StateT (Local n KemSK (handleSource source)) (M (handleSource source) Platform) (RustM (Option Encoded))) := by
  apply bind_safe (Valid source pool) _ _
    (RegistrationNativePlatformQuerySafety.Beacon.begin (Valid source pool) _
      (outgoing source pool setup checks representation created index owner live) _
      (fun _ => lift_safe (Valid source pool) (fun _ => trivial) _) _ _ _ _ _)
  intro published
  cases published with
  | fail error | div => exact pure_safe (Valid source pool) _
  | ok answer => cases answer with
    | Err previous => exact pure_safe (Valid source pool) _
    | Ok finished =>
      apply bind_safe (Valid source pool) _ _ (native source pool setup checks representation created _)
      intro _changed
      apply bind_safe (Valid source pool) _ _ (native source pool setup checks representation created _)
      intro _advanced
      exact pure_safe (Valid source pool) _

private theorem native_get (before : Local n KemSK (handleSource source)) (previous : Platform) :
    (((RegistrationNativePlatformMldsaProgram.lift (source := handleSource source) (RegistrationNativePlatformBundleLower.native
      RegistrationNativePlatformMldsaProgram.coins setup checks representation created get)).run before).run previous) =
      pure ((before.1, before), previous) := rfl

/-- The actual owner lookup derives the source Init signer from the reached live owner list. -/
theorem bundle
    (encode : registration.SignedInitView → RegistrationNativePlatformBundleLower.Front n KemSK (handleSource source)
      (StateT Platform ProbComp) (RustM (Option Encoded)))
    (index : Nat) (before : Local n KemSK (handleSource source)) (previous : Platform)
    (owners : OwnersLive source pool before.1) :
    (((RegistrationNativePlatformMldsaBundle.bundle setup checks representation created encode index).run before).run previous).AllQueriesSatisfy
      (Valid source pool) := by
  simp only [RegistrationNativePlatformMldsaBundle.bundle, StateT.run_bind,
    native_get source setup checks representation created, pure_bind]
  cases found : before.1[index]? with
  | none => exact allQueriesSatisfy_pure _ _
  | some owner =>
    have live : CredentialLive source pool owner.mldsa := owners owner (List.mem_of_getElem? found)
    dsimp only
    cases phase : owner.phase with
    | initSent pending oneTime | established completed | aborted previous =>
      dsimp only
      exact allQueriesSatisfy_pure _ _
    | fresh =>
      dsimp only
      simp only [StateT.run_bind]
      apply allQueriesSatisfy_bind
        (lift_safe (Valid source pool) (fun _ => trivial) _ before previous)
      intro oneTime
      exact published source pool setup checks representation created index owner live oneTime.1.1 encode oneTime.1.2 oneTime.2
    | freshWithCoins oneTime =>
      dsimp only
      exact published source pool setup checks representation created index owner live oneTime encode before previous

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

/-- Closing the full source bundle retains live-signing validity, including failed stateful source encoding. -/
theorem sourceBundle {E : Type}
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (live : RegistrationNativeMldsaPoolMap.StateLive source pool before) :
    (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run before).run previous).AllQueriesSatisfy
      (Valid source pool) := by
  simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, StateT.run, state_map_apply, map_eq_pure_bind]
  exact allQueriesSatisfy_bind
    (bundle source pool setup checks representation created _ index
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous live)
    (fun _ => allQueriesSatisfy_pure _ _)
end Bundle

namespace Server
variable (credential : Credential (handleSource source)) (live : CredentialLive source pool credential)
include live

private theorem outgoing {Auxiliary : Type} (query : RegistrationSigningShared.Spec.Domain) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaServer.outgoing (n := n) (Platform := Platform)
      (Auxiliary := Auxiliary) (handleSource source) credential query) := by
  apply inject_safe
  intro before
  change ((fun result => (result.1, { before with world := result.2 })) <$>
    (RegistrationNativeMldsaServer.outgoing (handleSource source) credential query).run before.world).AllQueriesSatisfy (Valid source pool)
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind
    (RegistrationNativeMldsaControllerValid.Server.outgoing source pool credential live query before.world)
    (fun _ => allQueriesSatisfy_pure _ _)

private theorem afterRecord {E : Type}
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaServer.afterRecord (n := n)
      (handleSource source) credential writer control hashed) := by
  unfold RegistrationNativePlatformMldsaServer.afterRecord
  apply bind_safe (Valid source pool) _ _
    (RegistrationNativePlatformQuerySafety.Server.program (Valid source pool) _
      (outgoing source pool credential live) _
      (fun _ => lift_safe (Valid source pool) (fun _ => trivial) _) _)
  intro published
  cases published with
  | fail error | div => exact pure_safe (Valid source pool) _
  | ok answer => cases answer with
    | Err prior => exact pure_safe (Valid source pool) _
    | Ok ready => exact lift_safe (Valid source pool) (fun _ => trivial) _

variable [primitive : AdapterSealPrimitive.Operations]
private theorem finish {E Reader Response : Type} (setup : Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaServer.finish (n := n) (handleSource source) credential
      setup codec view failure allocation erased helper writer control initial) := by
  unfold RegistrationNativePlatformMldsaServer.finish
  apply bind_safe (Valid source pool) _ _ (lift_safe (Valid source pool) (fun _ => trivial) _)
  intro recorded
  cases recorded with
  | fail error | div => exact pure_safe (Valid source pool) _
  | ok answer => cases answer with
    | Err prior => exact pure_safe (Valid source pool) _
    | Ok hashed => exact afterRecord source pool credential live writer control hashed

/-- The complete actual source build uses only ordinary effects and its reached live owned Server signer. -/
theorem build {E Reader Response : Type} (setup : Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Safe (Valid source pool) (RegistrationNativePlatformMldsaServer.build (n := n) (handleSource source) credential
      setup codec view failure allocation erased reservePeer helper writer handle application) := by
  unfold RegistrationNativePlatformMldsaServer.build
  exact RegistrationNativePlatformSdkQuerySafety.build (Valid source pool) _
    (lift_safe (Valid source pool) (fun _ => trivial) _) _
    (lift_safe (Valid source pool) (fun _ => trivial) _) _
    (fun _ => lift_safe (Valid source pool) (fun _ => trivial) _) _
    (finish source pool credential live setup codec view failure allocation erased helper writer) handle application

end Server

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Bundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Bundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Bundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Bundle.sourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Server.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaControllerValid.Server.build
