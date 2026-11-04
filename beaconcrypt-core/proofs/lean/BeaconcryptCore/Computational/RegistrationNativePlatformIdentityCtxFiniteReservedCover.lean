-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover

/-! The exact original source causal cover transports to any reserved-family size through its explicit same-run pool representation. The final generated handle selects the family index, while accept and first-bundle ordinals retain the original budgets. No public-key uniqueness, prefix owner eligibility, reveal freshness or family probability equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteReservedCover
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativePlatformIdentityCtxCausalAttempt (Attempt)
open RegistrationNativePlatformIdentityCtxFiniteCover (Unissued Issued causal_cover)
open RegistrationNativeStageTrace (Call)
variable {V : Type}
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


/-- A reserved-family interpretation of the final same-run pool supplies its exact finite generated-handle index. This is a representation corollary, not a probability-game identification. -/
theorem reserved_cover (count : Nat) (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (empty : before.1.beacons = [])
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical setup.source.crypto wire
      (RegistrationNativePlatformOrdinaryCausalReservedCover.identities setup.joint (drop result.2.2.1)) result.2.1.transcript)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) (router : PqxdhDynamicIdentityRouting.PublicState)
    (capacity : router.created ≤ count)
    (pool : result.2.2.1.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router) :
    ∃ attempt : Attempt setup.joint wire budget result.2.2.2 result.2.2.1, ∃ identity : Fin count,
      identity.val = attempt.finalOwner.identity.handle ∧
      attempt.finalOwner.identity.publicIdentity = setup.joint.publicKeys (seeds identity) ∧
      (Unissued attempt ∨ Nonempty (Issued attempt)) := by
  obtain ⟨attempt, branch⟩ := causal_cover setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer shortRejects serverKeyId bounds mode work budget bounded before empty physical result reached failed
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work _ result reached
  have owned : RegistrationNativePlatformIdentityCtxLifecycle.Owned setup.joint (drop result.2.2.1) := by
    apply (RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer path ?_).1
    constructor
    · change RegistrationNativeIdentityRealization.Owned setup.joint _ before.1.beacons
      rw [empty]
      intro owner member
      cases member
    · simp only [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles, owners, empty, List.map_nil, List.nodup_nil]
  obtain ⟨identity, handleEq, publicEq⟩ := RegistrationNativePlatformIdentityCtxReservedOwners.owner setup.joint seeds router capacity
    (drop result.2.2.1) owned pool attempt.finalOwner (List.mem_of_getElem? attempt.finalFound)
  exact ⟨attempt, identity, handleEq, publicEq, branch⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteReservedCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteReservedCover.reserved_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteReservedCover.reserved_cover
