-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceBundle
/-! The literal corrected public `.create` and `.bundle` callbacks interpret to the literal fixed-scalar ordinary platform callbacks with the same persistent P. The only owner premise is the internal canonical representation invariant, derived separately for actual adaptive public execution. No old callback identity, fixed writer, successful allocation or empty marker history is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (project nativeView)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Platform E Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem executeLocal_map (change : Value → Next)
    (work : RegistrationNativePlatformPublicFrontend.LocalM n KemSK Platform source Value) :
    RegistrationNativePlatformPublicFrontend.executeLocal (change <$> work) =
      change <$> RegistrationNativePlatformPublicFrontend.executeLocal work := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal, StateT.run, map_apply,
    simulateQ_map]

private theorem execute_map (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (change : Value → Next) (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) :
    RegistrationNativePlatformPublicSourceExecution.execute (n := n) setup wire route sign seed scalar (change <$> work) =
      change <$> RegistrationNativePlatformPublicSourceExecution.execute (n := n) setup wire route sign seed scalar work := by
  funext before
  simp only [RegistrationNativePlatformPublicSourceExecution.execute, RegistrationNativePublicSourceEffects.close,
    StateT.run, map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq]

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Actual public creation restores the exact eager source birth on the complete reached native/P state. -/
theorem create (selected selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.1.beacons) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute (n := n) setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selected selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (.inr (.create edPin mlPin keyId)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selected scalar (.inr (.create edPin mlPin keyId))).run
          (RegistrationNativePublicSourceState.restore roots scalar before.1.1 before.2)).run before.1.2 := by
  convert RegistrationNativePlatformPublicSourceCreate.create_source setup checks wire route representation created credential writer selected scalar roots
      edPin mlPin keyId before canonical using 1 <;> rfl


/-- Actual public bundle publication retains the same dynamic source writer, all allocation outcomes and complete reached native/P state. -/
theorem bundle (selected selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (index : Nat) (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.1.beacons) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute (n := n) setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selected selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (.inr (.bundle index)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selected scalar (.inr (.bundle index))).run
          (RegistrationNativePublicSourceState.restore roots scalar before.1.1 before.2)).run before.1.2 := by
  change (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
    (RegistrationNativePlatformPublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.bundleBytes <$>
          RegistrationNativePlatformPublicFrontend.beacon
            (RegistrationNativePlatformPublicSourceBundle.work setup source writer selected scalar index)))).run before =
    (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
      ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
        (RegistrationNativePublicSourceState.restore roots scalar before.1.1 before.2)).run before.1.2
  rw [executeLocal_map, execute_map]
  simp only [StateT.run_map, Functor.map_map]
  convert RegistrationNativePlatformPublicSourceBundle.bundle_source setup checks wire route representation created credential writer selected scalar roots
    index before canonical using 1

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks.bundle
