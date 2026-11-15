-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountStop
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram

/-! The actual true-count private-table callback packs the complete external platform state with its native state. This is only a checked reassociation of actual source execution; no platform state or ML history is erased. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {KemSK Platform E Native Value ι : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

abbrev State := RegistrationNativePlatformOrdinaryMldsaCountStop.State n KemSK Platform (handleSource source) × Pool source

def arrange (result : ((Value × Native) × Platform) × Pool source) :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

def observe (publicKey : RegistrationNativeMldsaEuf.PublicKey) : RegistrationNativeMldsaStop.Observer
    (spec := RegistrationNativeRawAdapter.TypedSpec) (State := State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (Candidate := RegistrationNativeMldsaEuf.Forgery) :=
  fun query before reply after => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1.1 reply after.1.1

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

/-- Packing the actual source callback commutes with its full private-table evaluation. -/
theorem packed (work : StateT Native (RegistrationNativePlatformMldsaProgram.M (handleSource source) Platform) Value)
    (before : Native) (previous : Platform) (pool : Pool source) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      RegistrationNativeMldsaTableProgram.runState source (pack work) (before, previous) pool =
      arrange source <$> RegistrationNativePlatformMldsaTableProgram.runState source work before previous pool := by
  simp only [RegistrationNativeMldsaTableProgram.runState, pack, StateT.run,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativePlatformMldsaTableProgram.runState, Prod.map, id_eq]
  rfl

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def callback : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (State (n := n) (KemSK := KemSK) (Platform := Platform) source) ProbComp) := fun query before =>
  arrange source <$> RegistrationNativePlatformMldsaTableProgram.runState source
    (RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) before.1.1 before.1.2 before.2

/-- The executable packed callback is exactly the existing generic free private-table interpreter on the actual source body. -/
theorem generic (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) :
    (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        RegistrationNativeMldsaTableProgram.runState source
          (RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation created credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer query) before.1 before.2 :=
  (packed source _ before.1.1 before.1.2 before.2).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback.packed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback.packed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback.generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback.generic
