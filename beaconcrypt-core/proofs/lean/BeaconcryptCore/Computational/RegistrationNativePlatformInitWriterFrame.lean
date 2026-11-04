-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay
import BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame
import BeaconcryptCore.Computational.RegistrationNativeInitTupleCache

/-! The literal effectful source Init writer retains the complete owner/environment/native state and changes only its outer platform state. Every raw source writer failure and divergence is retained. The frame is proved by exact interpretation of the checked source encoder, without a static wire-function or successful-encoding assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform Value Next ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def encoder
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) : StateT (Local n KemSK source) (StateT Platform ProbComp)
      (RustM (Option (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBundleLower.lower (RegistrationNativePlatformGenericBundle.encoderWith
    (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)

private theorem simulate_lift {I A : Type} {spec : OracleSpec I}
    (writer : QueryImpl spec (StateT Platform ProbComp)) (work : OracleComp spec A) :
    simulateQ (fun query => StateT.lift (writer query) : QueryImpl spec (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp))) work =
      StateT.lift (simulateQ writer work) := by
  change simulateQ (writer.liftTarget (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp))) work =
    liftM (simulateQ writer work)
  exact simulateQ_liftTarget writer work

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual source encoding changes only the external platform state. -/
theorem encoder_frame
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) :
    encoder (n := n) (KemSK := KemSK) (source := source) writer view =
      StateT.lift (simulateQ writer
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket view)).run) := by
  let work := (AdapterRegistrationWriterRequestExtraction.encodeInit
    (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) (RegistrationNativePlatformWriter.initPacket view)).run
  change RegistrationNativePlatformBundleLower.lower (StateT.lift (StateT.lift
    (simulateQ (fun query => StateT.lift (writer query) : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E)
      (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp))) work))) =
    StateT.lift (simulateQ writer work)
  rw [simulate_lift]
  funext before previous
  simp only [RegistrationNativePlatformBundleLower.lower, StateT.run, lift_apply, map_apply, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame.encoder_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame.encoder_frame
