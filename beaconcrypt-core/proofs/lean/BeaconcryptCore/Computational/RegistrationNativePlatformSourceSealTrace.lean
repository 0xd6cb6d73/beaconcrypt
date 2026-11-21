-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes

/-! The actual source seal, mutable commitment hash and raw writer run with one shared external platform state. Successful first-record execution supplies literal supported callback receipts in this same joint execution, before any response-signing, encoding or peer-installation outcome. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform Value Next ι KemSK Reader Response : Type} {base : OracleSpec ι}

def joint {Native : Type} (work : StateT Native (StateT Platform ProbComp) Value) :
    StateT (Native × Platform) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> ((work.run before.1).run before.2)

private theorem joint_pure {Native : Type} (value : Value) :
    joint (pure value : StateT Native (StateT Platform ProbComp) Value) = pure value := by
  funext before
  simp only [joint, StateT.run_pure, map_pure]
  rfl

private theorem joint_bind {Native : Type} (work : StateT Native (StateT Platform ProbComp) Value)
    (next : Value → StateT Native (StateT Platform ProbComp) Next) :
    joint (work >>= next) = (joint work >>= fun value => joint (next value)) := by
  funext before
  simp only [joint, StateT.run, StateT.monad_bind_def, StateT.bind,
    map_bind, bind_map_left]

private theorem joint_hom {Native : Type} :
    Cslib.IsMonadHom (StateT Native (StateT Platform ProbComp)) (StateT (Native × Platform) ProbComp) joint :=
  .mk' joint_pure joint_bind

variable [primitive : AdapterSealPrimitive.Operations]

noncomputable def record (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) :
    StateT (Local n) (StateT Platform ProbComp) (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformSourceRecord.fromInitialWithHash
    (RegistrationNativePlatformServerCompletion.records coins setup codec)
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper) initial

/-- Literal source callback specialization, retaining both private native state and external platform state. -/
theorem record_joint (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) :
    joint (record (n := n) coins setup codec view failure allocation erased helper initial) =
      RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (fun query => joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
        (fun request => joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
        (fun transcript => joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
        (fun request => joint (RegistrationNativePlatformSourceBuild.write helper request)) initial :=
  RegistrationNativePlatformSourceRecord.fromInitialWithHash_map joint_hom _ _ _ _ initial

/-- Supported source success supplies all five actual callback cuts, including full enclosing RustM results and actual later cache state. -/
theorem run (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (before after : Local n × Platform)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((joint (record coins setup codec view failure allocation erased helper initial)).run before)) :
    Nonempty (RegistrationNativePlatformRecordTrace.Trace
      (fun query => joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
      (fun request => joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
      (fun transcript => joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
      (fun request => joint (RegistrationNativePlatformSourceBuild.write helper request)) initial completed before after) := by
  rw [record_joint] at supported
  exact RegistrationNativePlatformRecordTrace.run _ _ _ _ initial completed before after supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace.record_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace.record_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace.run
