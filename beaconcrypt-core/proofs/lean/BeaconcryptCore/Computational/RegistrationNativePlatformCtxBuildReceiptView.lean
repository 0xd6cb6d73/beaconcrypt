-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild
/-! The complete Context build ignores prior raw ML receipt payloads under an explicit view, with the KEM pool, every other native field, physical CTX state and persistent platform state retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformCtxContext (M)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

def context (before : Context n KemSK) : Context n KemSK :=
  {before with server := RegistrationNativePlatformCtxSdkReceiptView.serverView before.server}

def view (before : Context n KemSK × Platform) : Context n KemSK × Platform := (context before.1, before.2)

def Stable (work : M n KemSK Platform A) : Prop := RegistrationNativePlatformViewStable.Stable view work

/-- Receipt erasure leaves every other Context coordinate unchanged. -/
theorem view_idempotent (before : Context n KemSK × Platform) : view (view before) = view before := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The full Context lens retains the exact pool and external poststate from every actual SDK branch. -/
theorem server_stable (work : RegistrationNativePlatformCtxRunner.M (RegistrationServerFrontendCompiler.State n) Platform A)
    (law : RegistrationNativePlatformCtxSdkReceiptView.Stable work) : Stable (RegistrationNativePlatformCtxBuild.server work : M n KemSK Platform A) := by
  rintro ⟨before, previous⟩
  have same := congrArg (fun distribution => (fun result =>
    (result.1, ({before with server := result.2.1}, result.2.2))) <$> distribution) (law (before.server, previous))
  simpa only [RegistrationNativePlatformCtxBuild.server, RegistrationNativePlatformPackedState.pack,
    StateT.run, state_map_apply, Functor.map_map, view, context,
    RegistrationNativePlatformCtxSdkReceiptView.view, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] using same

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The literal current-runtime build has no prior-raw-receipt dependency; every source leaf and failed prefix is discharged internally. -/
theorem build_stable (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    Stable (RegistrationNativePlatformCtxBuild.build (n := n) setup codec keys failure allocation erased sign helper writer reserve handle application) := by
  apply RegistrationNativePlatformViewStable.map_stable view view_idempotent
  exact server_stable _ (RegistrationNativePlatformCtxSdkSourceReceiptView.build_stable setup codec keys failure allocation erased sign helper writer reserve handle application)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.server_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.server_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.build_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView.build_stable
