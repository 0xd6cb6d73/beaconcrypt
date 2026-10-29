-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup

/-! Public one-use Server capabilities reconstruct native consumed tokens only inside the private source interpretation. Material services use the caller's current local World and chronological signing receipts, while the executable frontend retains no root or generated kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialSourceState
variable {n : Nat} {Value : Type}

abbrev State (n : Nat) := RegistrationServerMaterialFrontend.State × RegistrationServerRootCompiler.Local n

def project (roots : RegistrationServerReferenceRestore.Roots) (before : State n) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceRestore.restore roots before.1 (RegistrationServerRecordWorldSource.project before.2)

def nativeView (before : RegistrationServerFrontendCompiler.State n) : RegistrationServerFrontendCompiler.State n :=
  { before with world := RegistrationServerRecordWorldSource.project before.world }

def restore (roots : RegistrationServerReferenceRestore.Roots) (before : State n) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceRestore.restore roots before.1 before.2

/-- Source reconstruction keeps its full native instrumentation before the output view is applied. -/
theorem view_restore (roots : RegistrationServerReferenceRestore.Roots) (before : State n) :
    nativeView (restore roots before) = project roots before := rfl

noncomputable def service (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n)
      (StateT (RegistrationServerRootCompiler.Local n) ProbComp)
  | .inl message => pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot hkdf (roots message))))
  | .inr query => RegistrationServerKnownStageWorldSource.common hkdf writer sign query

noncomputable def close (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (work : StateT RegistrationServerMaterialFrontend.State
      (OracleComp (RegistrationServerMaterialFrontend.Spec n)) Value) : StateT (State n) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (service hkdf writer sign roots) (work.run before.1)).run before.2

/-- Native publication commit changes exactly the same public frontend control on every failure or successful response. -/
theorem commit (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (before : State n) :
    Prod.map id (project roots) <$>
      (close hkdf writer sign roots (RegistrationServerMaterialFrontend.finish published)).run before =
      (RegistrationServerSdkSource.commit published).run (project roots before) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- Native commit has the same exact API response and source-view state when entered with the full actual local source state. -/
theorem commit_full (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (before : State n) :
    Prod.map id (project roots) <$>
      (close hkdf writer sign roots (RegistrationServerMaterialFrontend.finish published)).run before =
      Prod.map id nativeView <$> (RegistrationServerSdkSource.commit published).run (restore roots before) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- Taking a public capability consumes exactly its restored private native token before later application or primitive failure. -/
theorem take (roots : RegistrationServerReferenceRestore.Roots) (handle : Nat) (before : State n) :
    RegistrationServerSdkSource.take handle (project roots before) =
      ((RegistrationServerMaterialFrontend.take handle before.1).1.map (RegistrationServerReferenceRestore.token roots),
        project roots ((RegistrationServerMaterialFrontend.take handle before.1).2, before.2)) :=
  RegistrationServerReferenceRestore.take roots handle before.1 (RegistrationServerRecordWorldSource.project before.2)

end BeaconcryptCore.Computational.RegistrationServerMaterialSourceState

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.commit
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.take

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.view_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.view_restore
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.commit_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceState.commit_full
