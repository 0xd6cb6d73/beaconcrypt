-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformViewStable
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! Earlier raw ML receipt payloads remain private analysis data. The actual source callbacks ignore them while retaining all World fields, cache coordinates, request markers and persistent platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxRunner (M privateWork publicWork)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {I KemSK Reader Response Auxiliary Platform E A B : Type} {base : OracleSpec I}

def view (before : State n Auxiliary × Platform) : State n Auxiliary × Platform :=
  (RegistrationNativePlatformIdentityReceiptView.view before.1, before.2)

def Stable (work : M (State n Auxiliary) Platform A) : Prop :=
  RegistrationNativePlatformViewStable.Stable view (pack work)

theorem view_idempotent (before : State n Auxiliary × Platform) : view (view before) = view before := rfl

theorem pure_stable (value : A) : Stable (pure value : M (State n Auxiliary) Platform A) := by
  unfold Stable
  rw [RegistrationNativePlatformPackedState.pure_pack]
  exact RegistrationNativePlatformViewStable.pure_stable view view_idempotent value

theorem bind_stable (work : M (State n Auxiliary) Platform A) (next : A → M (State n Auxiliary) Platform B)
    (first : Stable work) (following : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  unfold Stable at *
  rw [RegistrationNativePlatformPackedState.bind_pack]
  exact RegistrationNativePlatformViewStable.bind_stable view _ _ first following

theorem map_stable (work : M (State n Auxiliary) Platform A) (observe : A → B) (stable : Stable work) :
    Stable (observe <$> work) := by
  simpa only [bind_pure_comp] using bind_stable work (fun value => pure (observe value)) stable (fun value => pure_stable (observe value))

theorem program_stable {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (M (State n Auxiliary) Platform)) (law : ∀ query, Stable (handler query))
    (work : OracleComp queries A) : Stable (simulateQ handler work) := by
  unfold Stable at *
  rw [RegistrationNativePlatformPackedState.simulate_pack]
  exact RegistrationNativePlatformViewStable.program_stable view view_idempotent _ law work

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual private callbacks keep the same complete projected native and P outputs. -/
theorem private_stable (work : StateT (State n Auxiliary) (OracleComp RegistrationNativePlatformCtxBackend.Spec) A)
    (law : RegistrationNativePlatformIdentityReceiptView.Stable work) : Stable (privateWork work : M (State n Auxiliary) Platform A) := by
  rintro ⟨before, previous⟩
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, previous))) <$> distribution) (law before)
  simpa only [RegistrationNativePlatformPackedState.pack, privateWork, StateT.run, StateT.lift,
    bind_pure_comp, Functor.map_map, view, Prod.map_def, id_eq] using same

/-- Public allocator/writer callbacks have no prior raw-receipt input and retain the same external poststate. -/
theorem public_stable (work : StateT Platform ProbComp A) : Stable (publicWork work : M (State n Auxiliary) Platform A) := by
  rintro ⟨before, previous⟩
  simp only [RegistrationNativePlatformPackedState.pack, publicWork, StateT.run, Functor.map_map,
    view, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- The actual source record marker changes only the retained request journal. -/
theorem marker_stable (query : RegistrationRecordPrimitives.Spec.Domain) :
    Stable (modify (fun before : State n Auxiliary => {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}) : M (State n Auxiliary) Platform Unit) := by
  rintro ⟨before, previous⟩
  simp only [RegistrationNativePlatformPackedState.pack, StateT.run, state_modify_apply, state_pure_apply, map_pure,
    view, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

/-- Complete record callbacks retain their real KDF/hash/AEAD work and request marker independently of earlier raw signing bytes. -/
theorem records_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    RegistrationNativePlatformIdentityReceiptView.Stable (RegistrationNativePlatformCtxLocal.records (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  intro before
  have body := RegistrationNativePlatformViewStable.program_stable RegistrationNativePlatformIdentityReceiptView.view
    (fun _ => rfl) (RegistrationNativePlatformCtxLocal.shared (n := n) (Auxiliary := Auxiliary) setup codec)
    (RegistrationNativePlatformIdentityReceiptView.shared setup codec) (RegistrationRecordPrimitives.callbacks setup.source query)
  have same := congrArg (fun distribution => (fun result => (result.1,
    {result.2 with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall query]})) <$> distribution) (body before)
  simpa only [RegistrationNativePlatformCtxLocal.records, StateT.run, Functor.map_map,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] using same
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.pure_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.pure_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.bind_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.bind_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.map_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.map_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.program_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.private_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.private_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.public_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.public_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.marker_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.marker_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.records_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxReceiptView.records_stable
