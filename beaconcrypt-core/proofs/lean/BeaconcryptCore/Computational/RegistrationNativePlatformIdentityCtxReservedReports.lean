-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource

/-! A source-erased ghost observer reports every reserved public-key alias before the original accept callback. Future uncreated aliases are included internally without changing a Native request, reply or source state. The observer receives public keys only; private reserved seeds remain in the primitive interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhJointIdentity (PublicIdentity)
variable {count : Nat} {S Value : Type}

def emit (reports : List PqxdhJointPhase1Reports.CandidateReport) : OracleComp Spec Unit :=
  simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol (RegistrationNativeIdentityMain.emit reports)

def wrap (keys : Fin count → PublicIdentity) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) :
    QueryImpl TypedSpec (StateT S (OracleComp Spec))
  | .inr (.accept packet) => do
      let _ ← StateT.lift (emit (PqxdhJointReservedPhase1Reports.packetReports keys packet))
      frontend (.inr (.accept packet))
  | query => frontend query

/-- All new reports are literal no-ops in the honest private source, retaining its complete generated pool and physical hash state. -/
theorem emit_source (joint : PqxdhJointIdentity.Primitives)
    (reports : List PqxdhJointPhase1Reports.CandidateReport) (before : State) :
    (simulateQ (implementation joint) (emit reports)).run before = pure ((), before) := by
  rw [emit, RegistrationNativePlatformIdentityCtxSource.protocol_source,
    RegistrationNativeIdentityMainSource.emit_source, map_pure]

noncomputable def callback (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) :
    QueryImpl TypedSpec (StateT (S × State) ProbComp) := QueryImpl.Stateful.link frontend (implementation joint)

private theorem bind_apply {T A B : Type} {m : Type → Type} [Monad m]
    (work : StateT T m A) (next : A → StateT T m B) (before : T) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem lift_apply {T A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : T) :
    (StateT.lift work : StateT T m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem map_apply {T A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT T m A) (before : T) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The original accept and every other callback have exactly their original full private interpretation after inserting the unrestricted reserved-family reports. -/
theorem query_source (joint : PqxdhJointIdentity.Primitives) (keys : Fin count → PublicIdentity)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain) (before : S × State) :
    (callback joint (wrap keys frontend) query).run before = (callback joint frontend query).run before := by
  cases query with
  | inl coin => rfl
  | inr query =>
    cases query <;> try rfl
    case accept packet =>
      rw [callback, QueryImpl.Stateful.link_impl_apply_run, callback, QueryImpl.Stateful.link_impl_apply_run]
      simp only [wrap, StateT.run, bind_apply, lift_apply, bind_map_left, simulateQ_bind,
        map_bind]
      have report := emit_source joint (PqxdhJointReservedPhase1Reports.packetReports keys packet) before.2
      change simulateQ (implementation joint) (emit (PqxdhJointReservedPhase1Reports.packetReports keys packet)) before.2 = pure ((), before.2) at report
      rw [report, pure_bind]

/-- Ghost reservation coverage preserves the exact continued adaptive source distribution, including failed accepts and all private/P poststates. -/
theorem program_source (joint : PqxdhJointIdentity.Primitives) (keys : Fin count → PublicIdentity)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec Value) (before : S × State) :
    (simulateQ (callback joint (wrap keys frontend)) work).run before = (simulateQ (callback joint frontend) work).run before := by
  have same : callback joint (wrap keys frontend) = callback joint frontend := by
    funext query current
    exact query_source joint keys frontend query current
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.emit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.emit_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedReports.program_source
