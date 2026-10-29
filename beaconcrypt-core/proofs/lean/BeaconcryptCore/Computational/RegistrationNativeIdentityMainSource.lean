-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMain
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceConstruction
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned

/-! The private interpretation of the whole opaque-identity native client runs the ordinary indexed source and treats prefix candidate reports as ghost operations. Reassembly restores identity seeds only from the private source table, retaining the full original native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource
open PqxdhJointPhase1Reports (ProtocolSpec)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityMain (State M)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def implementation (joint : PqxdhJointIdentity.Primitives) : QueryImpl ProtocolSpec (StateT SourceState ProbComp)
  | .inl query => PqxdhDynamicIdentityPool.lazyImpl joint query
  | .inr _ => pure ()

def interpret (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK mlSource Value) :
    StateT (State n KemSK mlSource × SourceState) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation joint) (work.run before.1)).run before.2

def project (before : State n KemSK mlSource × SourceState) : RegistrationNativeExperiment.State n KemSK mlSource :=
  ⟨before.1.context.server, RegistrationNativeIdentityRealization.owners before.2 before.1.beacons,
    before.1.context.kem, before.1.context.parsedAccepts⟩

def Owned (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK mlSource × SourceState) : Prop :=
  RegistrationNativeIdentityRealization.Owned joint before.2 before.1.beacons

/-- The executable compiler's indexed operation is interpreted by the literal ordinary private joint source. -/
theorem dynamic_program (joint : PqxdhJointIdentity.Primitives)
    (work : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value) (before : SourceState) :
    (simulateQ (implementation joint) (simulateQ RegistrationNativeIdentityMain.dynamicLift work)).run before =
      (simulateQ (PqxdhDynamicIdentityPool.lazyImpl joint) work).run before := by
  have composed : implementation joint ∘ₛ RegistrationNativeIdentityMain.dynamicLift =
      PqxdhDynamicIdentityPool.lazyImpl joint := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativeIdentityMain.dynamicLift, simulateQ_spec_query, implementation]
  rw [← QueryImpl.simulateQ_compose, composed]

/-- Ordinary already-counted native coins retain their actual literal replies and all private generated seeds. -/
theorem coins_source (joint : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    Prod.map id RegistrationNativeIdentityCompiler.poolView <$>
      (simulateQ (implementation joint) (simulateQ RegistrationNativeIdentityMain.coins work)).run before =
      (fun value => (value, RegistrationNativeIdentityCompiler.poolView before)) <$> work := by
  have composed : implementation joint ∘ₛ RegistrationNativeIdentityMain.coins =
      PqxdhDynamicIdentityPool.lazyImpl joint ∘ₛ RegistrationNativeIdentityCompiler.coins := by
    funext query
    rfl
  rw [← QueryImpl.simulateQ_compose, composed, QueryImpl.simulateQ_compose]
  exact RegistrationNativeIdentityCompiler.coins_source joint work before

/-- Clearing the joint game's extra uniform transcript entries preserves every actual native field. -/
theorem project_pool_view (before : State n KemSK mlSource) (pool : SourceState) :
    project (before, RegistrationNativeIdentityCompiler.poolView pool) = project (before, pool) := rfl

/-- Every candidate report is an exact no-op in the source interpretation, including arbitrary aliases and rejected candidates. -/
theorem emit_source (joint : PqxdhJointIdentity.Primitives)
    (reports : List PqxdhJointPhase1Reports.CandidateReport) (before : SourceState) :
    (simulateQ (implementation joint) (RegistrationNativeIdentityMain.emit reports)).run before = pure ((), before) := by
  induction reports with
  | nil => rfl
  | cons report rest ih =>
      simp only [RegistrationNativeIdentityMain.emit, simulateQ_bind, simulateQ_spec_query,
        implementation, pure_bind, ih]

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.dynamic_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.dynamic_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.coins_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.project_pool_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.project_pool_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.emit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource.emit_source
