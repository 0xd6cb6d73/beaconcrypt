-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource

/-! The shared private hash interpreter closes the actual owner/Env/Main/P lens. Physical CTX addresses remain in the private backend; the executable indexed Main state retains only its original local cache coordinate. The operational projection restores the complete source cache and generated service table, not merely a public value marginal. Censored receipt/history realization remains a separate relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {I KemSK Platform Value : Type} {base : OracleSpec I} {n : Nat} {source : RegistrationNativeMldsa.Source}

abbrev M (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (State n KemSK source × Platform) (OracleComp Spec)
abbrev Full (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  (State n KemSK source × Platform) × RegistrationNativePlatformIdentityCtxSource.State

noncomputable def beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value) :
    M n KemSK Platform source Value :=
  RegistrationNativePlatformIdentityCtxCompiler.beacon RegistrationNativePlatformIdentityCtxCompiler.coins
    RegistrationNativePlatformIdentityCtxCompiler.joint
    (fun query current => simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend
      ((RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created query).run current)) work

noncomputable def interpret (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK Platform source Value) :
    StateT (Full n KemSK Platform source) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) (work.run before.1)).run before.2

def project (before : Full n KemSK Platform source) :
    (State n KemSK source × Platform) × PqxdhDynamicIdentityPool.SourceState :=
  (({before.1.1 with context := RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context}, before.1.2),
    RegistrationNativeIdentityCompiler.poolView before.2.1)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem compiled_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value)
    (before : RegistrationNativePlatformIdentityCtxCompilerSource.Full n KemSK) :
    (simulateQ (RegistrationNativePlatformIdentityCtxCompilerSource.implementation (source := source) setup checks representation created) work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
          ((simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
            (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run before.1)).run before.2 := by
  have linked : RegistrationNativePlatformIdentityCtxCompilerSource.implementation (n := n) (source := source) setup checks representation created =
      QueryImpl.Stateful.link (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created))
        (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) := by
    funext query current
    rfl
  rw [linked, QueryImpl.Stateful.simulateQ_link_run]
  rfl

/-- The actual effectful source frontend closes through the same private hash/joint interpreter with every owner, Env field, native counter and external poststate retained. -/
theorem beacon_execution (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (before : Full n KemSK Platform source) :
    Prod.map id project <$> (interpret setup.joint (beacon setup checks representation created work)).run before =
      RegistrationNativePlatformIdentityMain.assemble <$>
        (simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created)
          (((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2)).run
            ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,
              RegistrationNativeIdentityCompiler.poolView before.2.1⟩ := by
  let script := ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2
  have same := congrArg (fun distribution => RegistrationNativePlatformIdentityMain.assemble <$> distribution)
    (RegistrationNativePlatformIdentityCtxCompilerSource.complete (source := source) setup checks representation created script
      (before.1.1.context, before.2))
  rw [compiled_program] at same
  simp only [interpret, beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon, StateT.run,
    simulateQ_map, map_apply, RegistrationNativePlatformIdentityCtxCompiler.free, Functor.map_map, Prod.map_def, id_eq,
    project, RegistrationNativePlatformIdentityMain.assemble,
    RegistrationNativePlatformIdentityCtxCompilerSource.project,
    RegistrationNativePlatformIdentityCtxAmbient.replace, RegistrationNativePlatformCtxCacheFrame.replace,
    script] at same ⊢
  exact same

/-- Closing the shared backend gives the same complete prior ordinary indexed Main execution after its explicit uniform-transcript projection. -/
theorem beacon_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (before : Full n KemSK Platform source) :
    Prod.map id project <$> (interpret setup.joint (beacon setup checks representation created work)).run before =
      Prod.map id RegistrationNativePlatformIdentityMain.poolProjection <$>
        (RegistrationNativePlatformIdentityMain.interpret setup.joint
          (RegistrationNativePlatformIdentityMain.beacon setup checks representation created work)).run
          (({before.1.1 with context := RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context}, before.1.2), before.2.1) := by
  rw [beacon_execution, RegistrationNativePlatformIdentityMain.beacon_execution]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain.beacon_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain.beacon_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain.beacon_source
