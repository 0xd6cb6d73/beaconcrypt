-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
import Cslib.Foundations.Control.Monad.IsMonadHom

/-! The indexed Ed compiler has a substitutable ambient backend. Identity operations remain the same generated joint-service requests and preserve the exact32-draw creation charge. The common CTX/ordinary backend is interpreted independently, so its physical cache can stay private. Theorems commute arbitrary lawful interpreters through the complete frontend and Main state; no whole-handler/source-security equation is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityMain (State)
open PqxdhDynamicIdentityPool (PoolSpec DynamicSpec)
variable {n : Nat} {KemSK Platform Value : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]

abbrev Client (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) (m : Type → Type) :=
  StateT (State n KemSK source × Platform) m

/-- Only genuine identity creation charges its actual32 native uniform draws. External coins and ambient work retain their separate interpreters. -/
def implementation (coins : QueryImpl unifSpec m) (joint : QueryImpl PoolSpec m)
    (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) m)) :
    QueryImpl (RegistrationNativePlatformIdentityProgram.Spec n KemSK) (StateT (Context n KemSK) m)
  | .inl query => fun before => (fun reply => (reply, before)) <$> coins query
  | .inr (.inl query) => ambient query
  | .inr (.inr .create) => fun before => (fun reply => (reply, RegistrationNativeIdentityCompiler.advance before)) <$> joint .create
  | .inr (.inr (.service handle request)) => fun before => (fun reply => (reply, before)) <$> joint (.service handle request)
  | .inr (.inr (.reveal handle)) => fun before => (fun reply => (reply, before)) <$> joint (.reveal handle)

private def assemble (result : (((Value × RegistrationNativeIdentityFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform) × Context n KemSK) :
    Value × (State n KemSK source × Platform) :=
  (result.1.1.1.1, ({
    context := { result.2 with server := { result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.1.2 result.2.server.world.world.1 } }
    beacons := result.1.1.1.2 }, result.1.2))

/-- The same actual opaque-owner/Env/Main joins work over a shared symbolic or physical hash backend. -/
def beacon (coins : QueryImpl unifSpec m) (joint : QueryImpl PoolSpec m)
    (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) m))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value) :
    Client n KemSK Platform source m Value := fun before =>
  assemble <$> (simulateQ (implementation coins joint ambient)
    (((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)).run before.2)).run before.1.context

/-- Auxiliary current-runtime commands preserve the same opaque owner roster and use only the supplied common backend. -/
def ordinary (work : StateT (Context n KemSK × Platform) m Value) : Client n KemSK Platform source m Value := fun before =>
  (fun result => (result.1, ({ before.1 with context := result.2.1 }, result.2.2))) <$> work.run (before.1.context, before.2)

section Natural
variable {right : Type → Type} [Monad right]
variable {F : ∀ {A : Type}, m A → right A}
variable (hom : Cslib.IsMonadHom m right F)
include hom

/-- Interpretation commutes at each literal ambient/coin/joint capability. -/
theorem query_natural (coins : QueryImpl unifSpec m) (joint : QueryImpl PoolSpec m)
    (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) m))
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain) (before : Context n KemSK) :
    F ((implementation coins joint ambient query).run before) =
      (implementation (fun query => F (coins query)) (fun query => F (joint query))
        (fun query current => F ((ambient query).run current)) query).run before := by
  cases query with
  | inl query => exact hom.map_map _ _
  | inr query => cases query with
    | inl query => rfl
    | inr query => cases query <;> exact hom.map_map _ _

variable [LawfulMonad m] [LawfulMonad right]

/-- Every adaptive frontend branch commutes with the same interpreter, retaining the complete reached Context. -/
theorem program_natural (coins : QueryImpl unifSpec m) (joint : QueryImpl PoolSpec m)
    (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) m))
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value) (before : Context n KemSK) :
    F ((simulateQ (implementation coins joint ambient) work).run before) =
      (simulateQ (implementation (fun query => F (coins query)) (fun query => F (joint query))
        (fun query current => F ((ambient query).run current))) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact hom.map_pure _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hom.map_bind]
    rw [query_natural hom]
    exact bind_congr (fun result => ih result.1 result.2)

/-- The complete owner/Env/Main/P closing operation preserves the same interpreted source state and result. -/
theorem beacon_natural (coins : QueryImpl unifSpec m) (joint : QueryImpl PoolSpec m)
    (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) m))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (before : State n KemSK source × Platform) :
    F ((beacon coins joint ambient work).run before) =
      (beacon (fun query => F (coins query)) (fun query => F (joint query))
        (fun query current => F ((ambient query).run current)) work).run before := by
  change F (assemble <$> _) = assemble <$> _
  rw [hom.map_map, program_natural hom]

omit [LawfulMonad m] [LawfulMonad right] in
/-- Literal auxiliary work commutes while retaining the full opaque roster and external state. -/
theorem ordinary_natural (work : StateT (Context n KemSK × Platform) m Value) (before : State n KemSK source × Platform) :
    F ((ordinary (source := source) work).run before) =
      (ordinary (fun current => F (work.run current))).run before := hom.map_map _ _
/-- Full adaptive Main-level compilation also commutes with the same common interpreter and retains every reached owner/context/P coordinate. -/
theorem main_program_natural {I : Type} {queries : OracleSpec.{0, 0} I}
    (handler : QueryImpl queries (Client n KemSK Platform source m))
    (work : OracleComp queries Value) (before : State n KemSK source × Platform) :
    F ((simulateQ handler work).run before) =
      StateT.run (simulateQ (r := Client n KemSK Platform source right)
        (fun query current => F ((handler query).run current)) work) before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact hom.map_pure _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hom.map_bind]
    exact bind_congr (fun result => ih result.1 result.2)

end Natural

/-- The executable client has one generated joint-service branch and one shared CTX hash branch. -/
abbrev Spec := PqxdhJointPhase1Reports.ProtocolSpec + RegistrationNativePlatformCtxBackend.HashSpec

def protocol : QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

def backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec (OracleComp Spec)
  | .inl bytes => Spec.query (.inr bytes)
  | .inr query => Spec.query (.inl (.inl (.inl query)))

def joint : QueryImpl PoolSpec (OracleComp Spec) := fun query => Spec.query (.inl (.inl (.inr query)))
def coins : QueryImpl unifSpec (OracleComp Spec) := fun query => Spec.query (.inl (.inl (.inl query)))

/-- A concrete ambient free hash program can be plugged into the same indexed owner compiler without exposing the physical cache to its executable state. -/
def free (ambient : QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK)
    (StateT (Context n KemSK) (OracleComp RegistrationNativePlatformCtxBackend.Spec))) :=
  implementation coins joint (fun query current => simulateQ backend ((ambient query).run current))

private theorem lift_apply {S A : Type} [LawfulMonad m] (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

omit [Monad m] in
/-- Specializing only the ambient backend recovers the already checked literal actual indexed compiler, including true creation costs and external coins. -/
theorem legacy {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    implementation RegistrationNativeIdentityCompiler.coins
      (fun query => (DynamicSpec.query (.inr query) : OracleComp DynamicSpec _))
      (fun query current => simulateQ RegistrationNativeIdentityCompiler.coins
        ((RegistrationNativeIdentityWorld.ambient (n := n) (mlSource := source) setup checks representation created query).run current)) =
      RegistrationNativePlatformIdentityCompiler.implementation (n := n) (source := source) setup checks representation created := by
  funext query before
  cases query with
  | inl query =>
    simp only [implementation, RegistrationNativeIdentityCompiler.coins,
      RegistrationNativePlatformIdentityCompiler.implementation, lift_apply]
  | inr query => cases query with
    | inl query => rfl
    | inr query => cases query with
      | create =>
        simp only [implementation, RegistrationNativePlatformIdentityCompiler.implementation,
          RegistrationNativeIdentityCompiler.implementation, bind_pure_comp]
        rfl
      | service handle request | reveal handle =>
        simp only [implementation, RegistrationNativePlatformIdentityCompiler.implementation,
          RegistrationNativeIdentityCompiler.implementation, lift_apply]
        rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.query_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.query_natural
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.program_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.program_natural
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.beacon_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.beacon_natural
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.ordinary_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.ordinary_natural
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.main_program_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.main_program_natural
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler.legacy
