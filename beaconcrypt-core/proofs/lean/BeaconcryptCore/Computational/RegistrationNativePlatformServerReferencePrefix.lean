-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
import BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The original public primitive-prefix AST and public root-reference client run through caller-supplied effect and preparation callbacks in any lawful common monad. Source closure interprets only individual EnvEffects through the same coin handler; the existing extra forwarding counter projection is kept separate from actual native accounting. No private root value enters the executable agreement definition. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerReferenceRoot (Ready PrepareSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def environment (effects : QueryImpl (EnvEffects n) m)
    (work : StateT Environment (OracleComp (EnvEffects n)) Value) : StateT Environment m Value :=
  fun before => simulateQ effects (work.run before)

noncomputable def collect (effects : QueryImpl (EnvEffects n) m)
    (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment m (Option (PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)) :=
  environment effects (RegistrationServerReferenceCompilerNative.collect setup checks packet authenticated)

noncomputable def agreement (effects : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT RegistrationServerMaterialFrontend.State (StateT Environment m) (RustM (Option Ready)) := do
  let input ← StateT.lift (collect effects setup checks packet authenticated)
  match input with
  | none => pure (.ok none)
  | some input => StateT.lift (StateT.lift (simulateQ prepare (RegistrationServerReferenceRoot.client authenticated.binding input)))

noncomputable def effects (coins : QueryImpl unifSpec m) : QueryImpl (EnvEffects n) (StateT (PqxdhRecordLiftWorld.State n) m) :=
  fun query => RegistrationNativePlatformInterpret.state coins (PqxdhRecordLiftWorld.effects query)

def closeEnvironment (work : StateT Environment (StateT (PqxdhRecordLiftWorld.State n) m) Value) :
    StateT (RegistrationServerReferenceCompilerNative.Local n) m Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> ((work.run before.1).run before.2)

theorem environment_source (coins : QueryImpl unifSpec m)
    (work : StateT Environment (OracleComp (EnvEffects n)) Value)
    (before : RegistrationServerReferenceCompilerNative.Local n) :
    (closeEnvironment (environment (effects coins) work)).run before =
      simulateQ coins ((RegistrationServerReferenceCompilerNative.lower work).run before) := by
  unfold closeEnvironment environment effects
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((simulateQ (fun query => RegistrationNativePlatformInterpret.state coins (PqxdhRecordLiftWorld.effects query))
      (work.run before.1)).run before.2) = _
  rw [← RegistrationNativePlatformInterpret.state_simulate]
  simp only [RegistrationNativePlatformInterpret.state, RegistrationServerReferenceCompilerNative.lower,
    StateT.run, simulateQ_map]

theorem collect_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompilerNative.Local n) :
    Prod.map id RegistrationWorldAgreementProgramCompiler.project <$>
      (closeEnvironment (collect (effects coins) setup checks packet authenticated)).run before =
    simulateQ coins ((simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run
        (RegistrationWorldAgreementProgramCompiler.project before)) := by
  rw [collect, environment_source, ← simulateQ_map,
    RegistrationServerReferenceCompilerNative.collect_native setup checks packet authenticated before]


theorem environment_bind {Next : Type} (handler : QueryImpl (EnvEffects n) m)
    (work : StateT Environment (OracleComp (EnvEffects n)) Value)
    (next : Value → StateT Environment (OracleComp (EnvEffects n)) Next) :
    environment handler (work >>= next) = (environment handler work >>= fun value => environment handler (next value)) := by
  funext before
  change simulateQ handler ((work >>= next).run before) = _
  rw [StateT.run_bind, simulateQ_bind]
  rfl

noncomputable def localAgreement (handler : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment m (RustM (Option Ready)) := do
  let input ← collect handler setup checks packet authenticated
  match input with
  | none => pure (.ok none)
  | some input => StateT.lift (simulateQ prepare (RegistrationServerReferenceRoot.client authenticated.binding input))

theorem agreement_factor (handler : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    agreement handler prepare setup checks packet authenticated = StateT.lift (localAgreement handler prepare setup checks packet authenticated) := by
  apply StateT.ext
  intro before
  simp only [agreement, localAgreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply bind_congr
  intro input
  cases input <;> simp only [StateT.run_pure, StateT.run_lift, pure_bind]

theorem close_bind {Next : Type}
    (work : StateT Environment (StateT (PqxdhRecordLiftWorld.State n) m) Value)
    (next : Value → StateT Environment (StateT (PqxdhRecordLiftWorld.State n) m) Next) :
    closeEnvironment (work >>= next) = (closeEnvironment work >>= fun value => closeEnvironment (next value)) := by
  funext before
  simp only [closeEnvironment, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

theorem close_lift (work : StateT (PqxdhRecordLiftWorld.State n) m Value)
    (before : RegistrationServerReferenceCompilerNative.Local n) :
    (closeEnvironment (StateT.lift work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (((StateT.lift work : StateT Environment (StateT (PqxdhRecordLiftWorld.State n) m) Value).run before.1).run before.2) = _
  simp only [StateT.run_lift, bind_pure_comp]
  rw [StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.environment_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.collect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.environment_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.environment_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.agreement_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.agreement_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.close_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.close_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix.close_lift
