-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal open indexed-KEM reference AST is interpreted in a common stateful monad. Preparation, material and publication callbacks can carry arbitrary real platform effects. Ordinary World effects and indexed KEM calls use their existing source bodies under the same coin interpreter, retaining the entire provider pool and private callback state. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeKemReferenceCompiler (Spec)
open RegistrationNativeKemReferenceWorld (Private)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

structure Callbacks (n : Nat) (KemSK Extra : Type) (m : Type → Type) where
  other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp
  prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) m)
  demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
    (StateT (Private n KemSK Extra) m)
  publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m)

noncomputable def handler (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra m) :
    QueryImpl (Spec n KemSK) (StateT (Private n KemSK Extra) m)
  | .inl message => callbacks.prepare message
  | .inr (.inl (.inl message)) => callbacks.demand message
  | .inr (.inl (.inr (.inl query))) => callbacks.publication query
  | .inr (.inl (.inr (.inr query))) => RegistrationNativePlatformInterpret.state coins (RegistrationNativeKemReferenceWorld.effect query)
  | .inr (.inr query) => RegistrationNativePlatformInterpret.state coins (RegistrationNativeKemReferenceWorld.kem setup callbacks.other query)

def liftCallbacks (coins : QueryImpl unifSpec m) (callbacks : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra) :
    Callbacks n KemSK Extra m where
  other := callbacks.other
  prepare := fun query => RegistrationNativePlatformInterpret.state coins (callbacks.prepare query)
  demand := fun query => RegistrationNativePlatformInterpret.state coins (callbacks.demand query)
  publication := fun query => RegistrationNativePlatformInterpret.state coins (callbacks.publication query)

omit [LawfulMonad m] in
theorem handler_lift (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra) (query : (Spec n KemSK).Domain) :
    handler coins setup (liftCallbacks coins callbacks) query =
      RegistrationNativePlatformInterpret.state coins (RegistrationNativeKemReferenceEffects.implementation setup callbacks query) := by
  cases query with
  | inl _ => rfl
  | inr query => cases query with
    | inr _ => rfl
    | inl query => cases query with
      | inl _ => rfl
      | inr query => cases query <;> rfl

def environment (implementation : QueryImpl (Spec n KemSK) m)
    (work : StateT Environment (OracleComp (Spec n KemSK)) Value) : StateT Environment m Value :=
  fun before => simulateQ implementation (work.run before)

noncomputable def collect (implementation : QueryImpl (Spec n KemSK) m)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :=
  environment implementation (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)

noncomputable def agreement (implementation : QueryImpl (Spec n KemSK) m)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT RegistrationServerMaterialFrontend.State (StateT Environment m) (RustM (Option RegistrationServerReferenceRoot.Ready)) :=
  fun before => environment implementation ((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before)

noncomputable def localAgreement (implementation : QueryImpl (Spec n KemSK) m)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment m (RustM (Option RegistrationServerReferenceRoot.Ready)) :=
  environment implementation (do
    let input ← RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated
    match input with
    | none => pure (.ok none)
    | some input => StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.prepare
      (RegistrationServerReferenceRoot.client authenticated.binding input)))

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

attribute [local irreducible] RegistrationNativeKemReferenceCompiler.collect RegistrationServerReferenceRoot.client

set_option maxHeartbeats 1000000 in
theorem agreement_factor (implementation : QueryImpl (Spec n KemSK) m)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    agreement implementation setup checks packet authenticated =
      StateT.lift (localAgreement implementation setup checks packet authenticated) := by
  funext before env
  change ((agreement implementation setup checks packet authenticated).run before).run env =
    ((StateT.lift (localAgreement implementation setup checks packet authenticated)).run before).run env
  rw [StateT.run_lift, bind_pure_comp, StateT.run_map]
  change simulateQ implementation (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env) =
    Prod.map (fun value => (value, before)) id <$> (localAgreement implementation setup checks packet authenticated).run env
  unfold localAgreement environment
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, simulateQ_bind]
  simp only [StateT.run, map_bind]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input <;> simp only [StateT.lift, bind_pure_comp, state_map_apply, state_pure_apply,
    simulateQ_pure, simulateQ_map, map_pure, Functor.map_map]
  all_goals rfl


def closeEnvironment (work : StateT Environment (StateT (Private n KemSK Extra) m) Value) :
    StateT (RegistrationNativeKemReferenceBackend.State n KemSK Extra) m Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> ((work.run before.1).run before.2)

theorem environment_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (callbacks : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (work : StateT Environment (OracleComp (Spec n KemSK)) Value)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    (closeEnvironment (environment (handler coins setup (liftCallbacks coins callbacks)) work)).run before =
      simulateQ coins ((RegistrationNativeKemReferencePrefix.lower setup callbacks work).run before) := by
  have handlerEq : handler coins setup (liftCallbacks coins callbacks) =
      fun query => RegistrationNativePlatformInterpret.state coins (RegistrationNativeKemReferenceEffects.implementation setup callbacks query) :=
    funext (handler_lift coins setup callbacks)
  unfold closeEnvironment environment
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((simulateQ (handler coins setup (liftCallbacks coins callbacks)) (work.run before.1)).run before.2) = _
  rw [handlerEq, ← RegistrationNativePlatformInterpret.state_simulate]
  simp only [RegistrationNativePlatformInterpret.state, RegistrationNativeKemReferencePrefix.lower, StateT.run, simulateQ_map]

omit [LawfulMonad m] in
theorem handler_independent (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (left right : Callbacks n KemSK Extra m) (sameOther : left.other = right.other)
    (samePrepare : left.prepare = right.prepare) (query : (Spec n KemSK).Domain)
    (allowed : ¬ RegistrationNativePlatformServerOpenServiceFree.IsService query) :
    handler coins setup left query = handler coins setup right query := by
  cases query with
  | inl message => exact congrFun samePrepare message
  | inr query => cases query with
    | inr query => simp only [handler, sameOther]
    | inl query => cases query with
      | inl message => exact (allowed trivial).elim
      | inr query => cases query with
        | inl query => exact (allowed trivial).elim
        | inr query => rfl

theorem collect_independent (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (left right : Callbacks n KemSK Extra m) (sameOther : left.other = right.other)
    (samePrepare : left.prepare = right.prepare)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    collect (handler coins setup left) setup checks packet authenticated =
      collect (handler coins setup right) setup checks packet authenticated := by
  funext before
  exact RegistrationNativePlatformServerOpenServiceFree.simulate_zero _ _ _
    (handler_independent coins setup left right sameOther samePrepare)
    _ (RegistrationNativePlatformServerOpenServiceFree.collect_free setup checks packet authenticated before)

theorem localAgreement_independent (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (left right : Callbacks n KemSK Extra m) (sameOther : left.other = right.other)
    (samePrepare : left.prepare = right.prepare)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    localAgreement (handler coins setup left) setup checks packet authenticated =
      localAgreement (handler coins setup right) setup checks packet authenticated := by
  funext before
  exact RegistrationNativePlatformServerOpenServiceFree.simulate_zero _ _ _
    (handler_independent coins setup left right sameOther samePrepare)
    _ (RegistrationNativePlatformServerOpenServiceFree.local_free setup checks packet authenticated before)

theorem agreement_independent (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (left right : Callbacks n KemSK Extra m) (sameOther : left.other = right.other)
    (samePrepare : left.prepare = right.prepare)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    agreement (handler coins setup left) setup checks packet authenticated =
      agreement (handler coins setup right) setup checks packet authenticated := by
  rw [agreement_factor, agreement_factor, localAgreement_independent coins setup checks left right sameOther samePrepare]

theorem localAgreement_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (callbacks : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    (closeEnvironment (localAgreement (handler coins setup (liftCallbacks coins
      (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember callbacks))) setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember callbacks packet authenticated).run before) := by
  exact environment_source coins setup _ _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.handler_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.handler_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.agreement_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.agreement_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.environment_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.handler_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.handler_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.collect_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.collect_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.localAgreement_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.localAgreement_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.agreement_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.agreement_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.localAgreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel.localAgreement_source
