-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCaps
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual collector and preparation syntax does not invoke material-demand or publication callbacks. The zero-query result is structural for every reply, so changing these callbacks preserves the entire interpretation in an arbitrary lawful common monad, including all private state. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare)
open RegistrationNativeKemReferenceCompiler (backend collect visit)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- A zero query budget makes the excluded handlers irrelevant, without a support or success restriction. -/
theorem simulate_zero {Index : Type} {spec : OracleSpec Index} {m : Type → Type} [Monad m] [LawfulMonad m]
    (excluded : Index → Prop) [DecidablePred excluded]
    (left right : QueryImpl spec m)
    (same : ∀ query, ¬ excluded query → left query = right query)
    (work : OracleComp spec Value) (free : work.IsQueryBoundP excluded 0) :
    simulateQ left work = simulateQ right work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at free
    have allowed : ¬ excluded query := free.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [same query allowed]
    apply bind_congr
    intro reply
    apply ih reply
    simpa only [allowed, ite_false] using free.2 reply

def IsService : (Spec n KemSK).Domain → Prop
  | .inr (.inl (.inl _)) => True
  | .inr (.inl (.inr (.inl _))) => True
  | _ => False

instance : DecidablePred (IsService (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => cases query with
    | inr _ => exact isFalse id
    | inl query => cases query with
      | inl _ => exact isTrue trivial
      | inr query => cases query with
        | inl _ => exact isTrue trivial
        | inr _ => exact isFalse id

def OldService : (RegistrationServerReferenceCompiler.Spec n).Domain → Prop
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => True
  | _ => False

instance : DecidablePred (OldService (n := n)) := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => cases query with
    | inl _ => exact isTrue trivial
    | inr query => cases query with
      | inl _ => exact isTrue trivial
      | inr _ => exact isFalse id

private theorem lift_free (work : OracleComp (RegistrationServerReferenceCompiler.Spec n) Value)
    (bounded : work.IsQueryBoundP (OldService (n := n)) 0) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK)) work).IsQueryBoundP
      (IsService (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (OldService (n := n)) _ work 0 bounded
  intro query
  rcases query with _ | _ | _ | _ <;>
    simp [RegistrationNativeKemReferenceCompiler.lift, OldService, IsService, isQueryBoundP_query_iff]

private theorem old_backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((RegistrationServerReferenceCompiler.backend (n := n) setup checks query).run before).IsQueryBoundP
      (OldService (n := n)) 0 := by
  unfold RegistrationServerReferenceCompiler.backend RegistrationServerReferenceCompiler.liftEnvironment
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationServerReferenceCompiler.effect, OldService, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  cases query with
  | encapsulate key =>
    simp only [backend, StateT.run, isQueryBoundP_map_iff]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    simp [RegistrationBeaconReferenceCompiler.indexed, IsService, isQueryBoundP_query_iff]
  | _ => exact lift_free _ (old_backend_free setup checks _ before)

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact backend_free setup checks query state

private theorem prefix_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit query).run before).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free setup checks _ before
    | trivial

theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact prefix_free setup checks query state

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsService, isQueryBoundP_query_iff]

theorem local_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (env : Environment) :
    ((show StateT Environment (OracleComp (Spec n KemSK)) (RustM (Option RegistrationServerReferenceRoot.Ready)) from do
      let input ← collect setup checks packet authenticated
      match input with
      | none => pure (.ok none)
      | some input => StateT.lift (simulateQ prepare
        (RegistrationServerReferenceRoot.client authenticated.binding input))).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationServerReferenceRoot.client authenticated.binding input))

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

theorem agreement_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationServerReferenceRoot.client authenticated.binding input))

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.simulate_zero' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.simulate_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.collect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.local_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.local_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenServiceFree.agreement_free
