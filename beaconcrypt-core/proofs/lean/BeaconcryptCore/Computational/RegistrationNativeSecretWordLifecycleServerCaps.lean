-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! The actual authenticated Server prefix has one encapsulation position. This structural bill includes all native authentication, replay, reservation and primitive failures; ordinary World effects add no indexed encapsulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare)
open RegistrationNativeKemReferenceCompiler (backend collect visit)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsEncap : (Spec n KemSK).Domain → Prop
  | .inr (.inr (.inr (.inr _))) => True
  | _ => False
instance : DecidablePred (IsEncap (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsEncap
  split <;> infer_instance

def PrimitiveEncap : RegistrationAgreementExecutor.Spec.Domain → Prop
  | .encapsulate _ => True
  | _ => False
instance : DecidablePred PrimitiveEncap := fun query => by cases query <;> first | exact isTrue trivial | exact isFalse id

def PrefixEncap {Reader E : Type} : PqxdhServerRootPreparation.Query Reader E → Prop
  | .encapsulate _ => True
  | _ => False
instance {Reader E : Type} : DecidablePred (PrefixEncap (Reader := Reader) (E := E)) := fun query => by
  cases query <;> first | exact isTrue trivial | exact isFalse id

/-- The original collector has exactly one possible encapsulation query, after its preceding source gates. -/
theorem collector_one {Reader E Shared : Type} (verified : PqxdhServerRootPreparation.Verified Reader) :
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified).IsQueryBoundP PrefixEncap 1 := by
  unfold PqxdhServerRootPreparation.collectVerified
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (simp_all only [PrefixEncap, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
        OptionT.run_pure, Option.elimM, Option.elim_some,
        bind_map_left, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        not_false_eq_true, not_true_eq_false, true_or, false_or])
    | (rw [isQueryBoundP_query_bind_iff]; constructor)
    | (intro answer; cases answer)

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsEncap, isQueryBoundP_query_iff]

private theorem ordinary_free (work : OracleComp (RegistrationServerReferenceCompiler.Spec n) Value) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK)) work).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  rcases query with message | (message | query)
  all_goals simp [RegistrationNativeKemReferenceCompiler.lift, IsEncap, isQueryBoundP_query_iff]

private theorem backend_bound (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP (IsEncap (KemSK := KemSK))
      (if PrimitiveEncap query then 1 else 0) := by
  cases query with
  | encapsulate key =>
      simp only [backend, StateT.run, isQueryBoundP_map_iff]
      cases key with
      | none => trivial
      | some key =>
          simp only [RegistrationNativeKemInterface.server]
          split
          · simp [RegistrationNativeKemInterface.encapsulate, RegistrationBeaconReferenceCompiler.indexed,
              IsEncap, PrimitiveEncap, isQueryBoundP_query_iff]
          · trivial
  | _ => exact ordinary_free _

private theorem backend_program_bound (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP PrimitiveEncap cap) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query charged state
    simpa only [ite_eq_left charged] using backend_bound setup checks query state
  · intro query quiet state
    simpa only [ite_eq_right quiet] using backend_bound setup checks query state

private theorem callback_bound
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain) :
    (RegistrationAgreementRoot.callbacks query).IsQueryBoundP PrimitiveEncap
      (if PrefixEncap query then 1 else 0) := by
  cases query <;> simp [RegistrationAgreementRoot.callbacks, PrefixEncap, PrimitiveEncap,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem prefix_bound (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit query).run before).IsQueryBoundP
      (IsEncap (KemSK := KemSK)) (if PrefixEncap query then 1 else 0) := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_bound setup checks _ _ (callback_bound _) before
    | trivial

/-- The entire concrete indexed collector exposes at most its actual single encapsulation position. -/
theorem collect_bound (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) 1 := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  apply (collector_one (RegistrationRootInput.verified packet authenticated)).simulateQ_run_of_step
  · intro query charged state
    simpa only [ite_eq_left charged] using prefix_bound setup checks query state
  · intro query quiet state
    simpa only [ite_eq_right quiet] using prefix_bound setup checks query state

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsEncap, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Root preparation follows the sole indexed encapsulation, without adding another KEM getter. -/
theorem agreement_bound (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP
      (IsEncap (KemSK := KemSK)) 1 := by
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_bound setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationServerReferenceRoot.client authenticated.binding input))

private theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP
      (IsEncap (KemSK := KemSK)) 0 := by
  simp only [RegistrationServerOpenReferenceCompiler.retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before with
  | fail error => trivial
  | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

private theorem after_bound (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP
      (IsEncap (KemSK := KemSK)) 1 := by
  simp only [RegistrationServerOpenReferenceCompiler.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · simp only [StateT.run_bind]
      apply isQueryBoundP_bind (m := 0) (agreement_bound setup checks packet authenticated before env)
      intro result _reached
      cases result.1.1 with
      | fail error => trivial
      | div => trivial
      | ok accepted => cases accepted with
        | none => trivial
        | some ready => exact retain_free ready result.1.2 result.2
    · trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- The complete mandatory-authentication/replay/allocator Server accept invokes its indexed KEM getter at most once, on every failure or success path. -/
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((RegistrationServerOpenReferenceCompiler.accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP
      (IsEncap (KemSK := KemSK)) 1 := by
  simp only [RegistrationServerOpenReferenceCompiler.accept, StateT.run_bind, StateT.run_get,
    StateT.run_lift, pure_bind, bind_assoc]
  apply isQueryBoundP_bind (n := 0) (m := 1) (environment_free _)
  intro checked _
  cases checked with
  | fail error => trivial
  | div => trivial
  | ok result =>
      rcases result with ⟨events, reply⟩
      cases reply <;> first
        | exact after_bound setup checks packet _ before env
        | trivial

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.collector_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.collector_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.collect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.agreement_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps.accept_bound
