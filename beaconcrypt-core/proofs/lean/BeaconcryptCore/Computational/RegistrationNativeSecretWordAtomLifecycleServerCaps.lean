-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore

/-! The actual opaque-word Server controller has one indexed encapsulation position. Authentication, replay, reservation and ordinary primitive failures add no encapsulation, and preparation follows that same getter without duplicating its word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare localKem)
open RegistrationNativeSecretWordServerCompiler (backend ordinaryPrefix prefixImpl collect agreement retain afterAuthentication accept)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsEncap : (LocalSpec n KemSK).Domain → Prop
  | .inr (.inr (.inr (.inr _))) => True
  | _ => False
instance : DecidablePred (IsEncap (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsEncap
  split <;> infer_instance

def PrefixEncap {Reader E : Type} : PqxdhServerRootPreparation.Query Reader E → Prop
  | .encapsulate _ => True
  | _ => False
instance {Reader E : Type} : DecidablePred (PrefixEncap (Reader := Reader) (E := E)) := fun query => by
  cases query <;> first | exact isTrue trivial | exact isFalse id

/-- The actual symbolic collector has one encapsulation point on all its reply branches. -/
theorem collector_one {Reader E Shared : Type} (verified : PqxdhServerRootPreparation.Verified Reader) :
    (RegistrationNativeSecretWordServerCollect.collect (E := E) (Shared := Shared) verified).IsQueryBoundP PrefixEncap 1 := by
  unfold RegistrationNativeSecretWordServerCollect.collect
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

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 :=
  environment_free _

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible state
    exact impossible.elim
  · intro query _quiet state
    exact backend_free setup checks query state

private theorem ordinary_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((ordinaryPrefix (n := n) setup checks query).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  cases query <;> simp only [ordinaryPrefix, PqxdhServerStaticDhSource.prefixImpl,
    RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free setup checks _ before
    | trivial

private theorem prefix_bound (setup : Setup base KemSK) (checks : Checks)
    (query : (RegistrationNativeSecretWordServerCollect.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((prefixImpl (n := n) setup checks query).run before).IsQueryBoundP (IsEncap (KemSK := KemSK))
      (if PrefixEncap query then 1 else 0) := by
  cases query <;> simp only [prefixImpl, PrefixEncap, ite_true, ite_false]
  all_goals first
    | exact ordinary_free setup checks _ before
    | (simp only [StateT.run]; split
       · simp [localKem, IsEncap, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
       · trivial)

/-- The concrete current-environment collector retains the sole indexed getter through every optional failure. -/
theorem collect_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsEncap (KemSK := KemSK)) 1 := by
  unfold RegistrationNativeSecretWordServerCompiler.collect
  apply (collector_one (RegistrationRootInput.verified packet authenticated)).simulateQ_run_of_step
  · intro query charged state
    simpa only [ite_eq_left charged] using prefix_bound setup checks query state
  · intro query quiet state
    simpa only [ite_eq_right quiet] using prefix_bound setup checks query state

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
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

private theorem agreement_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsEncap (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_bound setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some collected => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected))

private theorem retain_free (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (IsEncap (KemSK := KemSK)) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before with
  | fail error | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

private theorem after_bound (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsEncap (KemSK := KemSK)) 1 := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · simp only [StateT.run_bind]
      apply isQueryBoundP_bind (m := 0) (agreement_bound setup checks packet authenticated before env)
      intro result _reached
      cases result.1.1 with
      | fail error | div => trivial
      | ok reply => cases reply with
        | none => trivial
        | some ready => exact retain_free ready result.1.2 result.2
    · trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Mandatory native authentication, replay and preparation retain at most one actual indexed encapsulation on every accepted or rejected path. -/
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsEncap (KemSK := KemSK)) 1 := by
  rw [RegistrationNativeSecretWordTargetServerReceipt.accept_program_source]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 1) (environment_free _)
  intro checked _
  cases checked with
  | fail error | div => trivial
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict <;> first
        | exact after_bound setup checks packet _ before env
        | trivial

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.collector_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.collector_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.collect_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps.accept_bound
