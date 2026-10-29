-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! Each actual native Server admission prepares at most one root address. Mandatory authentication, local collection, replay checks and failed paths cannot add preparations; later builds use the retained reference without preparing again. These source bills hold before any real or candidate provider is interpreted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerOpenReferenceCompiler
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl _ => True
  | _ => False

instance : DecidablePred (IsPrepare (n := n) (KemSK := KemSK)) := fun query => by
  cases query <;> simp only [IsPrepare] <;> infer_instance

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [effect, IsPrepare, isQueryBoundP_query_iff]

private theorem ordinary_backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK))
      ((RegistrationServerReferenceCompiler.backend (n := n) setup checks query).run before)).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  change (simulateQ RegistrationNativeKemReferenceCompiler.lift
    (simulateQ RegistrationServerReferenceCompiler.effect
      ((RegistrationWorldAgreementCompiler.compiler setup.source
        (RegistrationServerRoleBackend.localBackend setup checks) query).run before))).IsQueryBoundP
          (IsPrepare (KemSK := KemSK)) 0
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [QueryImpl.compose, RegistrationServerReferenceCompiler.effect, RegistrationNativeKemReferenceCompiler.lift,
    IsPrepare, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  cases query with
  | encapsulate key =>
      simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro query
      simp [RegistrationBeaconReferenceCompiler.indexed, IsPrepare, isQueryBoundP_query_iff]
  | _ => exact ordinary_backend_free setup checks _ before

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks) work).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible; contradiction
  · intro query _ current
    exact backend_free setup checks query current

private theorem prefix_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit query).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first | exact backend_program_free setup checks _ before | trivial

/-- Actual primitive and selected-KEM collection is before the sole root-preparation request and never emits one itself. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible; contradiction
  · intro query _ current
    exact prefix_free setup checks query current

private theorem prepare_bound (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) (RegistrationServerReferenceRoot.client binding input)).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 1 := by
  have bounded : (RegistrationServerReferenceRoot.client binding input).IsQueryBoundP (fun _ => True) 1 := by
    simpa only [IsQueryBoundP, IsTotalQueryBound, not_true_eq_false, false_or, ite_true] using
      RegistrationServerReferenceRoot.client_bound binding input
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ _ 1 bounded
  intro query
  simp [prepare, IsPrepare, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem agreement_bound (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (n := 0) (m := 1) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input =>
      simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
        prepare_bound (n := n) (KemSK := KemSK) authenticated.binding input

private theorem bind_bound {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y) (firstCount laterCount : Nat)
    (first : ∀ before env, ((work.run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) firstCount)
    (later : ∀ value before env, (((next value).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) laterCount)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((work >>= next).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) (firstCount + laterCount) := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (first before env)
  intro result _
  exact later result.1.1 result.1.2 result.2

private theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before <;> trivial

private theorem after_bound (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · apply bind_bound _ _ 1 0 (agreement_bound setup checks packet authenticated)
      intro value state current
      cases value with
      | fail error => trivial
      | div => trivial
      | ok value => cases value with
        | none => trivial
        | some ready => exact retain_free ready state current
    · trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Every actual native SDK admission emits at most one preparation, including authentication, replay, reservation and primitive failures. -/
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  unfold accept
  apply bind_bound _ _ 0 1
  · intro current env
    simp only [StateT.run_get, StateT.run_pure]
    trivial
  · intro current before env
    apply bind_bound _ _ 0 1
    · intro state env
      simpa only [StateT.run_lift, StateT.run_map, map_state_apply, bind_pure_comp, isQueryBoundP_map_iff] using
        environment_free (KemSK := KemSK) (RegistrationAuthenticationCompiler.program setup.source.crypto verify current.pin packet)
    · intro checked state env
      cases checked with
      | fail error | div => trivial
      | ok result =>
          rcases result with ⟨events, reply⟩
          cases reply <;> first | exact after_bound setup checks packet _ state env | trivial

private theorem common_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (env : Environment) :
    ((RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) source writer sign query).run env).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
        StateT.run, isQueryBoundP_map_iff]
      exact environment_free _
  | inr query =>
      simp [RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, effect, IsPrepare, isQueryBoundP_query_iff]

/-- A later build consumes the already retained reference and never prepares a new root address. -/
theorem build_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((build (n := n) (KemSK := KemSK) source wire checks sign handle application).run before).run env).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  change ((simulateQ (RegistrationNativeCommonCompiler.service effect demand source wire.frameWrite sign)
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before)).run env).IsQueryBoundP _ 0
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible; contradiction
  · intro query _ current
    cases query with
    | inl message =>
        simp [RegistrationNativeCommonCompiler.service, demand, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, IsPrepare, isQueryBoundP_query_iff]
    | inr query => exact common_free source wire.frameWrite sign query current

end BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.accept_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.build_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps.build_free
