-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! Actual Server authentication and agreement allocate no Beacon owner. Their only environment effects are native hash/coin callbacks; the selected encapsulation remains in the external indexed service. These are structural facts about every continuation, before any provider or World service is interpreted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenAllocationProtocol (effectDelta capabilityDelta)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationServerOpenReferenceCompiler
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def EffectAllowed (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) : Prop := effectDelta query = 0
def LocalAllowed : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain → Prop
  | .inr (.inl (.inr (.inr effect))) => EffectAllowed effect
  | _ => True

local notation "LocalSafe" => LocalAllowed (n := n) (KemSK := KemSK)

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem run_safe {Index State : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK))))
    (step : ∀ query before, AllQueriesSatisfy ((impl query).run before) LocalSafe)
    (work : OracleComp spec Value) (before : State) :
    AllQueriesSatisfy ((simulateQ impl work).run before) LocalSafe := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (step query before) (fun result => ih result.1 result.2)

private theorem effect_safe (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work) LocalSafe := by
  apply simulation _ EffectAllowed LocalSafe _ work safe
  intro query allowed
  exact (allQueriesSatisfy_query_iff _ _).mpr allowed

private theorem coins_safe (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ (RegistrationWorldCoinCompiler.envCoin (n := n)) work) EffectAllowed := by
  apply simulation _ (fun _ => True) EffectAllowed _ work (every work)
  intro query _
  simp [RegistrationWorldCoinCompiler.envCoin,
    EffectAllowed, effectDelta, allQueriesSatisfy_query_iff]

private theorem ordinary_backend_safe (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    AllQueriesSatisfy (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK))
      ((RegistrationServerReferenceCompiler.backend (n := n) setup checks query).run before)) LocalSafe := by
  simp only [RegistrationServerReferenceCompiler.backend, RegistrationServerReferenceCompiler.liftEnvironment,
    RegistrationWorldAgreementCompiler.compiler, StateT.run, simulateQ_map]
  apply mapped
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply simulation _ (fun _ => True) LocalSafe _ _ (every _)
  intro query _
  simp [QueryImpl.compose, RegistrationWorldCoinCompiler.envCoin,
    RegistrationServerReferenceCompiler.effect, RegistrationNativeKemReferenceCompiler.lift,
    LocalAllowed, EffectAllowed, effectDelta, allQueriesSatisfy_query_iff]

private theorem backend_safe (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    AllQueriesSatisfy ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query).run before) LocalSafe := by
  cases query with
  | encapsulate key =>
      simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run]
      apply mapped
      apply simulation _ (fun _ => True) LocalSafe _ _ (every _)
      intro query _
      simp [RegistrationBeaconReferenceCompiler.indexed, LocalAllowed, allQueriesSatisfy_query_iff]
  | _ => exact ordinary_backend_safe setup checks _ before

private theorem prefix_safe (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    AllQueriesSatisfy ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit query).run before) LocalSafe := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact run_safe _ (backend_safe setup checks) _ before
    | trivial

/-- The actual selected-KEM/root collector emits no Beacon allocation on any failure or success branch. -/
theorem collect_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    AllQueriesSatisfy ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before)
      (LocalAllowed (KemSK := KemSK)) := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  exact run_safe _ (prefix_safe setup checks) _ before

private theorem root_safe (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK)) work) LocalSafe := by
  exact simulation _ (fun _ => True) LocalAllowed (fun query _ => by
    simp [RegistrationBeaconReferenceCompiler.prepare, LocalAllowed, allQueriesSatisfy_query_iff]) work (every work)

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem agreement_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((agreement (n := n) setup checks packet authenticated).run before).run env) LocalSafe := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply allQueriesSatisfy_bind (collect_safe setup checks packet authenticated env)
  intro result
  cases result.1 with
  | none => trivial
  | some input =>
      simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, Functor.map_map] using
        mapped _ _ LocalAllowed (root_safe (n := n) (KemSK := KemSK)
          (RegistrationServerReferenceRoot.client authenticated.binding input))

private theorem bind_safe {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y)
    (first : ∀ before env, AllQueriesSatisfy ((work.run before).run env) LocalSafe)
    (later : ∀ value before env, AllQueriesSatisfy (((next value).run before).run env) LocalSafe)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((work >>= next).run before).run env) LocalSafe := by
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before env) (fun result => later result.1.1 result.1.2 result.2)

private theorem retain_safe (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((retain (n := n) (KemSK := KemSK) ready).run before).run env) LocalSafe := by
  simp only [retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before <;> trivial

private theorem after_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env) LocalSafe := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · apply bind_safe _ _ (agreement_safe setup checks packet authenticated)
      intro value current state
      cases value with
      | fail error => trivial
      | div => trivial
      | ok value => cases value with
        | none => trivial
        | some ready => exact retain_safe ready current state
    · trivial

attribute [local irreducible] RegistrationAuthenticationExecutor.begin

/-- Every actual incoming verifier callback is a native hash or pure verification; none allocates a Beacon owner. -/
theorem authentication_safe (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    AllQueriesSatisfy (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet) EffectAllowed := by
  unfold RegistrationAuthenticationCompiler.program
  apply simulation _ (fun _ => True) EffectAllowed _ _ (every _)
  intro query _
  cases query with
  | hash request =>
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)
  | mldsa request => trivial
  | ed25519 request => trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- The whole actual SDK accept, including mandatory authentication, replay and reservation failures, is allocation-free. -/
theorem accept_safe (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((accept (n := n) setup checks verify packet).run before).run env) (LocalAllowed (KemSK := KemSK)) := by
  simp only [accept, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]
  apply allQueriesSatisfy_bind (effect_safe _ (authentication_safe setup.source.crypto verify before.pin packet))
  intro checked
  cases checked with
  | fail error => trivial
  | div => trivial
  | ok result =>
      rcases result with ⟨events, reply⟩
      cases reply <;> first
        | exact after_safe setup checks packet _ before env
        | trivial

/-- Routing and the outer native Server state preserve this structural allocation footprint. -/
theorem server_safe {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : RegistrationNativePublicFrontend.State source)
    (safe : AllQueriesSatisfy ((work.run before.server).run before.environment) LocalSafe) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.serverOpen selected work).run before)
      RegistrationNativeHiddenAllocationCore.Allowed := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run]
  apply mapped
  apply simulation _ LocalSafe RegistrationNativeHiddenAllocationCore.Allowed _ _ safe
  intro query allowed
  rcases query with message | (query | query)
  · simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeHiddenAllocationCore.Allowed, allQueriesSatisfy_query_iff]
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    rcases query with message | (publication | effect)
    · trivial
    · trivial
    · exact allowed
  · apply simulation _ (fun _ => True) RegistrationNativeHiddenAllocationCore.Allowed _ _ (every _)
    intro routed _
    simp [RegistrationNativePublicFrontend.liftRoutedKem, RegistrationNativeHiddenAllocationCore.Allowed,
      allQueriesSatisfy_query_iff]

/-- Actual selected or ordinary SDK admission remains allocation-free in the complete public frontend. -/
theorem accept_frontend_safe {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK)
    (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (selected : Bool)
    (packet : registration.InitPacket) (before : RegistrationNativePublicFrontend.State source) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.serverOpen selected
      (accept (n := n) setup checks verify packet)).run before) RegistrationNativeHiddenAllocationCore.Allowed :=
  server_safe selected _ before (accept_safe setup checks verify packet before.server before.environment)

end BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.collect_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.collect_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.authentication_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.authentication_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.accept_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.accept_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.server_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.server_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.accept_frontend_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps.accept_frontend_safe
