-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts
import BeaconcryptCore.Computational.RegistrationNativeWeightedContext
import BeaconcryptCore.Computational.RegistrationNativeAcceptSourceCosts

/-! Concrete source costs for actual native acceptance. Primitive coin costs remain inputs; the actual authenticated collector, including early failures and replay lookup, supplies the callback multiplicities. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeAcceptCosts
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_run weighted_simulate weighted_bind weighted_mono)
open RegistrationNativePrimitiveCosts (coinCost)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def ordinaryCount : RegistrationAgreementExecutor.Request → Nat
  | .generate _ => 32
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_coins (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (ordinary : RegistrationNativeKemReferenceCompiler.NonEncapsulation query)
    (before : RegistrationServerRoleBackend.State) :
    ((RegistrationAgreementShared.auxiliary setup.source (RegistrationServerRoleBackend.localBackend setup checks) query).run before).IsTotalQueryBound (ordinaryCount query) := by
  cases query with
  | convertPublic key => trivial
  | convertSecret role => cases role <;> trivial
  | generate role =>
      cases role
      simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend,
        StateT.run, ordinaryCount, IsTotalQueryBound, isQueryBound_map_iff, PqxdhServerAuthExperiment.generateEphemeral, bind_pure_comp]
      exact PqxdhJointGapDh.sampleScalar_uniform
  | encapsulate key => exact ordinary.elim
  | decapsulate ciphertext => trivial
  | dh request =>
      simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend, StateT.run]
      cases request.secret_role <;> trivial
  | root request => trivial

theorem effects_bound (qSign qKem : Nat) (kind : EffectKind)
    (work : OracleComp (EnvEffects n) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => effectKind query = kind) count) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (KemSK := KemSK) qSign qKem query kind)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work) count := by
  apply weighted_simulate (fun query => if effectKind query = kind then 1 else 0)
  · simpa only [Nat.one_mul] using weighted_indicator (fun query => effectKind query = kind) 1 work count bounded
  · intro query
    simpa only [RegistrationBeaconReferenceCompiler.effect, RegistrationNativeReferenceCosts.bill] using
      RegistrationNativeWeightedContext.query_bound
        (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
        (.inr (.inl (.inr (.inr query))))

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_backend (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind) (query : RegistrationAgreementExecutor.Request)
    (ordinary : RegistrationNativeKemReferenceCompiler.NonEncapsulation query)
    (before : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativeKemReferenceCompiler.ordinary (KemSK := KemSK) (RegistrationServerReferenceCompiler.backend (n := n) setup checks query)).run before)
      (coinCost (ordinaryCount query) kind) := by
  simp only [RegistrationNativeKemReferenceCompiler.ordinary, RegistrationServerReferenceCompiler.backend,
    RegistrationServerReferenceCompiler.liftEnvironment, RegistrationWorldAgreementCompiler.compiler,
    StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose]
  have inclusion : RegistrationNativeKemReferenceCompiler.lift (n := n) (KemSK := KemSK) ∘ₛ RegistrationServerReferenceCompiler.effect =
      RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK) := rfl
  rw [inclusion]
  apply RegistrationNativeWeightedContext.map_bound
  apply effects_bound
  have coins := RegistrationWorldCoinCompiler.env_bound (n := n)
    ((RegistrationAgreementShared.auxiliary setup.source (RegistrationServerRoleBackend.localBackend setup checks) query).run before.auxiliary)
    (ordinaryCount query) (ordinary_coins setup checks query ordinary before.auxiliary) kind
  cases kind <;> simpa only [StateT.run, coinCost, reduceCtorEq, ite_true, ite_false] using coins

def agreementCost (qKem : Nat) : RegistrationAgreementExecutor.Request → EffectKind → Nat
  | .encapsulate _, kind => coinCost qKem kind
  | query, kind => coinCost (ordinaryCount query) kind

set_option backward.isDefEq.respectTransparency false in
theorem backend_bound (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind) (query : RegistrationAgreementExecutor.Request)
    (before : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativeKemReferenceCompiler.backend setup checks query).run before)
      (agreementCost qKem query kind) := by
  cases query with
  | encapsulate key =>
      cases key with
      | none => trivial
      | some key =>
          simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run,
            RegistrationNativeKemInterface.server]
          split
          · simp only [RegistrationNativeKemInterface.encapsulate, simulateQ_map, simulateQ_spec_query]
            simp only [Functor.map_map, RegistrationBeaconReferenceCompiler.indexed]
            apply RegistrationNativeWeightedContext.map_bound
            exact RegistrationNativeWeightedContext.query_bound _ _
          · trivial
  | convertPublic key => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before
  | convertSecret role => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before
  | generate role => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before
  | decapsulate ciphertext => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before
  | dh request => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before
  | root request => exact ordinary_backend setup checks qSign qKem kind _ (by trivial) before

set_option backward.isDefEq.respectTransparency false in
theorem prefix_bound (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend setup checks))
        RegistrationNativeKemReferenceCompiler.visit query).run before)
      (RegistrationNativeAcceptSourceCosts.bill qKem query kind) := by
  cases query <;>
    simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl,
      RegistrationAgreementRoot.callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  all_goals first
    | trivial
    | (apply RegistrationNativeWeightedContext.map_bound; exact backend_bound setup checks qSign qKem kind _ before)

theorem collect_bound (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated).run before)
      (coinCost (32 + qKem) kind) :=
  weighted_run _ _ _ _ _ _
    (RegistrationNativeAcceptSourceCosts.collector_bound (RegistrationRootInput.verified packet authenticated) qKem kind)
    (fun query state => prefix_bound setup checks qSign qKem kind query state)

theorem prepare_bound (qSign qKem : Nat) (kind : EffectKind)
    (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (simulateQ RegistrationBeaconReferenceCompiler.prepare work) 0 := by
  apply weighted_simulate (fun _ => 0)
  · simpa only [ite_false, Nat.zero_mul] using
      weighted_indicator (fun _ => False) 0 work 0 (isQueryBoundP_false work 0)
  · intro message
    exact RegistrationNativeWeightedContext.query_bound _ _

set_option backward.isDefEq.respectTransparency false in
theorem agreement_bound (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env)
      (coinCost (32 + qKem) kind) := by
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply weighted_bind _ _ _ (coinCost (32 + qKem) kind) 0 (collect_bound setup checks qSign qKem kind packet authenticated env)
  rintro ⟨_ | input, reached⟩
  · trivial
  · simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]
    apply RegistrationNativeWeightedContext.map_bound
    exact prepare_bound qSign qKem kind _

set_option backward.isDefEq.respectTransparency false in
theorem after_authentication_bound (setup : Setup base KemSK) (checks : Checks)
    (qSign qKem : Nat) (kind : EffectKind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated).run before).run env)
      (coinCost (32 + qKem) kind) := by
  simp only [RegistrationServerOpenReferenceCompiler.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · simp only [StateT.run_bind]
      apply weighted_bind _ _ _ (coinCost (32 + qKem) kind) 0 (agreement_bound setup checks qSign qKem kind packet authenticated before env)
      rintro ⟨⟨reply, after⟩, reached⟩
      cases reply with
      | fail error => trivial
      | div => trivial
      | ok ready =>
          cases ready with
          | none => trivial
          | some ready =>
              simp only [RegistrationServerOpenReferenceCompiler.retain, StateT.run]
              cases RegistrationServerMaterialFrontend.retain ready after <;> trivial
    · trivial

def bill (qKem : Nat) : EffectKind → Nat
  | .coin => 32 + qKem
  | .hash => 8
  | .administrative => 0

attribute [local irreducible] RegistrationAuthenticationCompiler.program RegistrationServerOpenReferenceCompiler.afterAuthentication

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (qSign qKem : Nat) (kind : EffectKind) (packet : registration.InitPacket)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationServerOpenReferenceCompiler.accept setup checks verify packet).run before).run env)
      (bill qKem kind) := by
  simp only [RegistrationServerOpenReferenceCompiler.accept, StateT.run_bind, StateT.run_get,
    StateT.run_lift, bind_pure_comp, bind_map_left, pure_bind]
  apply weighted_mono _ _ ((if kind = .hash then 8 else 0) + coinCost (32 + qKem) kind) _
  · apply weighted_bind _ _ _ (if kind = .hash then 8 else 0) (coinCost (32 + qKem) kind)
    · exact effects_bound qSign qKem kind _ _
        ((RegistrationAuthenticationBounds.program_bound setup.source.crypto verify before.pin packet kind).mono (by cases kind <;> simp))
    · intro reply
      cases reply with
      | fail error => trivial
      | div => trivial
      | ok checked =>
          rcases checked with ⟨events, state⟩
          cases state <;> first
            | trivial
            | exact after_authentication_bound setup checks qSign qKem kind packet _ before env
  · cases kind <;> simp [bill, coinCost]

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
theorem frontend_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept qSign qKem : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : RegistrationNativePublicFrontend.State source) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.accept packet))).run before) (bill qKem kind) := by
  simp only [RegistrationNativePublicFrontend.handler, StateT.run]
  apply RegistrationNativeWeightedContext.map_bound
  apply RegistrationNativeReferenceCosts.lifted_program
  exact accept_bound setup checks source.verify qSign qKem kind packet before.server before.environment

end BeaconcryptCore.Computational.RegistrationNativeAcceptCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.ordinary_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.ordinary_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.effects_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.effects_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.ordinary_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.ordinary_backend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.backend_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.prefix_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.collect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.prepare_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.after_authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.after_authentication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.accept_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptCosts.frontend_bound
