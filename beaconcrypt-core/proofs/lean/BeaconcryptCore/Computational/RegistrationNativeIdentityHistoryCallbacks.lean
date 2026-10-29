-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape

/-! Actual incoming authentication, static DH and sequence-one record callbacks retain the indexed signing history. Local static DH still executes the ordinary service and records its optional response; it contributes no signed message. All native Env, cache and installation side effects remain in the execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend
open RegistrationNativeIdentityHistoryInvariant
open RegistrationNativeIdentitySourceSimulation (runNew liftAmbient)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem lift_old (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (OracleComp (Ambient n KemSK)) Value) :
    liftOld (source := source) (StateT.lift work) = liftAmbient work := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [liftOld, liftAmbient, StateT.run_lift, StateT.run_map, bind_pure_comp,
    Functor.map_map, id_map']

theorem readonly_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary) (OracleComp (Ambient n KemSK)) Value) :
    Preserves (source := source) setup checks representation created index handle (liftOld (StateT.lift work)) := by
  rw [lift_old]
  exact ambient_preserves setup checks representation created index handle _

theorem static_signed (pool : PqxdhDynamicIdentityPool.SourceState) (identity selected : Nat)
    (peer : PqxdhJointIdentity.PeerEncoding) (reply : Option PqxdhJointIdentity.DhOutput) :
    PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history identity
      (PqxdhDynamicIdentityPool.record (.inr (.service selected (.staticDh peer))) (some reply) pool).transcript) =
      PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history identity pool.transcript) := by
  by_cases same : selected = identity <;>
    simp [PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
      RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.requestEvent,
      PqxdhJointIdentity.signedMessages, List.filterMap_append, same]

private theorem run_double_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp (Trusted n KemSK) Value)
    (before : RegistrationNativeIdentitySourceSimulation.NewState n KemSK Auxiliary source) :
    runNew setup checks representation created (StateT.lift (StateT.lift work)) before =
      (fun result => (result.1, ((before.1.1, before.1.2), result.2))) <$>
        (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created) work).run before.2 := by
  simp only [runNew, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map, Functor.map_map]

theorem dh_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (peer : PqxdhBeaconPhase2Preparation.Word32) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index owner.identity.handle
      (StateT.lift (StateT.lift (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) owner.identity peer))) := by
  intro before result prior supported
  obtain ⟨current, found, same⟩ := at_owner index owner.identity.handle before.1.1 prior.2
  obtain ⟨seed, receipt⟩ := prior.1.1 current (List.mem_of_getElem? found)
  have seedAt : before.2.identities.seeds[owner.identity.handle]? = some seed := by
    rw [← same]
    exact receipt.1
  rw [run_double_lift, RegistrationNativeIdentityWorldServices.dh_source setup checks representation created
    owner.identity seed peer before.2 seedAt, map_pure, mem_support_pure_iff] at supported
  cases supported
  let after : RegistrationNativeIdentitySourceSimulation.NewState n KemSK Auxiliary source :=
    (before.1, { before.2 with
      identities := PqxdhDynamicIdentityPool.record
        (.inr (.service owner.identity.handle (.staticDh (PqxdhPhase2GapDhSource.peer peer))))
        (some (setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer))) before.2.identities })
  change Good setup.joint index owner.identity.handle after
  apply fields_preserve setup.joint index owner.identity.handle before after prior rfl rfl
  intro selected member
  rw [static_signed]
  exact prior.1.2.2 selected member

theorem authentication_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (query : RegistrationAuthenticationExecutor.Request) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle
      (authentication setup source query) := by
  cases query with
  | hash request =>
      exact bind_preserves setup checks representation created index handle _ _
        (RegistrationNativeIdentityHistoryOutgoing.effect_preserves setup checks representation created index handle _)
        (fun _ => pure_preserves setup checks representation created index handle _)
  | mldsa request | ed25519 request => exact pure_preserves setup checks representation created index handle _

theorem agreement_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (agreement setup owner oneTime query) := by
  by_cases ordinary : RegistrationNativeIdentityAgreementShape.Other query
  · rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary]
    let current := restore dummyIdentity owner
    have lifted := RegistrationBeaconReferenceNativeCallbacks.owned_query (n := n) (Auxiliary := Auxiliary) setup
      current.prekeyScalar (RegistrationBeaconReferenceCompiler.eraseOwner current) oneTime query
    rw [RegistrationBeaconReferenceCompiler.restore_erase current] at lifted
    rw [lifted]
    exact readonly_preserves setup checks representation created index owner.identity.handle _
  · cases query with
    | convertSecret role =>
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.update_preserves setup checks representation created index owner.identity.handle _)
          (fun _ => pure_preserves setup checks representation created index owner.identity.handle true)
    | dh request =>
        rcases request with ⟨role, peer⟩
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (RegistrationNativeIdentityHistoryOutgoing.update_preserves setup checks representation created index owner.identity.handle _)
          (fun _ => dh_preserves setup checks representation created index owner peer)
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request =>
        exact False.elim (ordinary trivial)

theorem record_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index handle : Nat)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle
      (record setup wire query) := by
  change Preserves setup checks representation created index handle
    (liftOld (RegistrationNativeBeaconFrontend.record setup wire query))
  rw [RegistrationBeaconReferenceNativeOwner.record_owned (mlSource := source)]
  exact readonly_preserves setup checks representation created index handle _

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.readonly_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.readonly_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.static_signed' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.static_signed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.dh_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.dh_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.authentication_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.authentication_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.agreement_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.agreement_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.record_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryCallbacks.record_preserves
