-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame

/-! Actual candidate-source callbacks retain the complete native owner roster except for its explicit local-state put. This operational frame keeps identity credentials, signing histories, World owner handles, lifecycle phases and KEM birth metadata together. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenFrame (NoPut lower)
open RegistrationNativeOptionalFrame (Keeps)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def owners (before : State n mlSource KemSK) : RegistrationNativeBeaconFrontend.State mlSource := before.1.1.beacons

private def ambientOwners (query : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Domain)
    (before : RegistrationNativeKemServerState.State n mlSource) : RegistrationNativeBeaconFrontend.State mlSource :=
  match query with
  | .inl (.inl (.put after)) => after.beacons
  | _ => before.beacons

attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.retain
  RegistrationServerSdkSource.build CborRecordWorldSimulation.guarded

private theorem other_owners (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Domain)
    (before after : RegistrationNativeKemServerState.State n mlSource)
    (reply : (RegistrationNativeKemParsedRouting.Ambient n mlSource).Range query)
    (supported : (reply, after) ∈ support
      ((RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential query).run before)) :
    after.beacons = ambientOwners query before := by
  rcases query with (request | ordinary) | publicKey
  · cases request <;> simp only [RegistrationNativeKemParsedRouting.other,
      RegistrationNativeKemRouting.publicAmbient, RegistrationNativeKemFrontendInterface.other,
      RegistrationNativeKemServerInterface.other, RegistrationNativeKemServerInterface.server,
      StateT.run, support_map, mem_support_pure_iff] at supported
    all_goals first
      | (cases supported; rfl)
      | (obtain ⟨result, _reached, returned⟩ := supported; cases returned; rfl)
  · cases ordinary with
    | build session application =>
        simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
          RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.server,
          StateT.run, support_map] at supported
        obtain ⟨result, _reached, returned⟩ := supported
        cases returned
        rfl
    | record query =>
        simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
          RegistrationNativeKemFrontendInterface.other] at supported
        rcases query with query | ⟨owner, query⟩
        · simp only [RegistrationNativeKemFrontendInterface.record, RegistrationNativeKemFrontendInterface.world,
            StateT.run, support_map] at supported
          obtain ⟨result, _reached, returned⟩ := supported
          cases returned
          rfl
        · cases query <;> cases found : before.beacons[owner]? <;>
            simp only [RegistrationNativeKemFrontendInterface.record, found,
              RegistrationNativeKemFrontendInterface.world, StateT.run, support_map,
              mem_support_pure_iff] at supported
          all_goals first
            | (cases supported; rfl)
            | (obtain ⟨result, _reached, returned⟩ := supported; cases returned; rfl)
  · simp only [RegistrationNativeKemParsedRouting.other, RegistrationNativeKemRouting.publicAmbient,
      StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨result, _reached, returned⟩ := supported
    cases returned
    rfl

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every actual non-put source callback preserves the complete original native owner roster. -/
theorem query_owners (query : (Spec n mlSource KemSK).Domain) (ordinary : NoPut query)
    (before after : State n mlSource KemSK) (reply : (Spec n mlSource KemSK).Range query)
    (supported : (some reply, after) ∈ support (((provider query).run).run before)) : owners after = owners before := by
  rcases query with other | (pool | key)
  · rw [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchFacts.ambient_run, support_map] at supported
    obtain ⟨⟨value, reached⟩, called, returned⟩ := supported
    have stateEq := congrArg Prod.snd returned
    cases stateEq
    have same := other_owners setup checks wire route representation created credential other before.1.1 reached value called
    rcases other with (request | ordinaryQuery) | publicKey
    · cases request <;> try exact same
      cases ordinary
    · exact same
    · exact same
  · cases phase : before.2 <;> simp only [RegistrationNativeKemOpenProvider.implementation,
      RegistrationNativeKemSwitchSource.source, phase, RegistrationNativeKemSwitchSource.post,
      RegistrationNativeKemSwitchSource.carry, RegistrationNativeKemGame.stopped,
      RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
      OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
    all_goals obtain ⟨result, _called, returned⟩ := supported; cases congrArg Prod.snd returned; rfl
  · cases phase : before.2 with
    | some label =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          RegistrationNativeKemSwitchSource.post, RegistrationNativeKemSwitchSource.carry,
          RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
          OptionT.run_mk, StateT.run, Functor.map_map, support_map] at supported
        obtain ⟨result, _called, returned⟩ := supported
        cases congrArg Prod.snd returned
        rfl
    | none =>
        simp only [RegistrationNativeKemOpenProvider.implementation, RegistrationNativeKemSwitchSource.source, phase,
          OptionT.run_mk, StateT.run, mem_support_bind_iff] at supported
        obtain ⟨pair, _generated, uniform, _sampled, called⟩ := supported
        by_cases matching : key = publicKey
        · simp only [matching, ite_true, pure_bind, mem_support_pure_iff, Prod.mk.injEq] at called
          obtain ⟨_replyEq, stateEq⟩ := called
          rw [stateEq]
          rfl
        · simp only [matching, ite_false, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at called
          obtain ⟨value, _encapsulated, _replyEq, stateEq⟩ := called
          rw [stateEq]
          rfl

/-- Arbitrary actual native work without a local-state put retains every owner field, independently of candidate replies. -/
theorem no_put_keeps (work : OracleComp (Spec n mlSource KemSK) Value) (allowed : work.AllQueriesSatisfy NoPut) :
    Keeps owners provider work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact RegistrationNativeOptionalFrame.pure_keeps owners provider value
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      apply RegistrationNativeOptionalFrame.bind_keeps owners provider _ _ _ (fun reply => ih reply (allowed.2 reply))
      intro before after value supported
      rw [simulateQ_spec_query] at supported
      exact query_owners setup checks wire route representation created credential selected pairs publicKey real query allowed.1 before after value supported

/-- The literal native modifier installs exactly the owner roster of its explicit reached-state transformation. -/
theorem modify_owners (chosen : Bool)
    (change : RegistrationNativeKemServerState.State n mlSource → RegistrationNativeKemServerState.State n mlSource)
    (before after : State n mlSource KemSK) (value : Unit)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.modify change))).run).run before)) :
    owners after = (change (RegistrationNativeKemServerState.mask before.1.1)).beacons := by
  simp only [RegistrationNativeKemServerInterface.modify, RegistrationNativeKemServerInterface.get,
    RegistrationNativeKemServerInterface.put, simulateQ_bind, simulateQ_spec_query, lower,
    QueryImpl.apply_compose, RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
    OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
  rw [RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  rw [RegistrationNativeKemOpenProvider.put_run] at supported
  simp only [mem_support_pure_iff, Prod.mk.injEq] at supported
  rw [supported.2]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.query_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.query_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.no_put_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.no_put_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.modify_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame.modify_owners
