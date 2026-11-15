-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenCreate
import BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners
import BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemRoster

/-! Completed candidate-provider executions derive the relation between retained local owners and the genuine reserved KEM prefix. Successful owner creation, private KEM handles and World owner handles remain separate API fields; their local-owner/private-birth equality is proved from the actual constructor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemOpenFrame (NoPut lower)
open RegistrationNativeKemBirthInvariant (metadata)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Holds (pairs : List (MlKem768PublicKey × KemSK)) (state : State n mlSource KemSK) : Prop :=
  borns state = state.1.1.beacons.length ∧
    ∀ (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource), state.1.1.beacons[index]? = some owner →
      ∃ pair, pairs[index]? = some pair ∧ owner.kemHandle = index ∧ owner.kemPublic = pair.1

private theorem same_holds (pairs : List (MlKem768PublicKey × KemSK)) (before after : State n mlSource KemSK)
    (prior : Holds pairs before) (counted : borns after = borns before)
    (preserved : after.1.1.beacons.map metadata = before.1.1.beacons.map metadata) : Holds pairs after := by
  have sizes : after.1.1.beacons.length = before.1.1.beacons.length := by simpa only [List.length_map] using congrArg List.length preserved
  refine ⟨counted.trans (prior.1.trans sizes.symm), ?_⟩
  intro index owner found
  have backwards : RegistrationNativeKemRoster.Prefix after.1.1.beacons before.1.1.beacons :=
    ⟨[], by rw [preserved]; simp⟩
  obtain ⟨earlier, earlierAt, same⟩ := RegistrationNativeKemRoster.lookup _ _ backwards index owner found
  obtain ⟨pair, pairAt, handle, key⟩ := prior.2 index earlier earlierAt
  exact ⟨pair, pairAt, (congrArg Prod.fst same).symm.trans handle, (congrArg Prod.snd same).symm.trans key⟩

private theorem create_holds (pairs : List (MlKem768PublicKey × KemSK)) (before after : State n mlSource KemSK)
    (prior : Holds pairs before) (transition : RegistrationNativeKemOpenCreate.Transition pairs before after) : Holds pairs after := by
  rcases transition with ⟨counted, same⟩ | ⟨pair, owner, pairAt, handle, key, counted, appended⟩
  · exact same_holds pairs before after prior counted (congrArg (List.map metadata) same)
  · refine ⟨by rw [counted, appended, List.length_append, List.length_singleton, prior.1], ?_⟩
    intro index current found
    by_cases earlier : index < before.1.1.beacons.length
    · rw [appended, List.getElem?_append_left earlier] at found
      exact prior.2 index current found
    · have within := (List.getElem?_eq_some_iff.mp found).1
      rw [appended, List.length_append, List.length_singleton] at within
      have exactIndex : index = before.1.1.beacons.length := by omega
      subst index
      rw [appended, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at found
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst current
      exact ⟨pair, prior.1 ▸ pairAt, handle.trans prior.1, key⟩

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every actual completed typed native controller preserves the derived owner-to-genuine-prefix relation under arbitrary candidate replies. -/
theorem dispatcher_holds (chosen : Bool) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State n mlSource KemSK) (prior : Holds pairs before) (value : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemRouting.route chosen)
        (RegistrationNativeKemDispatcherCompiler.handler setup wire checks query))).run).run before)) : Holds pairs after := by
  let compiled := simulateQ (RegistrationNativeKemRouting.route chosen)
    (RegistrationNativeKemDispatcherCompiler.handler (n := n) (mlSource := mlSource) setup wire checks query)
  have ordinary (noPut : compiled.AllQueriesSatisfy NoPut)
      (noBirth : compiled.IsQueryBoundP RegistrationNativeKemOpenBirthFrame.IsCreate 0) : Holds pairs after := by
    have owners := RegistrationNativeKemOpenOwnersFrame.no_put_keeps setup checks wire route representation created credential
      selected pairs publicKey real compiled noPut before after value supported
    have counted := RegistrationNativeKemOpenBirthFrame.no_create_keeps setup checks wire route representation created credential
      selected pairs publicKey real compiled noBirth before after value supported
    exact same_holds pairs before after prior counted (congrArg (List.map metadata) owners)
  cases query with
  | inl coin =>
      exact ordinary ((allQueriesSatisfy_query_iff _ _).mpr trivial)
        ((isQueryBoundP_query_iff _ _ 0).mpr (by intro impossible; cases impossible))
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          apply create_holds pairs before after prior
          apply RegistrationNativeKemOpenCreate.create_transition setup checks wire route representation created credential
            selected pairs publicKey real chosen edPin mlPin keyId before after value
          simpa only [RegistrationNativeKemDispatcherCompiler.handler, lower, QueryImpl.simulateQ_compose] using supported
      | bundle index =>
          have compiledSupport : (some value, after) ∈ support
              (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
                (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)))).run).run before) := by
            simpa only [RegistrationNativeKemDispatcherCompiler.handler, lower, QueryImpl.simulateQ_compose] using supported
          exact same_holds pairs before after prior
            (RegistrationNativeKemOpenBirthCompiler.beacon_keeps setup checks wire route representation created credential
              selected pairs publicKey real chosen _ (RegistrationNativeKemBeaconFootprint.bundle_zero setup .create wire index)
              before after value compiledSupport)
            (RegistrationNativeKemOpenBeaconResult.bundle_metadata setup checks wire route representation created credential
              selected pairs publicKey real chosen index before after value compiledSupport)
      | finish index packet =>
          have compiledSupport : (some value, after) ∈ support
              (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
                (RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet)))).run).run before) := by
            simpa only [RegistrationNativeKemDispatcherCompiler.handler, lower, QueryImpl.simulateQ_compose] using supported
          exact same_holds pairs before after prior
            (RegistrationNativeKemOpenBirthCompiler.beacon_keeps setup checks wire route representation created credential
              selected pairs publicKey real chosen _ (RegistrationNativeKemBeaconFootprint.finish_zero setup .create wire index packet)
              before after value compiledSupport)
            (RegistrationNativeKemOpenBeaconResult.finish_metadata setup checks wire route representation created credential
              selected pairs publicKey real chosen index packet before after value compiledSupport)
      | accept packet =>
          have compiledSupport : (some value, after) ∈ support
              (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run before) := by
            simpa only [RegistrationNativeKemDispatcherCompiler.handler, lower, QueryImpl.simulateQ_compose] using supported
          exact same_holds pairs before after prior
            (RegistrationNativeKemOpenBirthFrame.no_create_keeps setup checks wire route representation created credential
              selected pairs publicKey real _ (RegistrationNativeKemOpenBirthCompiler.lower_bound chosen _ 0
                (RegistrationNativeKemServerFootprint.typed_zero setup checks .create packet)) before after value compiledSupport)
            (congrArg (List.map metadata) (RegistrationNativeKemOpenSdkOwners.typed_owners setup checks wire route representation created credential
              selected pairs publicKey real chosen packet before after value compiledSupport))
      | hmac key message => exact ordinary (allQueriesSatisfy_pure _ _) (isQueryBoundP_pure _ _ _)
      | _ =>
          exact ordinary ((allQueriesSatisfy_query_iff _ _).mpr trivial)
            ((isQueryBoundP_query_iff _ _ 0).mpr (by intro impossible; cases impossible))

/-- Reading the actual parsed selector before native dispatch preserves the same derived roster invariant. -/
theorem parsed_holds (parsed : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State n mlSource KemSK) (prior : Holds pairs before) (value : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed query)).run).run before)) : Holds pairs after := by
  let call := query
  cases query with
  | inl coin => exact dispatcher_holds setup checks wire route representation created credential selected pairs publicKey real false call before after prior value supported
  | inr command =>
      cases command with
      | accept packet =>
          simp only [RegistrationNativeKemParsedRouting.handler, RegistrationNativeKemParsedRouting.get,
            simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
          rw [RegistrationNativeKemOpenProvider.get_run] at supported
          simp only [pure_bind, Option.elim_some] at supported
          exact dispatcher_holds setup checks wire route representation created credential selected pairs publicKey real
            _ call _ after prior value supported
      | _ => exact dispatcher_holds setup checks wire route representation created credential selected pairs publicKey real false call before after prior value supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster.dispatcher_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster.dispatcher_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster.parsed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster.parsed_holds
