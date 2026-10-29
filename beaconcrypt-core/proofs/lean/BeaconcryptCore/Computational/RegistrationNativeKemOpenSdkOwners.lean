-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenOwnersFrame

/-! Actual open SDK authentication, agreement and retention preserve the complete owner roster for arbitrary real or candidate KEM replies. Parsed counters and Server state retain their literal operational updates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenProvider (State implementation)
open RegistrationNativeKemOpenOwnersFrame (owners)
open RegistrationNativeKemOpenFrame (NoPut lower)
open RegistrationNativeOptionalFrame (Keeps pure_keeps bind_keeps simulate_keeps)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem query_allowed (query : (Spec n mlSource KemSK).Domain) (allowed : NoPut query) :
    AllQueriesSatisfy ((Spec n mlSource KemSK).query query : OracleComp (Spec n mlSource KemSK) _) NoPut :=
  (allQueriesSatisfy_query_iff query NoPut).mpr allowed

private theorem map_allowed {Result : Type} (function : Value → Result) (work : OracleComp (Spec n mlSource KemSK) Value)
    (allowed : work.AllQueriesSatisfy NoPut) : (function <$> work).AllQueriesSatisfy NoPut :=
  (isQueryBound_map_iff work function () _ _).mpr allowed

private theorem primitive_allowed (checks : Checks) (chosen : Bool)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.primitive (n := n) (mlSource := mlSource) (KemSK := KemSK) checks query)).AllQueriesSatisfy NoPut := by
  cases query with
  | encapsulate key =>
      cases key with
      | none => exact allQueriesSatisfy_pure _ _
      | some key =>
          simp only [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
            RegistrationNativeKemInterface.server]
          split
          · simp only [RegistrationNativeKemInterface.encapsulate, simulateQ_map,
              simulateQ_spec_query, RegistrationNativeKemServerInterface.lift]
            cases chosen <;> simp only [lower, QueryImpl.apply_compose,
              RegistrationNativeKemFrontendInterface.lift]
            all_goals exact map_allowed _ _ (query_allowed _ trivial)
          · exact allQueriesSatisfy_pure _ _
  | _ =>
      simp only [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
        RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other,
        RegistrationNativeKemServerInterface.lift, simulateQ_spec_query, simulateQ_pure,
        lower, RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
        allQueriesSatisfy_query_iff, allQueriesSatisfy_pure, NoPut]

private theorem core_allowed (setup : Setup base KemSK) (checks : Checks) (chosen : Bool)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.agreementCore (n := n) (mlSource := mlSource) setup checks query)).AllQueriesSatisfy NoPut := by
  cases query <;> first
    | exact allQueriesSatisfy_pure _ _
    | exact primitive_allowed checks chosen _

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)

local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

private theorem modifier_keeps (chosen : Bool)
    (change : RegistrationNativeKemServerState.State n mlSource → RegistrationNativeKemServerState.State n mlSource)
    (preserved : ∀ state, (change state).beacons = state.beacons) :
    Keeps owners provider (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.modify change)) := by
  intro before after value supported
  have exactChange := RegistrationNativeKemOpenOwnersFrame.modify_owners setup checks wire route representation created credential
    selected pairs publicKey real chosen change before after value supported
  exact exactChange.trans (preserved (RegistrationNativeKemServerState.mask before.1.1))

private theorem agreement_keeps (chosen : Bool) (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    Keeps owners provider (simulateQ (lower chosen)
      (simulateQ (RegistrationNativeKemServerInterface.agreement setup checks) work)) := by
  rw [← QueryImpl.simulateQ_compose]
  apply simulate_keeps
  intro query
  simp only [QueryImpl.apply_compose, RegistrationNativeKemServerInterface.agreement, simulateQ_bind]
  apply bind_keeps
  · exact modifier_keeps setup checks wire route representation created credential selected pairs publicKey real chosen _ (fun _ => rfl)
  · intro ignored
    exact RegistrationNativeKemOpenOwnersFrame.no_put_keeps setup checks wire route representation created credential
      selected pairs publicKey real _ (core_allowed setup checks chosen query)

/-- Every actual agreement callback preserves all local owner fields under the open candidate provider. -/
theorem agreement_owners (chosen : Bool) (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen)
        (simulateQ (RegistrationNativeKemServerInterface.agreement setup checks) work))).run).run before)) :
    owners after = owners before :=
  agreement_keeps setup checks wire route representation created credential selected pairs publicKey real chosen work before after value supported

private theorem ambient_keeps (chosen : Bool)
    (query : (RegistrationNativeKemServerInterface.Ambient n mlSource).Domain)
    (allowed : NoPut (.inl (.inl (.inl query)))) :
    Keeps owners provider (simulateQ (lower chosen)
      ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl query) :
        OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) _)) := by
  apply RegistrationNativeKemOpenOwnersFrame.no_put_keeps
  simpa only [simulateQ_spec_query, lower, QueryImpl.apply_compose,
    RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
    allQueriesSatisfy_query_iff] using allowed

private theorem after_keeps (chosen : Bool) (authenticated : registration.AuthenticatedInit) :
    Keeps owners provider (simulateQ (lower chosen)
      (RegistrationNativeKemSdkCompiler.afterAuthentication setup checks authenticated)) := by
  simp only [RegistrationNativeKemSdkCompiler.afterAuthentication, simulateQ_bind]
  apply bind_keeps
  · exact ambient_keeps setup checks wire route representation created credential selected pairs publicKey real chosen .get trivial
  · intro localState
    split
    · exact pure_keeps owners provider _
    · split
      · simp only [simulateQ_bind]
        apply bind_keeps
        · exact agreement_keeps setup checks wire route representation created credential selected pairs publicKey real chosen _
        · intro completed
          cases completed with
          | fail error | div => exact pure_keeps owners provider _
          | ok effect =>
              cases effect <;> first
                | exact pure_keeps owners provider _
                | exact ambient_keeps setup checks wire route representation created credential selected pairs publicKey real chosen (.retain _) trivial
      · exact pure_keeps owners provider _

private theorem accept_keeps (chosen : Bool) (packet : registration.InitPacket) :
    Keeps owners provider (simulateQ (lower chosen)
      (RegistrationNativeKemServerInterface.accept setup checks packet)) := by
  simp only [RegistrationNativeKemServerInterface.accept, simulateQ_bind]
  apply bind_keeps
  · exact ambient_keeps setup checks wire route representation created credential selected pairs publicKey real chosen (.authenticate packet) trivial
  · intro checked
    cases checked with
    | fail error | div => exact pure_keeps owners provider _
    | ok result =>
        rcases result with ⟨events, result⟩
        cases result with
        | Accepted authenticated =>
            exact after_keeps setup checks wire route representation created credential selected pairs publicKey real chosen authenticated
        | _ => exact pure_keeps owners provider _

/-- Every actual open SDK accept preserves the complete owner roster through authentication, replay, agreement and retention failures. -/
theorem accept_owners (chosen : Bool) (packet : registration.InitPacket)
    (before after : State n mlSource KemSK) (value : RustM (Option Nat))
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen)
        (RegistrationNativeKemServerInterface.accept setup checks packet))).run).run before)) :
    owners after = owners before :=
  accept_keeps setup checks wire route representation created credential selected pairs publicKey real chosen packet before after value supported

/-- The literal parsed-attempt increment precedes the actual accept and preserves the same complete owner roster. -/
theorem typed_owners (chosen : Bool) (packet : registration.InitPacket)
    (before after : State n mlSource KemSK) (value : RustM (Option Nat))
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run before)) :
    owners after = owners before := by
  simp only [RegistrationNativeKemServerInterface.typedAccept, simulateQ_bind, OptionT.run_bind,
    Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, reached⟩, incremented, tail⟩ := supported
  cases reply with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some reply =>
      have stayed := accept_keeps setup checks wire route representation created credential selected pairs publicKey real
        chosen packet reached after value tail
      have increased := RegistrationNativeKemOpenOwnersFrame.modify_owners setup checks wire route representation created credential
        selected pairs publicKey real chosen (fun state => { state with parsedAccepts := state.parsedAccepts + 1 })
        before reached reply incremented
      exact stayed.trans increased

end BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.agreement_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.agreement_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.accept_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.accept_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.typed_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkOwners.typed_owners
