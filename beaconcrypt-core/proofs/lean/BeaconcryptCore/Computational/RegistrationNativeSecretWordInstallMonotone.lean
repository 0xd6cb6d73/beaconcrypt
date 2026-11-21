-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource

/-! Every original callback appends to each role's successful installation list. Existing ordinal witnesses therefore survive all later preparations, demands, failures and unrelated successful insertions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordFrontendTrace (State handler begin finish)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
variable {n : Nat} {KemSK Value : Type}

private theorem installed (role : Role) (reply : Bool) (before : State) :
    ∃ added, messages role (RegistrationNativeSecretWordFrontendTrace.installed role reply
      (RegistrationNativeSecretWordFrontendTrace.attempt role before)).events = messages role before.events ++ added := by
  cases reply with
  | false =>
      refine ⟨[], ?_⟩
      cases current : before.current <;> simp [RegistrationNativeSecretWordFrontendTrace.installed,
        RegistrationNativeSecretWordFrontendTrace.attempt, current, messages, List.filterMap_append]
  | true => cases current : before.current with
    | none => exact ⟨[], by simp [RegistrationNativeSecretWordFrontendTrace.installed, RegistrationNativeSecretWordFrontendTrace.attempt, current]⟩
    | some message =>
        exact ⟨[message], by simp [RegistrationNativeSecretWordFrontendTrace.installed,
          RegistrationNativeSecretWordFrontendTrace.attempt, current, messages, List.filterMap_append, List.append_assoc]⟩

/-- Every actual callback extends each role's successful descriptor list, including callbacks that clear the current demand. -/
theorem query (role : Role) (request : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range request) (before : State) :
    ∃ added, messages role (finish request reply (begin request before)).events = messages role before.events ++ added := by
  by_cases active : GlobalInstall role request
  · rcases request with (prepare | (demand | (publication | environment)) | kem) | record
    · cases active
    · cases active
    · cases active
    · rcases environment with coin | capability
      · cases active
      · cases capability with
        | installServer keyId binding kernel =>
            change role = .server at active
            subst role
            exact installed .server reply before
        | installBeacon owner shell kernel =>
            change role = .beacon at active
            subst role
            exact installed .beacon reply before
        | _ => cases active
    · cases active
    · cases active
  · exact ⟨[], by rw [RegistrationNativeSecretWordInstallTrace.query_free role request reply before active, List.append_nil]⟩

/-- Actual adaptive observer execution retains every earlier successful installation at its original ordinal. -/
theorem program (role : Role) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler work).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨[], (List.append_nil _).symm⟩
  | query_bind request next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _called, continued⟩ := supported
      obtain ⟨head, first⟩ := query role request reply before
      obtain ⟨tail, last⟩ := ih reply _ continued
      exact ⟨head ++ tail, by rw [last, first, List.append_assoc]⟩

/-- The concrete monitored typed source retains every earlier successful descriptor through its original World and private interpreter. -/
theorem typed {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (outer : QueryImpl RegistrationNativeSecretWordService.Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (role : Role)
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeSecretWordTargetTracedSource.State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × RegistrationNativeSecretWordTargetTracedSource.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey request).run before)) :
    ∃ added, messages role result.2.1.2.events = messages role before.1.2.events ++ added := by
  simp only [RegistrationNativeSecretWordTargetTracedSource.typed, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have possible : reached.1 ∈ support ((simulateQ handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey request).run before.1.1)).run before.1.2) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  cases returned
  exact program role _ before.1.2 reached.1 possible
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone.typed
