-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRaw

/-! The concrete symbolic source counter agrees with the complete original native public ledger under arbitrary outer material replies. Hidden-bit and fresh-message draws remain above dispatch; refused sends and every failed raw poststate retain their actual ledger entry. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeWire (Wire)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeEvents (parsedAcceptCount parsedAccept)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := mlSource)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

noncomputable abbrev native : QueryImpl RegistrationNativeInterface.Spec (StateT (State n KemSK mlSource) ProbComp) :=
  RegistrationNativeRawAdapter.handler wire typed

private theorem send_increment (wire : Wire) (query : RegistrationNativeInterface.Spec.Domain)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false) :
    RegistrationNativeSecretWordTargetRaw.increment wire query = 0 := by
  cases query with
  | inl coin => rfl
  | inr command =>
      cases command <;> simp_all [RegistrationNativeSecretWordTargetRaw.increment,
        PqxdhDeploymentSecrecy.coinOrSend, RegistrationNativeInterface.eraseCore,
        RegistrationNativeInterface.eraseCommand]

/-- The actual source interpretation of any coins-and-sends AST keeps the parsed-call counter. -/
theorem restricted_counter (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (reached : result ∈ support ((simulateQ (native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) work).run before)) :
    result.2.1.parsedAccepts = before.1.parsedAccepts := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have restricted := allowed.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      have stepped := RegistrationNativeSecretWordTargetRaw.raw_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query before middle first
      rw [send_increment wire query restricted, Nat.add_zero] at stepped
      exact (ih middle.1 (by simpa using rest middle.1) middle.2 result tail).trans stepped

private theorem ledger_trace (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (result : RegistrationNativeInterface.FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl query =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl
  | inr query =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl

/-- The literal original secrecy step never advances the parsed-call counter, even when its eventual send is refused. -/
theorem secrecy_counter (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (result : Option RawCtxSourceSend.Encrypted × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds
      (typed)
      (.inr query)).run before)) : result.2.2.1.parsedAccepts = before.2.1.parsedAccepts := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact restricted_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey _
    (RegistrationNativeLedger.secrecy_frame setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds query before.1) before.2 inner supported

/-- Each complete original full-interface step preserves the counter-to-public-prefix equation. -/
theorem step_counter (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (prior : before.2.1.parsedAccepts = offset + parsedAcceptCount wire before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    result.2.2.1.parsedAccepts = offset + parsedAcceptCount wire result.2.1.transcript := by
  cases query with
  | inl query =>
      rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
        QueryImpl.flattenStateT_mapStateTBase_apply_run] at reached
      simp only [RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query,
        StateT.run_map, Functor.map_map, support_map] at reached
      obtain ⟨inner, supported, rfl⟩ := reached
      have counted := RegistrationNativeSecretWordTargetRaw.raw_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query before.2 inner supported
      rw [RegistrationNativeSecretWordTargetRaw.entry_increment wire query inner.1, prior] at counted
      cases chosen : parsedAccept wire ⟨.inl query, inner.1⟩ <;>
        simpa [RegistrationNativeLedger.record, parsedAcceptCount, List.filter_append,
          chosen, Bool.toNat, Nat.add_assoc] using counted
  | inr query =>
      have unchanged := secrecy_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result reached
      rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
        QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
      obtain ⟨inner, supported, equal⟩ := reached
      have localSupport := OracleComp.support_simulateQ_run'_subset
        (native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
        ((RegistrationNativeLedger.handler setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
          serverKeyId bounds (.inr query)).run before.1) before.2
      have original : inner.1 ∈ support ((RegistrationNativeLedger.handler setup.source.crypto
          (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds (.inr query)).run before.1) := by
        apply localSupport
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst supported
      have appended := ledger_trace setup.source.crypto wire serverKeyId bounds (.inr query) before.1 inner.1 original
      cases equal
      simpa only [appended, parsedAcceptCount, List.filter_append, parsedAccept, List.filter_cons,
        List.filter_nil, Bool.false_eq_true, ite_false, List.append_nil] using unchanged.trans prior

/-- Ordinary raw entries are logged outside their actual native callback, retaining its full poststate. -/
theorem core_run (bounds : FreshBounds) (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource) :
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
      (typed)
      (.inl query)).run before =
      (fun result => (result.1, (RegistrationNativeLedger.record before.1 ⟨.inl query, result.1⟩, result.2))) <$>
        (native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query).run before.2 := by
  rcases before with ⟨ledger, sourceBefore⟩
  simp only [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, RegistrationNativeLedger.query_forward,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- Every supported full step appends exactly its original native query and reply. -/
theorem step_trace (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  apply ledger_trace setup.source.crypto wire serverKeyId bounds query before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.restricted_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.restricted_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.secrecy_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.secrecy_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.step_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.core_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.core_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger.step_trace
