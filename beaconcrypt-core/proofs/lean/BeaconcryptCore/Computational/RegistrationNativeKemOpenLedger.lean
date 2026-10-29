-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter
import BeaconcryptCore.Computational.RegistrationNativeOptionalSupport

/-! The open candidate source executes the literal original secrecy ledger. Its parsed counter follows the original public transcript while fresh/test retain their original hidden draws and native send ordering. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State counter)
open RegistrationNativeEvents (parsedAccept parsedAcceptCount)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem send_increment (wire : Wire) (query : RegistrationNativeInterface.Spec.Domain)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false) :
    RegistrationNativeKemOpenRawCounter.increment wire query = 0 := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> simp_all [RegistrationNativeKemOpenRawCounter.increment,
      PqxdhDeploymentSecrecy.coinOrSend, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand]

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)

local notation "native" => RegistrationNativeKemOpenRawCounter.native (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed

noncomputable def step (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State) :=
  simulateQ native ((RegistrationNativeLedger.handler setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    created.server.server.metadata.sender bounds query).run before)

/-- The actual source interpretation of every original coins-and-sends program retains the parsed counter, including refused sends. -/
theorem restricted_counter (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support (((simulateQ native work).run).run before)) :
    counter after = counter before := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure original =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
      rw [supported.2]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have restricted := allowed.resolve_right (by omega)
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
            reduceCtorEq, false_and] at tail
      | some reply =>
          have stepped := RegistrationNativeKemOpenRawCounter.raw_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed query before reached reply called
          rw [send_increment wire query restricted, Nat.add_zero] at stepped
          exact (ih reply (by simpa using rest reply) reached after tail).trans stepped

private theorem ledger_trace (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State)
    (result : RegistrationNativeInterface.FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl query =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _called, rfl⟩ := supported
      rfl
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨reply, _called, rfl⟩ := supported
      rfl

/-- Every completed open full-interface step appends its literal original native entry outside the actual callback. -/
theorem step_trace (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (value : RegistrationNativeInterface.FullSpec.Range query)
    (supported : (some (value, afterLedger), after) ∈ support
      (((step setup checks wire route representation created credential selected pairs publicKey real parsed bounds query beforeLedger).run).run before)) :
    afterLedger.transcript = beforeLedger.transcript ++ [⟨query, value⟩] :=
  ledger_trace setup wire created bounds query beforeLedger (value, afterLedger)
    (RegistrationNativeOptionalSupport.completed_support native _ (value, afterLedger) before after supported)

/-- Native core entries preserve their original public bytes and complete source poststate. -/
theorem core_run (bounds : FreshBounds) (query : RegistrationNativeInterface.Spec.Domain)
    (ledger : RegistrationNativeLedger.State) (before : State n mlSource KemSK) :
    (((step setup checks wire route representation created credential selected pairs publicKey real parsed bounds (.inl query) ledger).run).run before) =
      (fun result => (result.1.map fun reply => (reply, RegistrationNativeLedger.record ledger ⟨.inl query, reply⟩), result.2)) <$>
        (((native query).run).run before) := by
  simp only [step, RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query,
    OptionT.run_map, StateT.run_map]
  rfl

/-- The original private secrecy controller keeps the parsed counter while preserving its exact private ledger result. -/
theorem secrecy_counter (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Secrecy)
    (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (value : Option RawCtxSourceSend.Encrypted)
    (supported : (some (value, afterLedger), after) ∈ support
      (((step setup checks wire route representation created credential selected pairs publicKey real parsed bounds (.inr query) beforeLedger).run).run before)) :
    counter after = counter before :=
  restricted_counter setup checks wire route representation created credential selected pairs publicKey real parsed _
    (RegistrationNativeLedger.secrecy_frame setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender bounds query beforeLedger) before after (value, afterLedger) supported

/-- The complete open candidate step derives the original parsed-prefix equation rather than assuming a selector invariant. -/
theorem step_counter (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (prior : counter before = offset + parsedAcceptCount wire beforeLedger.transcript)
    (value : RegistrationNativeInterface.FullSpec.Range query)
    (supported : (some (value, afterLedger), after) ∈ support
      (((step setup checks wire route representation created credential selected pairs publicKey real parsed bounds query beforeLedger).run).run before)) :
    counter after = offset + parsedAcceptCount wire afterLedger.transcript := by
  cases query with
  | inl query =>
      rw [core_run, support_map] at supported
      obtain ⟨⟨reply, reached⟩, called, returned⟩ := supported
      cases reply with
      | none =>
          have impossible := congrArg Prod.fst returned
          simp only [Option.map_none, reduceCtorEq] at impossible
      | some reply =>
          have sameState := congrArg Prod.snd returned
          change reached = after at sameState
          subst after
          have sameLedger := congrArg (fun result => result.1.map Prod.snd) returned
          simp only [Option.map_some, Option.some.injEq] at sameLedger
          rw [← sameLedger]
          have counted := RegistrationNativeKemOpenRawCounter.raw_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed query before reached reply called
          rw [RegistrationNativeKemOpenRawCounter.entry_increment wire query reply, prior] at counted
          cases chosen : parsedAccept wire ⟨.inl query, reply⟩ <;>
            simpa [RegistrationNativeLedger.record, parsedAcceptCount, List.filter_append, chosen,
              Bool.toNat, Nat.add_assoc] using counted
  | inr query =>
      have unchanged := secrecy_counter setup checks wire route representation created credential selected pairs publicKey real parsed
        bounds query beforeLedger afterLedger before after value supported
      have appended := step_trace setup checks wire route representation created credential selected pairs publicKey real parsed
        bounds (.inr query) beforeLedger afterLedger before after value supported
      simpa only [appended, parsedAcceptCount, List.filter_append, parsedAccept, List.filter_cons,
        List.filter_nil, Bool.false_eq_true, ite_false, List.append_nil] using unchanged.trans prior

end BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.restricted_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.restricted_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.step_trace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.core_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.core_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.secrecy_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.secrecy_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger.step_counter
