-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenReceipts
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! A canonical original native accept in the candidate hybrid yields its actual open SDK call. The receipt uses the original successful session and actual parsed prefix; it does not replace the candidate provider with the real closed SDK. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State counter)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeKemOpenProvider.implementation RegistrationNativeKemParsedRouting.handler
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)

local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real
local notation "native" => RegistrationNativeKemOpenRawCounter.native (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed

/-- A successful original raw callback comes from the literal successful typed SDK reply under the same candidate provider. -/
theorem raw_success (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : State n mlSource KemSK) (read : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some (some session), last) ∈ support (((native (.inr (.accept raw))).run).run first)) :
    (some (.ok (some session)), last) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed
        (.inr (.accept packet)))).run).run first) := by
  simp only [RegistrationNativeKemOpenRawCounter.native, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, read, simulateQ_map,
    simulateQ_spec_query, OptionT.run_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := supported
  cases reply with
  | none =>
      have impossible := congrArg Prod.fst equal
      simp only [Option.map_none, reduceCtorEq] at impossible
  | some reply =>
      cases reply with
      | fail error | div =>
          simp only [Option.map_some, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq,
            Option.some.injEq, reduceCtorEq, false_and] at equal
      | ok reply =>
          simp only [Option.map_some, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq,
            Option.some.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          exact called

/-- The private parsed-prefix receipt selects the actual open typed accept, keeping its candidate KEM callbacks exposed. -/
theorem selected_success (packet : registration.InitPacket) (session : Nat) (first last : State n mlSource KemSK)
    (counted : counter first = parsed)
    (supported : (some (.ok (some session)), last) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed
        (.inr (.accept packet)))).run).run first)) :
    (some (.ok (some session)), last) ∈ support
      (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run
          ((RegistrationNativeKemServerState.mask first.1.1, first.1.2), first.2)) := by
  simp only [RegistrationNativeKemParsedRouting.handler, RegistrationNativeKemParsedRouting.get,
    simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
  rw [RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  have selected : (RegistrationNativeKemServerState.mask first.1.1).parsedAccepts = parsed := counted
  simpa only [selected, decide_true, RegistrationNativeKemDispatcherCompiler.handler,
    RegistrationNativeKemOpenFrame.lower, QueryImpl.simulateQ_compose] using supported

/-- A complete candidate-provider execution derives the actual selected successful SDK call from the original canonical accept entry. -/
theorem call_of_accept (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before after : State n mlSource KemSK) (zero : counter before = 0)
    (value : Value) (ledger : RegistrationNativeLedger.State) (session : Nat)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire ledger.transcript session parsed) :
    ∃ pre raw packet post first last,
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session)) :: post ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧ counter first = parsed ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  obtain ⟨pre, raw, packet, post, trace, count, read, _first⟩ := accepted
  have receipts := (RegistrationNativeKemOpenReceipts.program_receipts setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds mode work before after value ledger supported).2
  obtain ⟨first, last, counted, reached⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session⟩ post trace
  have countedFirst : counter first = parsed := by simpa only [zero, Nat.zero_add, count] using counted
  have typed := raw_success setup checks wire route representation created credential selected pairs publicKey real parsed
    raw packet session first last read reached
  exact ⟨pre, raw, packet, post, ((RegistrationNativeKemServerState.mask first.1.1, first.1.2), first.2), last,
    trace, count, read, countedFirst,
    selected_success setup checks wire route representation created credential selected pairs publicKey real parsed
      packet session first last countedFirst typed⟩

end BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.raw_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.raw_success
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.selected_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.selected_success
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.call_of_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall.call_of_accept
