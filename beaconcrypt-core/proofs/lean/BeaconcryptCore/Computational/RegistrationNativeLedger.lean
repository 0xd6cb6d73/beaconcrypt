-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInterface
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! The original secrecy ledger runs above the ML-pin-aware native API. Native ordinary commands retain all public fields, and their analysis entries erase only the extra ML pin. Test and fresh execute the literal original ledger callback and its original coins/sends; native admission remains below those draws. The complete native transcript and original ledger have a derived projection invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeLedger
open RegistrationNativeInterface (Command Spec FullSpec Entry)
open PqxdhDeploymentInterface (Secrecy FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
variable {Reader Response Value : Type}

/-- A total embedding used only below secrecy callbacks. Its create branch is unreachable there, as secrecy_frame proves. -/
def legacyCommand : PqxdhDeploymentInterface.Command → Command
  | .create pin keyId => .create pin [] keyId
  | .bundle owner => .bundle owner
  | .accept raw => .accept raw
  | .build session payload => .build session payload
  | .finish owner raw => .finish owner raw
  | .hmac key message => .hmac key message
  | .hash bytes => .hash bytes
  | .serverSend keyId plaintext => .serverSend keyId plaintext
  | .serverRaw raw => .serverRaw raw
  | .beaconSend owner plaintext => .beaconSend owner plaintext
  | .beaconRaw owner raw => .beaconRaw owner raw

def legacyLift : QueryImpl PqxdhDeploymentInterface.Spec (OracleComp Spec)
  | .inl coin => Spec.query (.inl coin)
  | .inr (.create pin keyId) => Spec.query (.inr (.create pin [] keyId))
  | .inr (.bundle owner) => Spec.query (.inr (.bundle owner))
  | .inr (.accept raw) => Spec.query (.inr (.accept raw))
  | .inr (.build session payload) => Spec.query (.inr (.build session payload))
  | .inr (.finish owner raw) => Spec.query (.inr (.finish owner raw))
  | .inr (.hmac key message) => Spec.query (.inr (.hmac key message))
  | .inr (.hash bytes) => Spec.query (.inr (.hash bytes))
  | .inr (.serverSend keyId plaintext) => Spec.query (.inr (.serverSend keyId plaintext))
  | .inr (.serverRaw raw) => Spec.query (.inr (.serverRaw raw))
  | .inr (.beaconSend owner plaintext) => Spec.query (.inr (.beaconSend owner plaintext))
  | .inr (.beaconRaw owner raw) => Spec.query (.inr (.beaconRaw owner raw))

structure State where
  ledger : Ledger
  transcript : List Entry

def empty : State := ⟨Ledger.empty, []⟩

def Consistent (state : State) : Prop := state.ledger.transcript = state.transcript.map Entry.erase

def record (state : State) (entry : Entry) : State :=
  ⟨{ state.ledger with transcript := state.ledger.transcript ++ [entry.erase] }, state.transcript ++ [entry]⟩

noncomputable def handler (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) : QueryImpl FullSpec (StateT State (OracleComp Spec))
  | .inl core => fun state =>
      (fun reply => (reply, record state ⟨.inl core, reply⟩)) <$> (Spec.query core : OracleComp Spec _)
  | .inr secrecy => fun state =>
      (fun result => (result.1, State.mk result.2 (state.transcript ++ [⟨.inr secrecy, result.1⟩]))) <$>
        simulateQ legacyLift
          ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run state.ledger)

private theorem simulate_support {SourceTarget TargetIndex Result : Type}
    {source : OracleSpec SourceTarget} {target : OracleSpec TargetIndex}
    (implementation : QueryImpl source (OracleComp target)) (work : OracleComp source Result) (result : Result)
    (supported : result ∈ support (simulateQ implementation work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, mem_support_pure_iff] at supported
      simp only [mem_support_pure_iff, supported]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply tail⟩

private theorem original_record (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (secrecy : Secrecy) (before : Ledger)
    (result : Option RawCtxSourceSend.Encrypted × Ledger)
    (supported : result ∈ support
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before)) :
    result.2.transcript = before.transcript ++ [⟨.inr secrecy, result.1⟩] := by
  classical
  cases secrecy with
  | test handle left right =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
      split at supported
      · cases chosen : before.test with
        | none =>
            simp only [chosen, mem_support_bind_iff, mem_support_pure_iff] at supported
            obtain ⟨bit, bitReached, reply, replyReached, equal⟩ := supported
            cases equal
            rfl
        | some session =>
            simp only [chosen] at supported
            split at supported
            · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
              obtain ⟨reply, replyReached, equal⟩ := supported
              cases equal
              rfl
            · simp only [mem_support_pure_iff] at supported
              cases supported
              rfl
      · simp only [mem_support_pure_iff] at supported
        cases supported
        rfl
  | fresh handle length =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
      split at supported
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
        obtain ⟨message, messageReached, reply, replyReached, equal⟩ := supported
        cases equal
        rfl
      · simp only [mem_support_pure_iff] at supported
        cases supported
        rfl

/-- The new ordinary-command entry retains both public pins; the original ledger erases only the ML pin. -/
theorem query_forward (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (query : Spec.Domain) (state : State) :
    (handler crypto codec serverKid bounds (.inl query)).run state =
      (fun reply => (reply, record state ⟨.inl query, reply⟩)) <$> (Spec.query query : OracleComp Spec _) := rfl

/-- Test and fresh run the original ledger controller literally, with its original complete private test/fresh state. -/
theorem query_secrecy (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (secrecy : Secrecy) (state : State) :
    (handler crypto codec serverKid bounds (.inr secrecy)).run state =
      (fun result => (result.1, State.mk result.2 (state.transcript ++ [⟨.inr secrecy, result.1⟩]))) <$>
        simulateQ legacyLift
          ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run state.ledger) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original secrecy implementation cannot invoke the embedding's unused creation branch or any registration, hash or HMAC command. -/
theorem secrecy_frame (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (secrecy : Secrecy) (state : State) :
    ((handler crypto codec serverKid bounds (.inr secrecy)).run state).IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0 := by
  rw [query_secrecy, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound legacyLift (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) _ _ 0
    (PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy state.ledger)
  intro query
  cases query with
  | inl coin => simp [legacyLift, isQueryBoundP_query_iff, RegistrationNativeInterface.eraseCore,
      PqxdhDeploymentSecrecy.coinOrSend]
  | inr command =>
      cases command <;> simp only [legacyLift] <;> rw [isQueryBoundP_query_iff] <;>
        simp [RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentSecrecy.coinOrSend]

/-- Each actual native query preserves the exact original-ledger projection invariant. -/
theorem query_consistent (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain) (before : State)
    (consistent : Consistent before) (result : FullSpec.Range query × State)
    (supported : result ∈ support ((handler crypto codec serverKid bounds query).run before)) :
    Consistent result.2 := by
  unfold Consistent at consistent
  cases query with
  | inl core =>
      rw [query_forward, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      simp only [Consistent, record, List.map_append, List.map_cons, List.map_nil, consistent]
  | inr secrecy =>
      rw [query_secrecy, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have recorded := original_record crypto codec serverKid bounds secrecy before.ledger inner
        (simulate_support legacyLift _ inner reached)
      simp only [Consistent, List.map_append, List.map_cons, List.map_nil, Entry.erase, recorded, consistent]

/-- Native commands retain their extra public pin throughout arbitrary adaptive continuations, while the original complete secrecy ledger is exactly the derived projection. -/
theorem program_consistent (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (before : State)
    (consistent : Consistent before) (result : Value × State)
    (supported : result ∈ support ((simulateQ (handler crypto codec serverKid bounds) work).run before)) :
    Consistent result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact consistent
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, tail⟩ := supported
      exact ih inner.1 inner.2 (query_consistent crypto codec serverKid bounds query before consistent inner reached) result tail

/-- The actual wrapped native client starts with the original empty secrecy ledger and complete empty native transcript. -/
noncomputable def wrap (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) : OracleComp Spec (Value × State) :=
  (simulateQ (handler crypto codec serverKid bounds) work).run empty

noncomputable def interpreted {NativeState : Type}
    (native : QueryImpl Spec (StateT NativeState ProbComp))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (State × NativeState) ProbComp) :=
  (native.mapStateTBase (handler crypto codec serverKid bounds)).flattenStateT

/-- Executing the complete native API under its actual stateful handler equals executing its wrapped client, jointly over the full native transcript, original secrecy ledger and complete native poststate. -/
theorem run_wrap {NativeState : Type} (native : QueryImpl Spec (StateT NativeState ProbComp))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (before : NativeState) :
    (simulateQ (interpreted native crypto codec serverKid bounds) work).run (empty, before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ native (wrap crypto codec serverKid bounds work)).run before := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [interpreted]
  exact (id_map _).symm

/-- Every completed wrapped native execution has the original CE transcript, test state and fresh list alongside its full ML-pin-aware native transcript. -/
theorem wrap_consistent (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (result : Value × State)
    (supported : result ∈ support (wrap crypto codec serverKid bounds work)) :
    result.2.ledger.transcript = result.2.transcript.map Entry.erase :=
  program_consistent crypto codec serverKid bounds work empty rfl result supported

end BeaconcryptCore.Computational.RegistrationNativeLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.query_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.query_forward
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.query_secrecy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.query_secrecy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.secrecy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.secrecy_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.query_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.query_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.program_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.wrap_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.wrap_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedger.run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedger.run_wrap
