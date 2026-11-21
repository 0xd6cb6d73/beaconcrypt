-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! The original public finishOf witness identifies its same actual successful typed owner call in a chronological full-ledger execution, retaining the literal raw bytes and both complete source cut states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeInterface (Entry)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetPath (Path)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem finish_mem (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.finishOf transcript owner = some raw) :
    ∃ application, (⟨.inl (.inr (.finish owner raw)), some application⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | finish index bytes =>
        cases reply with
        | none => cases value
        | some application =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨application, member⟩
            · cases value
    | _ => cases value
  · cases value

private theorem native_finish (entry : Entry) (owner : Nat) (raw application : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.finish owner raw)), some application⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = (⟨.inl (.inr (.finish owner raw)), some application⟩ : Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The original first successful owner finish is the same native entry with its actual raw input and returned application. -/
theorem original_finish (entries : List Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.finishOf (entries.map Entry.erase) owner = some raw) :
    ∃ application, (⟨.inl (.inr (.finish owner raw)), some application⟩ : Entry) ∈ entries := by
  obtain ⟨application, member⟩ := finish_mem (entries.map Entry.erase) owner raw found
  obtain ⟨native, nativeMember, erased⟩ := List.mem_map.mp member
  exact ⟨application, native_finish native owner raw application erased ▸ nativeMember⟩

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

private theorem typed_success (owner : Nat) (raw application : Pqxdh.Bytes) (first last : State n KemSK source)
    (supported : (some application, last) ∈ support
      ((RegistrationNativeRawAdapter.handler wire typed (.inr (.finish owner raw))).run first)) :
    (.ok (some application), last) ∈ support
      ((typed (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw)))).run first) := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, current⟩, called, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      simpa only [actual] using called

/-- The literal original finish witness has one same-run successful typed call, exact full source cut states and its supported continuation. -/
theorem called (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (observed : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (actualPath : Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
      (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.finishOf observed.2.1.ledger.transcript owner = some raw) :
    ∃ application pre post first last,
      observed.2.1.transcript = pre ++ (⟨.inl (.inr (.finish owner raw)), some application⟩ : Entry) :: post ∧
      Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
        (RegistrationNativeLedger.empty, before) pre first ∧
      (.ok (some application), last.2) ∈ support
        ((typed (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw)))).run first.2) ∧
      Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) last post observed.2 := by
  let implementation := RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  rw [projected] at found
  obtain ⟨application, member⟩ := original_finish observed.2.1.transcript owner raw found
  obtain ⟨pre, post, recorded⟩ := List.mem_iff_append.mp member
  obtain ⟨first, last, prior, fullCall, later⟩ := RegistrationNativeSecretWordTargetPath.split implementation actualPath pre _ post recorded
  have rawCall := fullCall
  rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at rawCall
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := rawCall
  have replyEq : reply = some application := congrArg Prod.fst equal
  have stateEq : reached = last.2 := congrArg (fun result => result.2.2) equal
  subst reply
  rw [stateEq] at called
  exact ⟨application, pre, post, first, last, recorded, prior,
    typed_success setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey owner raw application first.2 last.2 called, later⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath.original_finish' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath.original_finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath.called' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath.called
