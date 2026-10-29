-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationNativeLedgerCaps

/-! The public raw native API decodes all native Init/response fields and retains complete failed poststates through its typed source operations. Malformed accept and invalid constructor pins stop before a typed callback. Build always consumes its one-use token through a typed call, including conversion failure. Finish always reaches the typed lifecycle operation even when response parsing fails, so its already-moved InitSent capability is aborted. Reserve and cryptographic admission gates belong to the actual typed frontend, below the unchanged secrecy draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRawAdapter
open RegistrationNativeWire (Wire)
open RegistrationNativeInterface (Spec)
open PqxdhBeaconPhase2Preparation (Word32)
variable {Value NativeState : Type}

inductive Command where
  | create (edPin : Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
  | bundle (owner : Nat)
  | accept (packet : registration.InitPacket)
  | build (session : Nat) (application : Option (Slice U8))
  | finish (owner : Nat) (packet : Option registration.ResponsePacket)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | serverSend (keyId : U64) (plaintext : Pqxdh.Bytes)
  | serverRaw (raw : Pqxdh.Bytes)
  | beaconSend (owner : Nat) (plaintext : Pqxdh.Bytes)
  | beaconRaw (owner : Nat) (raw : Pqxdh.Bytes)

abbrev CommandSpec : OracleSpec Command
  | .create _ _ _ => RustM (Option Nat)
  | .bundle _ => RustM (Option Pqxdh.Bytes)
  | .accept _ => RustM (Option Nat)
  | .build _ _ => RustM (Option (U64 × Pqxdh.Bytes))
  | .finish _ _ => RustM (Option Pqxdh.Bytes)
  | .hmac _ _ => PqxdhSecretInputKdf.HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .serverSend _ _ => Option RawCtxSourceSend.Encrypted
  | .serverRaw _ => core.option.Option RawCtxWholeOwner.Decrypted
  | .beaconSend _ _ => Option RawCtxSourceSend.Encrypted
  | .beaconRaw _ _ => core.option.Option RawCtxWholeOwner.Decrypted

abbrev TypedSpec := unifSpec + CommandSpec

def resultOption {Result : Type} : RustM (Option Result) → Option Result
  | .ok reply => reply
  | .fail _ | .div => none

def responseOption (result : RustM (Option (U64 × Pqxdh.Bytes))) :
    Option PqxdhServerRegistrationPublication.Response :=
  (resultOption result).map fun reply => ⟨reply.2, reply.1⟩

/-- The source default is one ff byte; an explicitly empty application stays empty. None here is a conversion failure and still consumes the moved build handle. -/
def application (payload : Option Pqxdh.Bytes) : Option (Slice U8) :=
  let bytes := payload.getD [0xff]
  if width : bytes.length ≤ Std.Usize.max then
    some ⟨bytes.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte, by simpa using width⟩
  else none

def adapter (wire : Wire) : QueryImpl Spec (OracleComp TypedSpec)
  | .inl coin => TypedSpec.query (.inl coin)
  | .inr (.create edPin mlPin keyId) =>
      match PqxdhDeploymentInterface.parsePin edPin, RegistrationNativeWire.parseMldsaPin mlPin with
      | some edPin, some mlPin => resultOption <$> (TypedSpec.query (.inr (.create edPin mlPin keyId)) : OracleComp TypedSpec _)
      | _, _ => pure none
  | .inr (.bundle owner) => resultOption <$> (TypedSpec.query (.inr (.bundle owner)) : OracleComp TypedSpec _)
  | .inr (.accept raw) =>
      match RegistrationNativeWire.readInit wire raw with
      | none => pure none
      | some packet => resultOption <$> (TypedSpec.query (.inr (.accept packet)) : OracleComp TypedSpec _)
  | .inr (.build session payload) =>
      responseOption <$> (TypedSpec.query (.inr (.build session (application payload))) : OracleComp TypedSpec _)
  | .inr (.finish owner raw) =>
      resultOption <$> (TypedSpec.query (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) : OracleComp TypedSpec _)
  | .inr (.hmac key message) => TypedSpec.query (.inr (.hmac key message))
  | .inr (.hash bytes) => TypedSpec.query (.inr (.hash bytes))
  | .inr (.serverSend keyId plaintext) => TypedSpec.query (.inr (.serverSend keyId plaintext))
  | .inr (.serverRaw raw) => TypedSpec.query (.inr (.serverRaw raw))
  | .inr (.beaconSend owner plaintext) => TypedSpec.query (.inr (.beaconSend owner plaintext))
  | .inr (.beaconRaw owner raw) => TypedSpec.query (.inr (.beaconRaw owner raw))

def compile (wire : Wire) (work : OracleComp Spec Value) : OracleComp TypedSpec Value := simulateQ (adapter wire) work

def handler (wire : Wire) (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) :
    QueryImpl Spec (StateT NativeState ProbComp) := typed ∘ₛ adapter wire

/-- A malformed Init packet triggers no typed authentication, replay reservation or agreement effect. -/
theorem accept_rejected (wire : Wire) (raw : Pqxdh.Bytes)
    (rejected : RegistrationNativeWire.readInit wire raw = none) : adapter wire (.inr (.accept raw)) = pure none := by
  simp only [adapter, rejected]

/-- Malformed responses still execute the typed finish lifecycle, which consumes and aborts an existing pending Beacon. -/
theorem finish_rejected (wire : Wire) (owner : Nat) (raw : Pqxdh.Bytes)
    (rejected : RegistrationNativeWire.readResponse wire raw = none) :
    adapter wire (.inr (.finish owner raw)) =
      resultOption <$> (TypedSpec.query (.inr (.finish owner none)) : OracleComp TypedSpec _) := by
  simpa only [adapter] using congrArg (fun packet : Option registration.ResponsePacket =>
    resultOption <$> (TypedSpec.query (.inr (.finish owner packet)) : OracleComp TypedSpec _)) rejected

/-- Build conversion failure still reaches its typed consume/cancel operation; it is never modeled as a pure raw rejection. -/
theorem build_rejected (wire : Wire) (session : Nat) (payload : Option Pqxdh.Bytes)
    (rejected : application payload = none) :
    adapter wire (.inr (.build session payload)) =
      responseOption <$> (TypedSpec.query (.inr (.build session none)) : OracleComp TypedSpec _) := by
  simpa only [adapter] using congrArg (fun slice : Option (Slice U8) =>
    responseOption <$> (TypedSpec.query (.inr (.build session slice)) : OracleComp TypedSpec _)) rejected

/-- Native default and explicit empty application remain distinct, with every actual byte preserved. -/
theorem application_bytes (payload : Option Pqxdh.Bytes) (slice : Slice U8)
    (parsed : application payload = some slice) : TranscriptAuthParts.absSlice slice = payload.getD [0xff] := by
  dsimp only [application] at parsed
  split at parsed
  · cases parsed
    simp [TranscriptAuthParts.absSlice, List.map_map, Function.comp_def]
  · cases parsed

/-- Actual raw failures only project replies; the typed callback's entire reached native state remains unchanged. -/
theorem finish_state (wire : Wire) (typed : QueryImpl TypedSpec (StateT NativeState ProbComp))
    (owner : Nat) (raw : Pqxdh.Bytes) (before : NativeState) :
    (handler wire typed (.inr (.finish owner raw))).run before =
      Prod.map resultOption id <$>
        (typed (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw)))).run before := by
  simp only [handler, QueryImpl.apply_compose, adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rfl

/-- Compiling arbitrary adaptive raw clients preserves every typed failure poststate; there is no whole-game equality hypothesis. -/
theorem program_native (wire : Wire) (typed : QueryImpl TypedSpec (StateT NativeState ProbComp))
    (work : OracleComp Spec Value) (before : NativeState) :
    (simulateQ (handler wire typed) work).run before = (simulateQ typed (compile wire work)).run before := by
  rw [handler, compile, QueryImpl.simulateQ_compose]

def kind : TypedSpec.Domain → Fin 12
  | .inl _ => 0
  | .inr (.create _ _ _) => 1
  | .inr (.bundle _) => 2
  | .inr (.accept _) => 3
  | .inr (.build _ _) => 4
  | .inr (.finish _ _) => 5
  | .inr (.hmac _ _) => 6
  | .inr (.hash _) => 7
  | .inr (.serverSend _ _) => 8
  | .inr (.serverRaw _) => 9
  | .inr (.beaconSend _ _) => 10
  | .inr (.beaconRaw _ _) => 11

/-- Parsing and representation introduce no additional typed query and preserve every native command class. -/
theorem query_bound (wire : Wire) (query : Spec.Domain) (selected : Fin 12) :
    (adapter wire query).IsQueryBoundP (fun query => kind query = selected)
      (if RegistrationNativeLedgerCaps.coreKind query = selected then 1 else 0) := by
  cases query with
  | inl coin =>
      simp only [adapter, isQueryBoundP_query_iff, kind, RegistrationNativeLedgerCaps.coreKind,
        RegistrationNativeInterface.eraseCore, PqxdhDeploymentCompileBudget.commandKind]
      intro counted
      simp only [counted, ite_true]
      decide
  | inr command =>
      cases command <;> simp only [adapter]
      all_goals repeat split
      all_goals first
        | trivial
        | simp_all [isQueryBoundP_map_iff, isQueryBoundP_query_iff, kind, RegistrationNativeLedgerCaps.coreKind,
            RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand,
            PqxdhDeploymentCompileBudget.commandKind]

/-- Raw native compilation preserves the supplied actual command bill through all adaptive replies. -/
theorem compile_bound (wire : Wire) (work : OracleComp Spec Value) (selected : Fin 12) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeLedgerCaps.coreKind query = selected) cap) :
    (compile wire work).IsQueryBoundP (fun query => kind query = selected) cap :=
  RawCtxSourceOpen.simulate_bound (adapter wire) _ _ work cap bounded (fun query => query_bound wire query selected)

end BeaconcryptCore.Computational.RegistrationNativeRawAdapter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.accept_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.accept_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.finish_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.finish_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.build_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.build_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.application_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.application_bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.finish_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.finish_state
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.program_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.query_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawAdapter.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawAdapter.compile_bound
