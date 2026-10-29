-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentInterface

/-! The native deployment API carries both actual public pins at Beacon creation. Every other command and reply is the original CE command and reply. The original event ledger is reached by an explicit projection that forgets only the extra ML public pin; the complete native transcript retains it. This projection asserts no cryptographic membership, parser correctness or game simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInterface
open PqxdhDeploymentInterface (Mode Secrecy SecrecySpec Budget)

inductive Command where
  | create (edPin mlPin : Pqxdh.Bytes) (keyId : Std.U64)
  | bundle (owner : Nat)
  | accept (raw : Pqxdh.Bytes)
  | build (session : Nat) (payload : Option Pqxdh.Bytes)
  | finish (owner : Nat) (raw : Pqxdh.Bytes)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | serverSend (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
  | serverRaw (raw : Pqxdh.Bytes)
  | beaconSend (owner : Nat) (plaintext : Pqxdh.Bytes)
  | beaconRaw (owner : Nat) (raw : Pqxdh.Bytes)

def eraseCommand : Command → PqxdhDeploymentInterface.Command
  | .create edPin _ keyId => .create edPin keyId
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

abbrev CommandSpec : OracleSpec Command := fun command => PqxdhDeploymentInterface.CommandSpec (eraseCommand command)
abbrev SuccessSpec : OracleSpec Command := fun command => PqxdhDeploymentInterface.SuccessSpec (eraseCommand command)
abbrev Spec := unifSpec + CommandSpec
abbrev FullSpec := Spec + SecrecySpec
abbrev FullSuccessSpec := (unifSpec + SuccessSpec) + SecrecySpec
abbrev Query := FullSpec.Domain

def eraseCore : Spec.Domain → PqxdhDeploymentInterface.Spec.Domain
  | .inl coin => .inl coin
  | .inr command => .inr (eraseCommand command)

def eraseQuery : Query → PqxdhDeploymentInterface.Query
  | .inl core => .inl (eraseCore core)
  | .inr secrecy => .inr secrecy

abbrev ModeSpec : Mode → OracleSpec Query
  | .O => FullSpec
  | .P => FullSuccessSpec

def project : (mode : Mode) → (query : Query) → FullSpec.Range query → (ModeSpec mode).Range query
  | .O, _, reply => reply
  | .P, .inl (.inl _), reply => reply
  | .P, .inl (.inr command), reply => PqxdhDeploymentInterface.project .P (.inl (.inr (eraseCommand command))) reply
  | .P, .inr _, reply => reply

def observeFull : QueryImpl FullSuccessSpec (OracleComp FullSpec)
  | .inl (.inl coin) => FullSpec.query (.inl (.inl coin))
  | .inl (.inr command) => do
      let reply ← (FullSpec.query (.inl (.inr command)) : OracleComp FullSpec _)
      pure (PqxdhDeploymentInterface.project .P (.inl (.inr (eraseCommand command))) reply)
  | .inr secrecy => FullSpec.query (.inr secrecy)

def asModeO {Value : Type} : (mode : Mode) → OracleComp (ModeSpec mode) Value → OracleComp FullSpec Value
  | .O, work => work
  | .P, work => simulateQ observeFull work

structure Entry where
  query : Query
  reply : FullSpec.Range query

def Entry.erase (entry : Entry) : PqxdhDeploymentInterface.Entry :=
  match entry with
  | ⟨.inl (.inl coin), reply⟩ => ⟨.inl (.inl coin), reply⟩
  | ⟨.inl (.inr command), reply⟩ => ⟨.inl (.inr (eraseCommand command)), reply⟩
  | ⟨.inr secrecy, reply⟩ => ⟨.inr secrecy, reply⟩

def queryClass (query : Query) : Fin 14 := PqxdhDeploymentInterface.queryClass (eraseQuery query)

def Respects {mode : Mode} {Value : Type} (budget : Budget) (work : OracleComp (ModeSpec mode) Value) : Prop :=
  ∀ kind, work.IsQueryBoundP (fun query => queryClass query = kind) (budget.cap kind)

/-- The public analysis projection preserves every original command operand except the additional ML pin. -/
theorem erase_create (edPin mlPin : Pqxdh.Bytes) (keyId : Std.U64) (reply : Option Nat) :
    (Entry.mk (.inl (.inr (.create edPin mlPin keyId))) reply).erase =
      ⟨.inl (.inr (.create edPin keyId)), reply⟩ := rfl

/-- Mode P keeps all native public fields while projecting only actual raw receive replies. -/
theorem observe_project (query : Query) :
    observeFull query = project .P query <$> (FullSpec.query query : OracleComp FullSpec _) := by
  cases query with
  | inl core => cases core with
    | inl coin => exact (id_map _).symm
    | inr command => rfl
  | inr secrecy => exact (id_map _).symm

/-- No raw bytes, plaintext-independent registration reply or secrecy reply are changed by ledger erasure. -/
theorem erase_entry_query (entry : Entry) : entry.erase.query = eraseQuery entry.query := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩ <;> rfl

/-- Switching observation mode preserves every original budget coordinate, including the fresh-message class. -/
theorem asModeO_bound {mode : Mode} {Value : Type} (budget : Budget)
    (work : OracleComp (ModeSpec mode) Value) (bounded : Respects budget work) (kind : Fin 14) :
    (asModeO mode work).IsQueryBoundP (fun query => queryClass query = kind) (budget.cap kind) := by
  cases mode with
  | O => exact bounded kind
  | P =>
      apply RawCtxSourceOpen.simulate_bound observeFull (fun query => queryClass query = kind) _ _ _ (bounded kind)
      intro query
      rw [observe_project, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro counted
      simp only [counted, ite_true]
      decide

end BeaconcryptCore.Computational.RegistrationNativeInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInterface.erase_create' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInterface.erase_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInterface.observe_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInterface.observe_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInterface.erase_entry_query' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInterface.erase_entry_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInterface.asModeO_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInterface.asModeO_bound
