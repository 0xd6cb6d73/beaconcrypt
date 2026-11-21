-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementKemBounds
import BeaconcryptCore.Computational.RegistrationNativeKemInterface
/-! Actual indexed native Server and Beacon KEM interfaces preserve the source agreement call caps. Invalid recipient keys, absent ciphertexts/handles and every failed optional prefix keep their actual zero-call behavior. Root HKDF and non-KEM callbacks introduce no KEM algorithm call. These resource certificates concern the request tree before primitive interpretation and do not substitute for an operational recipient-failure monitor. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCallBounds
open RegistrationAgreementKemBounds (Kind counted)
open RegistrationNativeKemInterface (Spec OtherSpec)
variable {I KemSK A : Type} {ambient : OracleSpec I}

def Counted : Kind → (Sum I (Sum PqxdhLiveKemBirth.Query PqxdhKemIndCca.MlKem768PublicKey)) → Prop
  | .encapsulate, .inr (.inr _) => True
  | .decapsulate, .inr (.inl (.decapsulate _ _)) => True
  | _, _ => False

instance (kind : Kind) (query : Sum I (Sum PqxdhLiveKemBirth.Query PqxdhKemIndCca.MlKem768PublicKey)) : Decidable (Counted kind query) := by
  cases kind with
  | encapsulate =>
      rcases query with query | (query | key)
      · exact isFalse (fun impossible => impossible)
      · exact isFalse (fun impossible => impossible)
      · exact isTrue trivial
  | decapsulate =>
      rcases query with query | (query | key)
      · exact isFalse (fun impossible => impossible)
      · cases query with
        | create | reveal handle => exact isFalse (fun impossible => impossible)
        | decapsulate handle ciphertext => exact isTrue trivial
      · exact isFalse (fun impossible => impossible)

theorem server_step (kind : Kind) (checks : PqxdhServerAuthExperiment.Checks)
    (query : RegistrationAgreementShared.PrimitiveRequest) :
    (RegistrationNativeKemInterface.server (KemSK := KemSK) checks query).IsQueryBoundP (Counted kind)
      (if counted kind query.toRequest then 1 else 0) := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      cases kind <;> simp [RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other,
        RegistrationAgreementShared.PrimitiveRequest.toRequest, counted, Counted]
  | decapsulate ciphertext =>
      cases kind <;> simp [RegistrationNativeKemInterface.server,
        RegistrationAgreementShared.PrimitiveRequest.toRequest, counted]
  | encapsulate key =>
      cases key with
      | none => cases kind <;> simp [RegistrationNativeKemInterface.server,
          RegistrationAgreementShared.PrimitiveRequest.toRequest, counted]
      | some key =>
          by_cases admitted : checks.kemKey (RegistrationRootInput.pqKey key) = true
          · cases kind <;> simp [RegistrationNativeKemInterface.server, admitted,
              RegistrationNativeKemInterface.encapsulate, RegistrationAgreementShared.PrimitiveRequest.toRequest,
              counted, Counted]
          · cases kind <;> simp [RegistrationNativeKemInterface.server, admitted,
              RegistrationAgreementShared.PrimitiveRequest.toRequest, counted]

theorem beacon_step (kind : Kind) (handle : Option Nat)
    (query : RegistrationAgreementShared.PrimitiveRequest) :
    (RegistrationNativeKemInterface.beacon (KemSK := KemSK) handle query).IsQueryBoundP (Counted kind)
      (if counted kind query.toRequest then 1 else 0) := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      cases kind <;> simp [RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        RegistrationAgreementShared.PrimitiveRequest.toRequest, counted, Counted]
  | encapsulate key => cases kind <;> simp [RegistrationNativeKemInterface.beacon,
      RegistrationAgreementShared.PrimitiveRequest.toRequest, counted]
  | decapsulate ciphertext =>
      cases ciphertext <;> cases handle <;> cases kind <;>
        simp [RegistrationNativeKemInterface.beacon, RegistrationAgreementShared.PrimitiveRequest.toRequest,
          counted, Counted]

/-- Root HKDF is a pure selected functional callback; every other request uses the actual role interface. -/
def executor (backend : QueryImpl RegistrationAgreementShared.PrimitiveSpec (OracleComp (Spec OtherSpec KemSK)))
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize)) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec OtherSpec KemSK))
  | .convertPublic key => backend (.convertPublic key)
  | .convertSecret role => backend (.convertSecret role)
  | .generate role => backend (.generate role)
  | .encapsulate key => backend (.encapsulate key)
  | .decapsulate ciphertext => backend (.decapsulate ciphertext)
  | .dh request => backend (.dh request)
  | .root request => pure (root request)

private theorem executor_step (kind : Kind)
    (backend : QueryImpl RegistrationAgreementShared.PrimitiveSpec (OracleComp (Spec OtherSpec KemSK)))
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize))
    (bounded : ∀ query, (backend query).IsQueryBoundP (Counted kind)
      (if counted kind query.toRequest then 1 else 0)) (query : RegistrationAgreementExecutor.Request) :
    (executor backend root query).IsQueryBoundP (Counted kind) (if counted kind query then 1 else 0) := by
  cases query with
  | convertPublic key => exact bounded (.convertPublic key)
  | convertSecret role => exact bounded (.convertSecret role)
  | generate role => exact bounded (.generate role)
  | encapsulate key => exact bounded (.encapsulate key)
  | decapsulate ciphertext => exact bounded (.decapsulate ciphertext)
  | dh request => exact bounded (.dh request)
  | root request => trivial

private theorem program_bound (kind : Kind)
    (backend : QueryImpl RegistrationAgreementShared.PrimitiveSpec (OracleComp (Spec OtherSpec KemSK)))
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize))
    (bounded : ∀ query, (backend query).IsQueryBoundP (Counted kind)
      (if counted kind query.toRequest then 1 else 0))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (cap : Nat)
    (calls : work.IsQueryBoundP (counted kind) cap) :
    (simulateQ (executor backend root) work).IsQueryBoundP (Counted kind) cap := by
  apply IsQueryBoundP.simulateQ_of_step calls
  · intro query paid
    simpa only [ite_eq_left paid] using executor_step kind backend root bounded query
  · intro query free
    simpa only [ite_eq_right free] using executor_step kind backend root bounded query

theorem server_program (kind : Kind) (checks : PqxdhServerAuthExperiment.Checks)
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (cap : Nat)
    (calls : work.IsQueryBoundP (counted kind) cap) :
    (simulateQ (executor (RegistrationNativeKemInterface.server (KemSK := KemSK) checks) root) work).IsQueryBoundP
      (Counted kind) cap :=
  program_bound kind _ root (server_step kind checks) work cap calls

theorem beacon_program (kind : Kind) (handle : Option Nat)
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (cap : Nat)
    (calls : work.IsQueryBoundP (counted kind) cap) :
    (simulateQ (executor (RegistrationNativeKemInterface.beacon (KemSK := KemSK) handle) root) work).IsQueryBoundP
      (Counted kind) cap :=
  program_bound kind _ root (beacon_step kind handle) work cap calls

theorem server_one (kind : Kind) (checks : PqxdhServerAuthExperiment.Checks)
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize))
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (authenticated : registration.AuthenticatedInit) :
    (simulateQ (executor (RegistrationNativeKemInterface.server (KemSK := KemSK) checks) root)
      (RegistrationAgreementExecutor.server control status authenticated)).IsQueryBoundP (Counted kind) 1 :=
  server_program kind checks root _ 1 (RegistrationAgreementKemBounds.server kind control status authenticated)

theorem beacon_one (kind : Kind) (handle : Option Nat)
    (root : agreement.RootKdfRequest → Option (Std.Array U8 32#usize)) (authenticated : registration.AuthenticatedResponse) :
    (simulateQ (executor (RegistrationNativeKemInterface.beacon (KemSK := KemSK) handle) root)
      (RegistrationAgreementExecutor.beacon authenticated)).IsQueryBoundP (Counted kind) 1 :=
  beacon_program kind handle root _ 1 (RegistrationAgreementKemBounds.beacon kind authenticated)

end BeaconcryptCore.Computational.RegistrationNativeKemCallBounds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.server_one

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCallBounds.beacon_one
