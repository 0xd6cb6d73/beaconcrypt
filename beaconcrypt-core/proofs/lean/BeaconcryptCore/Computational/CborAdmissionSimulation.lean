-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionSubstitution
import BeaconcryptCore.Computational.CborAdmissionSend
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! CBOR rejection has an exact implementation by empty native commands beneath the secrecy ledger. The admission decision still reads the native state internally; this operational simulation does not supply the public-control adversary compiler or transport a cryptographic headline. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionSimulation
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open CborProductionBoundary (NativeFrame baseHandler allowed reject)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

/-- Each fallback keeps the command's class and addressed handle; registration still moves its pending token. -/
noncomputable def emptyHandler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp)
  | .inr (.build session _) => baseHandler setup wire parse checks seed (.inr (.build session (some [])))
  | .inr (.serverSend keyId _) => baseHandler setup wire parse checks seed (.inr (.serverSend keyId []))
  | .inr (.beaconSend index _) => baseHandler setup wire parse checks seed (.inr (.beaconSend index []))
  | query => baseHandler setup wire parse checks seed query

/-- Admission chooses a real command at the same complete native state, before any record primitive. -/
noncomputable def replacementHandler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  fun query state => if allowed query state then (baseHandler setup wire parse checks seed query).run state
    else (emptyHandler setup wire parse checks seed query).run state

theorem base_build_empty (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    (baseHandler setup wire parse checks seed (.inr (.build session (some [])))).run state =
      pure (none, CborProductionBoundary.consumePending session state) := by
  unfold baseHandler CborCommandFilter.atState
  simp_rw [CborAdmissionSubstitution.deployment_build_empty]
  rfl

theorem base_server_empty (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (keyId : Std.U64) (state : PqxdhDeploymentNative.State KemSK) :
    (baseHandler setup wire parse checks seed (.inr (.serverSend keyId []))).run state = pure (none, state) := by
  unfold baseHandler CborCommandFilter.atState
  simp_rw [CborAdmissionSend.server_empty]
  rfl

theorem base_beacon_empty (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    (baseHandler setup wire parse checks seed (.inr (.beaconSend index []))).run state = pure (none, state) := by
  unfold baseHandler CborCommandFilter.atState
  simp_rw [CborAdmissionSend.beacon_empty]
  rfl

/-- Every genuinely blocked command has exactly its specified complete rejection effect. -/
theorem empty_reject (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (blocked : allowed query state = false) :
    (emptyHandler setup wire parse checks seed query).run state = pure (reject query state) := by
  cases query with
  | inl coin => simp only [allowed, Bool.true_eq_false] at blocked
  | inr command =>
    cases command <;> try simp only [allowed, Bool.true_eq_false] at blocked
    case build session payload =>
      simpa only [emptyHandler, reject] using base_build_empty setup wire parse checks seed session state
    case serverSend keyId plaintext =>
      simpa only [emptyHandler, reject] using base_server_empty setup wire parse checks seed keyId state
    case beaconSend index plaintext =>
      simpa only [emptyHandler, reject] using base_beacon_empty setup wire parse checks seed index state

/-- A concrete fallback equation removes synthetic rejection without changing either admitted branch. -/
theorem substitute_exact {κ State : Type} {spec : OracleSpec κ}
    (allow : spec.Domain → State → Bool)
    (rejection : (query : spec.Domain) → State → spec.Range query × State)
    (implementation fallback : QueryImpl spec (StateT State ProbComp))
    (fallbackExact : ∀ query state, allow query state = false →
      (fallback query).run state = pure (rejection query state)) :
    CborCommandFilter.handler allow rejection implementation =
      (fun query state => if allow query state then (implementation query).run state
        else (fallback query).run state) := by
  funext query state
  cases admitted : allow query state <;>
    simp only [CborCommandFilter.handler,
      StateT.run, admitted, Bool.false_eq_true, ite_false, ite_true]
  exact (fallbackExact query state admitted).symm

/-- The filtered production handler equals native execution with the exact empty substitutions. -/
theorem handler_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    CborProductionBoundary.handler setup wire parse checks seed = replacementHandler setup wire parse checks seed :=
  substitute_exact allowed reject (baseHandler setup wire parse checks seed) (emptyHandler setup wire parse checks seed)
    (empty_reject setup wire parse checks seed)

/-- Every adaptive native-interface client keeps its output and complete final native state. -/
theorem adaptive_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp Spec X) (state : PqxdhDeploymentNative.State KemSK) :
    (simulateQ (CborProductionBoundary.handler setup wire parse checks seed) work).run state =
      (simulateQ (replacementHandler setup wire parse checks seed) work).run state := by
  rw [handler_exact]

/-- The unchanged secrecy ledger runs above substitution, retaining original queries, hidden draws and every transcript position. -/
theorem ledger_adaptive_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp PqxdhDeploymentInterface.FullSpec X) (state : PqxdhDeploymentSecrecy.State KemSK) :
    (simulateQ (((CborProductionBoundary.handler setup wire parse checks seed).mapStateTBase
      (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto wire setup.serverKeyId bounds)).flattenStateT) work).run state =
      (simulateQ (((replacementHandler setup wire parse checks seed).mapStateTBase
        (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto wire setup.serverKeyId bounds)).flattenStateT) work).run state := by
  rw [handler_exact]

end BeaconcryptCore.Computational.CborAdmissionSimulation

/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.base_build_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.base_build_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.base_server_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.base_server_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.base_beacon_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.base_beacon_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.empty_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.empty_reject
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.substitute_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.substitute_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.handler_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.handler_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.adaptive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.adaptive_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSimulation.ledger_adaptive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSimulation.ledger_adaptive_exact
