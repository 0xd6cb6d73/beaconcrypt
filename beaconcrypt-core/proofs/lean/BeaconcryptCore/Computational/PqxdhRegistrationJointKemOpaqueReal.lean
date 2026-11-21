-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueClient

/-! Interpret the same private-marker source client with the actual fixed HKDF, retaining the complete primitive history/cache and all original auxiliary callbacks. The equation does not replace the existing initialized scheduler's restricted-ROM backend or assert Extract security. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal
open PqxdhRegistrationJointKemOpaqueSuffix PqxdhRegistrationJointKemOpaqueClient
open PqxdhServerRelatedRootConsumer PqxdhSecretInputKdf
variable {Reader A : Type}

/-- Real primitive interpretation is local to the private service; neither input bytes nor PRK/history are returned to its caller. The full private state remains retained. -/
def root (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader) :
    StateT (State A) ProbComp RootOutput := fun state =>
  pure (PqxdhJointDhExtractRoot.nativeRoot source (bytes candidate input),
    (PqxdhJointDhExtractRoot.rootState hmac (nativeMessage (materialize candidate input))
      (bytes candidate input) state.1, state.2))

/-- On the source's actual accepted branch, the real root service preserves its complete native callback state and exact returned root. -/
theorem root_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (control final : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (original : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) =
      ok (.Ok (final, original))) :
    root (A := A) source hmac candidate input =
      nativeRoot source hmac (materialize candidate input) original := by
  unfold root PqxdhServerRelatedRootConsumer.nativeRoot
  rw [accepted_bytes candidate input control final binding original accepted]

/-- The same source erasure and consumption handlers accompany the fixed real root interpreter. -/
def impl (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (aux : QueryImpl AuxSpec (StateT A ProbComp)) :
    QueryImpl (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) (StateT (State A) ProbComp)
  | .inl input => root source hmac candidate input
  | .inr query => auxImpl aux query

/-- Every source acceptance outcome and optional return agrees with the existing real-HKDF source consumer. All auxiliary callbacks and the entire private state survive unchanged. -/
theorem client_source (kdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Reader)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) :
    simulateQ (impl kdf hmac candidate aux) (PqxdhRegistrationJointKemOpaqueClient.client control binding input) =
      PqxdhServerRelatedRootConsumer.source kdf hmac aux control binding (materialize candidate input) := by
  simp only [PqxdhRegistrationJointKemOpaqueClient.client,
    PqxdhRegistrationJointKemOpaqueCore.accept_native control binding input candidate,
    PqxdhRegistrationJointKemOpaqueCore.clearedAccept, PqxdhServerRelatedRootConsumer.source]
  cases accepted : PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) with
  | fail error =>
      simp only [simulateQ_bind, simulateQ_spec_query, impl, simulateQ_pure]
      rfl
  | div =>
      simp only [simulateQ_bind, simulateQ_spec_query, impl, simulateQ_pure]
      rfl
  | ok result =>
      cases result with
      | Err error =>
          simp only [simulateQ_bind, simulateQ_spec_query, impl, simulateQ_pure]
          rfl
      | Ok pair =>
          rcases pair with ⟨final, original⟩
          simp only [simulateQ_bind, simulateQ_spec_query, impl, simulateQ_pure,
            root_source kdf hmac candidate input control final binding original accepted,
            PqxdhServerClearedRoot.cleared]
          rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal.root_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueReal.client_source
