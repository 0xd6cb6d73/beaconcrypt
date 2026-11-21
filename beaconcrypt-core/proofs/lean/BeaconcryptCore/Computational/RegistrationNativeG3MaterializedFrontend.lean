-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler

/-! The finite material frontend separates the actual key-service state from chronological signing receipts and the full shared World. The same key service has no World access. Its known interpretation reconstructs hidden108 outputs from one fixed private seed table; its public interpretation retains only material44 references and materializes their later installation as the canonical known kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePairedServerService (Common PublicSpec publicCommon)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KeyState Value : Type}

abbrev ServiceSpec (n : Nat) := Message →ₒ Option (Choice n)
abbrev State (n : Nat) (KeyState : Type) := KeyState × RegistrationNativeG3Common.State n

def materialize (seeds : Seeds n) : Choice n → Choice n
  | .known output => .known output
  | .hidden reference => .known (PqxdhDeploymentHiddenLayout.joinOutput reference.material (seeds reference.slot))

def keys (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (ServiceSpec n) (StateT (State n KeyState) ProbComp) := fun message before =>
  (fun result => (result.1, (result.2, before.2))) <$> (service message).run before.1

def common (implementation : QueryImpl (Common n) (StateT (RegistrationNativeG3Common.State n) ProbComp)) :
    QueryImpl (Common n) (StateT (State n KeyState) ProbComp) := fun query before =>
  (fun result => (result.1, (before.1, result.2))) <$> (implementation query).run before.2

noncomputable def known (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (PublicSpec n) (StateT (State n KeyState) ProbComp)
  | .inl message => Option.map (materialize seeds) <$> keys service message
  | .inr query => common (RegistrationNativeG3Common.handler source writer sign) query

noncomputable def thin (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (PublicSpec n) (StateT (State n KeyState) ProbComp)
  | .inl message => keys service message
  | .inr query => common (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds) query

/-- A whole Common component preserves the exact key-service state while retaining every actual receipt and World update. -/
theorem common_program (implementation : QueryImpl (Common n) (StateT (RegistrationNativeG3Common.State n) ProbComp))
    (work : OracleComp (Common n) Value) (before : State n KeyState) :
    (simulateQ (common implementation) work).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (simulateQ implementation work).run before.2 := by
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation (common implementation)
    (fun current => (before.1, current)) (fun _ _ => rfl) work before.2).symm

/-- The known frontend runs an actual Common component against the same reached receipt/World state. -/
theorem known_common (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (work : OracleComp (Common n) Value) (before : State n KeyState) :
    (simulateQ (known source writer sign seeds service) (simulateQ publicCommon work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (simulateQ (RegistrationNativeG3Common.handler source writer sign) work).run before.2 := by
  rw [← QueryImpl.simulateQ_compose]
  have same : known source writer sign seeds service ∘ₛ publicCommon = common (RegistrationNativeG3Common.handler source writer sign) := by
    funext query
    simp only [QueryImpl.compose, publicCommon, simulateQ_spec_query, known]
  rw [same, common_program]

/-- The public frontend materializes the same complete Common state without consulting cache/use preconditions. -/
theorem thin_common (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (work : OracleComp (Common n) Value) (before : State n KeyState) :
    (simulateQ (thin source writer sign seeds service) (simulateQ publicCommon work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (simulateQ (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds) work).run before.2 := by
  rw [← QueryImpl.simulateQ_compose]
  have same : thin source writer sign seeds service ∘ₛ publicCommon =
      common (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds) := by
    funext query
    simp only [QueryImpl.compose, publicCommon, simulateQ_spec_query, thin]
  rw [same, common_program]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.common_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.known_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.known_common
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.thin_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend.thin_common
