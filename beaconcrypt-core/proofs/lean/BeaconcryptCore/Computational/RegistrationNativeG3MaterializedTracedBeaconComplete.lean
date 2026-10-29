-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish

/-! The actual typed Beacon completion emits its material/publication service directly. Its owner and local environment remain outside the private key/Common state. Lifting the finite material equation through this actual controller preserves terminal aborts, successful owner establishment and every reached local field. This direct Beacon path neither restores a captured environment nor identifies its receipt list with the separate private publication frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec State known thin)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {KemSK KeyState Auxiliary Value : Type}

noncomputable def paired (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (StateT (State n KeyState) ProbComp) :=
  if full then known source writer sign seeds service else thin source writer sign seeds service

noncomputable def localImpl (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp)) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp)
  | .inr (.inl query) => paired full source writer sign seeds service query
  | query => fallback query

/-- Every actual Beacon paired-service AST is interpreted literally against its current private state. -/
theorem public_program (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    simulateQ (localImpl full source writer sign seeds service fallback)
        (simulateQ RegistrationBeaconReferenceFinish.service work) =
      simulateQ (paired full source writer sign seeds service) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : localImpl full source writer sign seeds service fallback ∘ₛ RegistrationBeaconReferenceFinish.service =
      paired full source writer sign seeds service := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query, localImpl]
  rw [same]

/-- The actual native completion has the same full owner/environment/private poststate under known108 and materialized44 service interpretations, across every first-open or installation failure. -/
theorem complete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) (before : State n KeyState) :
    (simulateQ (localImpl true source writer sign seeds service fallback)
      (((RegistrationBeaconReferenceFinish.complete source owner ready).run current).run env)).run before =
      (simulateQ (localImpl false source writer sign seeds service fallback)
        (((RegistrationBeaconReferenceFinish.complete source owner ready).run current).run env)).run before := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, simulateQ_bind, public_program,
    StateT.run_bind, paired, ite_true]
  rw [RegistrationNativeG3MaterializedTracedBeaconFrontend.admitted source writer sign seeds service
    owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference before]
  apply bind_congr
  rintro ⟨completed, after⟩
  cases completed with
  | fail error => rfl
  | div => rfl
  | ok completed => cases completed <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete.public_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete.public_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete.complete
