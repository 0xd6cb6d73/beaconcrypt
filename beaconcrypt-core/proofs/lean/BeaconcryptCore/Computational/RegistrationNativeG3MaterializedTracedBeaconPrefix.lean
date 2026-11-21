-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown

/-! The actual installation-free Beacon prefix has the same complete chronological source under known and materialized hidden outputs. Its existing derived footprint is reused without a new caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconPrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeG3KnownWorldFrameCommon (EffectAllowed)
open RegistrationNativeG3MaterializedTracedBeaconComplete (localImpl paired)
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec State)
open RegistrationNativeG3MaterializedBeaconPrefix (Compatible)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
private theorem query_same (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (query : (Spec n KemSK).Domain) (quiet : Compatible (KemSK := KemSK) query) :
    localImpl true source writer sign seeds service fallback query = localImpl false source writer sign seeds service fallback query := by
  rcases query with message | ((message | (query | query)) | query)
  · rfl
  · exact quiet.elim
  · rfl
  · simp only [localImpl, paired, Bool.false_eq_true, ite_true, ite_false, RegistrationNativeG3MaterializedTracedServerFrontend.known,
      RegistrationNativeG3MaterializedTracedServerFrontend.thin, ]
    apply StateT.ext
    intro before
    change (fun result => (result.1, (before.1, result.2))) <$> (RegistrationNativeG3MaterializedTracedServerCommon.effect true seeds query).run before.2 =
      (fun result => (result.1, (before.1, result.2))) <$> (RegistrationNativeG3MaterializedTracedServerCommon.effect false seeds query).run before.2
    rw [RegistrationNativeG3MaterializedTracedServerKnown.effect_unchanged seeds query quiet]
  · rfl

private theorem program_same (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (work : OracleComp (Spec n KemSK) Value) (quiet : AllQueriesSatisfy work (Compatible (KemSK := KemSK))) :
    simulateQ (localImpl true source writer sign seeds service fallback) work =
      simulateQ (localImpl false source writer sign seeds service fallback) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [query_same source writer sign seeds service fallback query allowed]
      congr 1
      funext reply
      exact ih reply (later reply)

/-- The whole actual native preparation prefix retains its exact full owner/environment/private result under both material interpretations, without a caller-supplied source or footprint condition. -/
theorem preparation_source (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (env : EnvState Auxiliary) :
    simulateQ (localImpl true setup.source writer sign seeds service fallback)
        (((finishPreparation setup mlSource packet).run owner).run env) =
      simulateQ (localImpl false setup.source writer sign seeds service fallback)
        (((finishPreparation setup mlSource packet).run owner).run env) :=
  program_same setup.source writer sign seeds service fallback _ (RegistrationNativeG3MaterializedBeaconPrefix.preparation_compatible setup mlSource packet owner env)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconPrefix.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconPrefix.preparation_source
