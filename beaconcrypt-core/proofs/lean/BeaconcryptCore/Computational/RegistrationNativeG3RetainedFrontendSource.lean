-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedSource

/-! The source state for the original retained compiler contains the same actual generated-key pool, chronological signing receipts, selective service and World. Its explicit reassembly into the materialized native interpreter forgets only the unused root memo and the three billed accounting coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Frame (n : Nat) (KemSK ProviderState : Type) :=
  RegistrationNativeOpenRetainedSource.SourceState n KemSK ProviderState × RegistrationNativeSelectiveHiddenService.State n

def project (before : Frame n KemSK ProviderState) : RegistrationNativeG3LocalKeys.State n KemSK ProviderState :=
  ((⟨before.2.1, before.1.1.pool, before.1.2, before.1.1.receipts⟩, before.2.2), RegistrationNativeG3MetricWorld.mask before.1.1.world)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

noncomputable def handler : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (Frame n KemSK ProviderState) ProbComp) :=
  ((RegistrationNativeG3RetainedCallbacks.keys setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds).mapStateTBase
      (RegistrationNativeOpenRetainedSource.source setup wire route sign provider)).flattenStateT

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

/-- The actual native prepare callback preserves the exact original service result and full source frame. -/
theorem prepare_source (message : RegistrationNativeRelatedFamily.Message) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds (.inl (.inl message))).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds (.inl (.inl message))).run (project before) := by
  rcases before with ⟨ordinaryFrame, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [
    RegistrationNativeOpenRetainedSource.source, RegistrationNativeOpenRetainedSource.withBase,
    RegistrationNativePublicRetained.compiler, simulateQ_map, simulateQ_spec_query, RegistrationNativeG3MaterializedDirectFrontend.handler, RegistrationNativeG3MaterializedDirectFrontend.onKeys,
    project, RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys,
    StateT.run, state_lift_apply, state_map_apply, Functor.map_map, Prod.map_def, id_eq]

/-- The actual native demand callback preserves the exact original service result and full source frame. -/
theorem demand_source (message : RegistrationNativeRelatedFamily.Message) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds (.inl (.inr (.inl (.inl message))))).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds (.inl (.inr (.inl (.inl message))))).run (project before) := by
  rcases before with ⟨ordinaryFrame, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [
    RegistrationNativeOpenRetainedSource.source, RegistrationNativeOpenRetainedSource.withBase,
    RegistrationNativePublicRetained.compiler, simulateQ_map, simulateQ_spec_query, RegistrationNativeG3MaterializedDirectFrontend.handler, RegistrationNativeG3MaterializedDirectFrontend.onKeys,
    project, RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys,
    StateT.run, state_lift_apply, state_map_apply, Functor.map_map, Prod.map_def, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource.demand_source
