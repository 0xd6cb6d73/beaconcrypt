-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage

/-! Collection followed by one private native root step retains the complete ordinary interpreter state. This algebraic factorization is shared by selected and materialized ordinary owners; neither source branch assumes an owner pin equals the selected Server identity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationBeaconReferenceGenericStage (Local lower primitive liftCache)
variable {ι KemSK Value Auxiliary Private : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Plain (Auxiliary Private : Type) := RegistrationNativeRelatedFamily.State × Local Auxiliary Private

def dropCache : RegistrationNativeBeaconRootSource.State (Local Auxiliary Private) → Plain Auxiliary Private :=
  fun state => (state.1, state.2.1)

noncomputable def prefixHandler (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    QueryImpl (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse)
      (StateT (Plain Auxiliary Private) ProbComp) := fun query before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (lower (Auxiliary := Auxiliary) setup trusted
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.trustedBackend setup owner oneTime) authenticated)
        RegistrationBeaconReferenceCompiler.trustedVisit query)).run before.2

private theorem lifted_run {Auxiliary : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value)
    (before : RegistrationNativeBeaconRootSource.State Auxiliary) :
    (RegistrationNativeBeaconRootSource.lift work).run before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := rfl

private theorem cache_run {Auxiliary : Type} (work : StateT Auxiliary ProbComp Value)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (liftCache work).run before = (fun result => (result.1, (result.2, before.2))) <$> work.run before.1 := rfl

private theorem lower_run (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local Auxiliary Private) :
    (lower (Auxiliary := Auxiliary) setup trusted work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (trusted)
          (work.run before.1)).run before.2 := rfl

private theorem prefix_query (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : RegistrationNativeBeaconRootSource.State (Local Auxiliary Private)) :
    Prod.map id dropCache <$>
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl
          (fun request => RegistrationNativeBeaconRootSource.lift
            (RegistrationAgreementShared.implementation setup.source
              (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime) request)) authenticated)
        (fun point => RegistrationNativeBeaconRootSource.lift
          (liftCache (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point)))) query).run before =
      (prefixHandler setup trusted owner oneTime authenticated query).run (dropCache before) := by
  unfold prefixHandler
  cases query <;>
    simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl,
      RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query,
      ← RegistrationBeaconReferenceGenericStage.backend_shared,
      lifted_run, cache_run, lower_run,
    RegistrationBeaconReferenceSource.backend, RegistrationBeaconReferenceSource.visit,
    RegistrationBeaconReferenceCompiler.trustedVisit, StateT.run_map,
    StateT.run_pure, StateT.run_modify, simulateQ_map, simulateQ_pure,
      bind_pure_comp, map_pure, Functor.map_map, Prod.map_def, id_eq, dropCache]
  all_goals rfl

def family (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
    (StateT RegistrationNativeRelatedFamily.State ProbComp)) :
    QueryImpl RegistrationNativeRelatedRoot.RootSpec (StateT (Plain Auxiliary Private) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2, before.2))) <$> (implementation query).run before.1

private theorem family_program
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (work : OracleComp RegistrationNativeRelatedRoot.RootSpec Value)
    (before : RegistrationNativeBeaconRootSource.State (Local Auxiliary Private)) :
    Prod.map id dropCache <$>
      (simulateQ (RegistrationNativeBeaconRootSource.familyImpl implementation) work).run before =
      (simulateQ (family implementation) work).run (dropCache before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeBeaconRootSource.familyImpl, family, StateT.run,
    Functor.map_map, Prod.map_def, id_eq, dropCache]

noncomputable def stage (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse) :
    StateT (Plain Auxiliary Private) ProbComp (RustM agreement.AgreementEffect) := do
  let pending ← simulateQ (prefixHandler setup trusted owner oneTime authenticated)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])
  match pending with
  | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated))
  | some pending => simulateQ (family implementation) (RegistrationNativeBeaconRootSource.client authenticated pending)

/-- Removing the unused cache frame commutes with the complete actual public collection and private root step. -/
theorem stage_project (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (before : RegistrationNativeBeaconRootSource.State (Local Auxiliary Private)) :
    Prod.map id dropCache <$>
      (RegistrationNativeBeaconRootStage.stage setup.beaconDomain
        (RegistrationAgreementShared.implementation setup.source (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime))
        (fun point => liftCache (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point)))
        implementation authenticated).run before =
      (stage setup trusted owner oneTime implementation authenticated).run (dropCache before) := by
  have collected := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ dropCache
    (prefix_query setup trusted owner oneTime authenticated)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) before
  simp only [RegistrationNativeBeaconRootStage.stage, stage, StateT.run_bind, map_bind]
  rw [← collected, bind_map_left]
  apply bind_congr
  rintro ⟨pending, reached⟩
  cases pending with
  | none => simp only [StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | some pending => exact family_program implementation _ reached

/-- The native arbitrary-pin descriptor phase reconstructs the complete actual agreement controller on the full reached World and private KEM pool. -/
theorem stage_native (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (before : Plain Auxiliary Private) :
    Prod.map id Prod.snd <$>
      (stage setup trusted owner oneTime
        (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed scalar)
        authenticated).run before =
      (simulateQ (RegistrationBeaconReferenceGenericStage.native setup trusted scalar owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2 := by
  have projected := congrArg (fun work => Prod.map id Prod.snd <$> work)
    (stage_project setup trusted owner oneTime
      (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed scalar)
      authenticated (before.1, (before.2, ∅)))
  have actual := RegistrationBeaconReferenceGenericStage.stage_native setup trusted seed scalar
    owner oneTime authenticated coherent (before.1, (before.2, ∅))
  simp only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def, dropCache] at projected actual ⊢
  exact projected.symm.trans actual

theorem framed_collect (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Plain Auxiliary Private) :
    (simulateQ (prefixHandler setup trusted owner oneTime authenticated)
      (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (lower (Auxiliary := Auxiliary) setup trusted
          (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run before.2 := by
  let embed : Local Auxiliary Private → Plain Auxiliary Private := fun current => (before.1, current)
  have framed := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => lower (Auxiliary := Auxiliary) setup trusted
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.trustedBackend setup owner oneTime) authenticated)
        RegistrationBeaconReferenceCompiler.trustedVisit query))
    (prefixHandler setup trusted owner oneTime authenticated) embed
    (fun _ _ => rfl) (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) before.2
  rw [← RegistrationBeaconReferenceGenericStage.lower_program] at framed
  simpa only [RegistrationBeaconReferenceCompiler.trustedCollect, embed, Prod.map_def, id_eq] using framed.symm

theorem family_only
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (work : OracleComp RegistrationNativeRelatedRoot.RootSpec Value) (before : Plain Auxiliary Private) :
    (simulateQ (family implementation) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$> (simulateQ implementation work).run before.1 := by
  let embed : RegistrationNativeRelatedFamily.State → Plain Auxiliary Private := fun current => (current, before.2)
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation (family implementation) embed
      (fun _ _ => rfl) work before.1).symm


/-- The stage issues the literal shared collection program before its sole native private-root continuation. -/
theorem stage_run (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse) (before : Plain Auxiliary Private) :
    (stage setup trusted owner oneTime implementation authenticated).run before = (do
      let reached ← (lower setup trusted
        (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run before.2
      match reached.1 with
      | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated), (before.1, reached.2))
      | some pending => (fun result => (result.1, (result.2, reached.2))) <$>
          (simulateQ implementation (RegistrationNativeBeaconRootSource.client authenticated pending)).run before.1) := by
  simp only [stage, StateT.run_bind, framed_collect, bind_map_left]
  apply bind_congr
  rintro ⟨pending, reached⟩
  cases pending with
  | none => rfl
  | some pending => exact family_only implementation _ _

end BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.framed_collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.framed_collect

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.family_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.family_only

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericAgreement.stage_run
