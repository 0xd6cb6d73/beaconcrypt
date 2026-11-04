-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconProgram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
/-! The literal corrected Beacon material demand and assigned-ID completion have one free known/opaque source equation. Authentication and root preparation are compared through their derived actual query footprint, while materialization only changes the private install reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (Spec SelectedOwner effect)
open RegistrationNativePlatformMaterializedBeacon (realize)
variable {n : Nat} {KemSK Auxiliary A : Type} {mlSource : RegistrationNativeMldsa.Source}

noncomputable def translate (full : Bool) (seeds : Seeds n) : QueryImpl (Spec n KemSK) (OracleComp (Spec n KemSK))
  | .inr (.inl (.inl message)) => if full then
      Option.map (RegistrationNativeG3MaterializedFrontend.materialize seeds) <$> (Spec n KemSK).query (.inr (.inl (.inl message)))
    else (Spec n KemSK).query (.inr (.inl (.inl message)))
  | .inr (.inl (.inr (.inr query))) => if full then
      (Spec n KemSK).query (.inr (.inl (.inr (.inr query))))
    else simulateQ effect (realize seeds query)
  | query => (Spec n KemSK).query query

private theorem effects_true (seeds : Seeds n) (work : OracleComp (EnvEffects n) A) :
    simulateQ (translate (KemSK := KemSK) true seeds) (simulateQ effect work) = simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : translate (KemSK := KemSK) true seeds ∘ₛ effect = effect := by
    funext query
    simp only [QueryImpl.apply_compose, effect, simulateQ_spec_query, translate, ite_true]
  rw [same]

private theorem effects_false (seeds : Seeds n) (work : OracleComp (EnvEffects n) A) :
    simulateQ (translate (KemSK := KemSK) false seeds) (simulateQ effect work) =
      simulateQ effect (simulateQ (realize seeds) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, effect, simulateQ_spec_query, translate, Bool.false_eq_true, ite_false]

private theorem chosen_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (seeds : Seeds n) (env : EnvState Auxiliary) :
    simulateQ (translate (KemSK := KemSK) true seeds)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen source writer effect owner ready
        (RegistrationNativeG3MaterializedFrontend.materialize seeds choice)).run current).run env) =
      simulateQ (translate (KemSK := KemSK) false seeds)
        (((RegistrationNativePlatformBeaconMaterialFrontend.chosen source writer effect owner ready choice).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.chosen, StateT.run, effects_true, effects_false]
  exact congrArg (simulateQ (effect (KemSK := KemSK)))
    (RegistrationNativePlatformMaterializedBeaconProgram.program_source source writer owner current ready choice seeds env)

private theorem abort_source (seeds : Seeds n) (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary) :
    simulateQ (translate (KemSK := KemSK) true seeds)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner).run current).run env) =
      simulateQ (translate (KemSK := KemSK) false seeds)
        (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, StateT.run_map,
    bind_pure_comp, simulateQ_map, effect, simulateQ_spec_query, translate, ite_true, Bool.false_eq_true, ite_false,
    realize]

/-- The actual one-demand continuation has the same returned owner, full local environment and all failure branches under either private seed interpretation. -/
theorem complete_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready)
    (seeds : Seeds n) (env : EnvState Auxiliary) :
    simulateQ (translate (KemSK := KemSK) true seeds)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete source writer effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) =
      simulateQ (translate (KemSK := KemSK) false seeds)
        (((RegistrationNativePlatformBeaconMaterialFrontend.complete source writer effect
          RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, bind_map_left, RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    simulateQ_spec_query, translate, ite_true, Bool.false_eq_true, ite_false]
  apply bind_congr
  intro chosen
  cases chosen with
  | none =>
      simp only [Option.map_none, seqRight_eq_bind, StateT.run_map,
        bind_pure_comp, simulateQ_map, abort_source]
  | some choice =>
      simp only [Option.map_some]
      exact chosen_source source writer owner current ready choice seeds env
private theorem query_free (full : Bool) (seeds : Seeds n) (query : (Spec n KemSK).Domain)
    (compatible : RegistrationNativeG3MaterializedBeaconPrefix.Compatible query) :
    translate full seeds query = (Spec n KemSK).query query := by
  rcases query with message | ((message | (query | query)) | query)
  · rfl
  · exact compatible.elim
  · rfl
  · cases full with
    | true => rfl
    | false =>
      cases query with
      | inl coin => rfl
      | inr capability =>
          cases capability <;> try rfl
          case installServer keyId binding kernel =>
            cases kernel with
            | known kernel => rfl
            | hidden slot => exact (compatible trivial).elim
          case installBeacon owner shell kernel =>
            cases kernel with
            | known kernel => rfl
            | hidden slot => exact (compatible trivial).elim
  · rfl
private theorem program_free (full : Bool) (seeds : Seeds n) (work : OracleComp (Spec n KemSK) A)
    (compatible : work.AllQueriesSatisfy (RegistrationNativeG3MaterializedBeaconPrefix.Compatible (n := n) (KemSK := KemSK))) :
    simulateQ (translate full seeds) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp compatible
      simp only [simulateQ_bind, simulateQ_spec_query, query_free full seeds query allowed]
      congr 1
      funext reply
      exact ih reply (later reply)

/-- The literal response authentication and native agreement/preparation prefix is unchanged, by its actual checked finite query footprint. -/
theorem preparation_source {I : Type} {base : OracleSpec I}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (seeds : Seeds n) (env : EnvState Auxiliary) :
    simulateQ (translate true seeds)
      (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run env) =
      simulateQ (translate false seeds)
        (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run env) :=
  (program_free true seeds _ (RegistrationNativeG3MaterializedBeaconPrefix.preparation_compatible setup source packet owner env)).trans
    (program_free false seeds _ (RegistrationNativeG3MaterializedBeaconPrefix.preparation_compatible setup source packet owner env)).symm

/-- Every post-preparation failure and successful assigned-ID completion retains the same full source state under materialization. -/
theorem afterPrepared_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner mlSource) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (seeds : Seeds n) (env : EnvState Auxiliary) :
    simulateQ (translate (KemSK := KemSK) true seeds)
      (((RegistrationNativePlatformBeaconContinuation.afterPrepared source writer owner result).run current).run env) =
      simulateQ (translate (KemSK := KemSK) false seeds)
        (((RegistrationNativePlatformBeaconContinuation.afterPrepared source writer owner result).run current).run env) := by
  cases result with
  | fail error | div =>
      simp only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind,
        StateT.run_map, bind_pure_comp, simulateQ_map, abort_source]
  | ok ready => cases ready with
    | none =>
      simp only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind,
        StateT.run_map, bind_pure_comp, simulateQ_map, abort_source]
    | some ready => exact complete_source source writer owner current ready seeds env
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.preparation_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend.afterPrepared_source
