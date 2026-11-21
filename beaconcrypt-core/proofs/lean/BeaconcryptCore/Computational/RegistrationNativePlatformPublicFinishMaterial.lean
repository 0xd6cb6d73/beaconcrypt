-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative
/-! Corrected incoming material demand uses the actual reached private memo. Its complete charged first-record, assigned-ID install and owner settlement run under the literal source callbacks, preserving all prior record markers and every private coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationBeaconReferenceNativeRecord (environment)
open RegistrationNativePlatformBeaconMaterialFrontend (chosen complete)
open RegistrationNativePlatformBeaconMaterialInterpreter (demand)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The literal corrected material branch uses only the actual stateful Env interpreter and retains the complete local environment. -/
theorem chosen_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState Auxiliary) (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((chosen setup.source wire.frameWrite effect owner ready choice).run current).run env)).run before =
      (simulateQ (trusted setup wire route sign seed scalar)
        (((chosen setup.source wire.frameWrite environment owner ready choice).run current).run env)).run before := by
  simp only [chosen, StateT.run, ← QueryImpl.simulateQ_compose]
  have same : implementation (n := n) setup wire route sign seed scalar ∘ₛ effect =
      trusted setup wire route sign seed scalar ∘ₛ environment := by
    funext query
    simp only [trusted, QueryImpl.apply_compose, environment, trustedLift, effect, simulateQ_spec_query]
  rw [same]

/-- A successful actual memo demand selects exactly the source-derived 108-byte material, with no initial-history restriction. -/
theorem complete_known (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState Auxiliary) (before : Private n KemSK) (prepared : before.extra.1 ready.reference = some root) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((complete setup.source wire.frameWrite effect demand owner ready).run current).run env)).run before =
      (simulateQ (trusted setup wire route sign seed scalar)
        (((RegistrationNativePlatformBeaconMaterialKnown.factored setup wire owner ready.descriptor root).run current).run env)).run before := by
  simp only [complete, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, simulateQ_spec_query, demand, bind_map_left]
  have same := RegistrationNativeOrdinaryFinishSourceMaterial.demand_run setup wire route sign seed scalar ready.reference before
  change (implementation setup wire route sign seed scalar (.inr (.inl (.inl ready.reference)))).run before = _ at same
  rw [same, prepared]
  simp only [Option.map_some, pure_bind]
  rw [chosen_source, RegistrationNativePlatformBeaconMaterialKnown.chosen_factored]

/-- Corrected aborts use the same actual World callback and preserve every private source field. -/
theorem abort_source {Value : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner source) (env : EnvState Auxiliary)
    (value : Value) (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect (RegistrationBeaconReferenceCompiler.eraseOwner owner) *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK)) Value).run
          (RegistrationBeaconReferenceCompiler.eraseOwner current)).run env)).run before =
      Prod.map RegistrationNativePlatformBeaconContinuation.view id <$>
        (simulateQ (trusted setup wire route sign seed scalar)
          (((RegistrationNativePlatformBeaconOwner.abort owner *> pure value :
            RegistrationNativePlatformBeaconOwner.M n KemSK Auxiliary source Value).run current).run env)).run before := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, RegistrationNativePlatformBeaconOwner.abort,
    seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, trusted, QueryImpl.apply_compose, trustedLift, effect,
    Functor.map_map, RegistrationNativePlatformBeaconContinuation.view, Prod.map_def, id_eq]
  rfl

/-- Missing actual preparation aborts before any source initial-record work. -/
theorem complete_missing (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) (before : Private n KemSK)
    (missing : before.extra.1 ready.reference = none) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((complete setup.source wire.frameWrite effect demand owner ready).run current).run env)).run before =
      (simulateQ (implementation setup wire route sign seed scalar)
        (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.ok none) :
          RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK))
            (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  simp only [complete, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, simulateQ_spec_query, demand, bind_map_left]
  have same := RegistrationNativeOrdinaryFinishSourceMaterial.demand_run setup wire route sign seed scalar ready.reference before
  change (implementation setup wire route sign seed scalar (.inr (.inl (.inl ready.reference)))).run before = _ at same
  rw [same, missing]
  simp only [Option.map_none, pure_bind]

/-- The memo-backed corrected public first-record continuation is the actual consumed-kernel source continuation, retaining every prior marker and private source field. -/
theorem complete_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState Auxiliary) (before : Private n KemSK) (prepared : before.extra.1 ready.reference = some root)
    (erased : Std.Array U8 227#usize) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((complete setup.source wire.frameWrite effect demand (RegistrationBeaconReferenceCompiler.eraseOwner owner) ready).run
        (RegistrationBeaconReferenceCompiler.eraseOwner current)).run env)).run before =
      Prod.map RegistrationNativePlatformBeaconContinuation.view id <$>
        (simulateQ (trusted setup wire route sign seed scalar)
          (((RegistrationNativePlatformBeaconMaterialKnown.postRoot setup wire owner
            (RegistrationBeaconReferenceRoot.atRoot ready root)).run current).run env)).run before := by
  rw [complete_known setup wire route sign seed scalar _ _ ready root env before prepared]
  have body :=  RegistrationNativePlatformBeaconMaterialKnown.post_root (n := n) setup wire erased owner current ready.descriptor root env
  have actual := congrArg (fun tree => (simulateQ (trusted setup wire route sign seed scalar) tree).run before) body
  convert actual.symm using 1; simp only [simulateQ_map, StateT.run_map, RegistrationNativePlatformBeaconContinuation.view, Prod.map_def, id_eq]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.chosen_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial.complete_source
