-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
/-! The entire corrected selected/ordinary incoming reference body executes the actual source authentication, unchanged agreement and corrected assigned-ID first-record/install controller. Prior record markers and every reached private source coordinate are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishLocal
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (drop)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (eraseOwner Spec effect)
open RegistrationNativePlatformBeaconContinuation (view)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem state_bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_lift_apply {m : Type → Type} [Monad m] {S A : Type}
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_pure_apply {m : Type → Type} [Monad m] {S A : Type}
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem adapt_effects (setup : Setup base KemSK) (localScalar : Option ScalarBytes)
    (work : OracleComp (EnvEffects n) Value) :
    simulateQ (adapt setup localScalar) (simulateQ (effect (KemSK := KemSK)) work) = simulateQ effect work := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar => exact RegistrationNativeOrdinaryFinishSourceWrapper.effects_program setup scalar work

private theorem effects_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (work : OracleComp (EnvEffects n) Value) (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed selectedScalar)
      (simulateQ (adapt setup localScalar) (simulateQ effect work))).run before =
      (simulateQ (trusted setup wire route sign seed selectedScalar)
        (simulateQ RegistrationBeaconReferenceNativeRecord.environment work)).run before := by
  rw [adapt_effects, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 2
  funext query
  simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.trustedLift]

private theorem abort_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (value : Value) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect (eraseOwner owner) *> pure value :
            RegistrationNativePlatformBeaconMaterialFrontend.M mlSource RegistrationServerRoleBackend.State (OracleComp (Spec n KemSK)) Value).run
              (eraseOwner current)).run env))).run before =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((RegistrationNativePlatformBeaconOwner.abort owner *> pure value :
            RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource Value).run current).run env)).run before := by
  rw [RegistrationNativePlatformPublicFinishAdapt.abort]
  have compared := congrArg (fun action => Prod.map id drop <$> action)
    (RegistrationNativePlatformPublicFinishMaterial.abort_source setup wire route sign seed selectedScalar owner current env value before)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using compared

/-- Complete incoming execution is the actual native owner controller, retaining original authentication, failures, state consumption, first opening and installation. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (packet : Option registration.ResponsePacket)
    (sameScalar : owner.prekeyScalar = localScalar.getD selectedScalar)
    (coherent : ∀ pending oneTime, owner.phase = .initSent pending oneTime →
      pending.control.expected_server_binding = pending.binding.server_pin.binding)
    (env : EnvState RegistrationServerRoleBackend.State)
    (erased : Std.Array U8 227#usize) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire mlSource packet :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner owner)).run env))).run before =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((RegistrationNativePlatformBeaconOwner.finish setup mlSource wire packet :
            RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before := by
  have phaseView : (eraseOwner owner).phase = owner.phase := rfl
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, RegistrationNativePlatformBeaconOwner.finish,
        StateT.run_bind, StateT.run_get, pure_bind, phaseView, phase, StateT.run_pure,
        simulateQ_pure, map_pure, Prod.map_def, id_eq, view]
  | initSent pending oneTime =>
      simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, RegistrationNativePlatformBeaconOwner.finish,
        StateT.run_bind, StateT.run_get, pure_bind, phaseView, phase]
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq, view]
      | ok aborted =>
          simp only [StateT.run_modify, pure_bind, StateT.run_bind, StateT.run_lift,
            bind_pure_comp, simulateQ_bind, map_bind, bind_map_left,
            RegistrationBeaconReferenceNativeOwner.authentication]
          rw [effects_source]
          apply bind_congr_of_forall_mem_support
          rintro ⟨authenticated, afterPrivate⟩ supported
          cases authenticated with
          | fail error | div =>
              exact abort_source setup wire route sign seed selectedScalar localScalar owner
                { owner with phase := .aborted aborted } env _ afterPrivate
          | ok result => cases result with
            | Err error =>
                exact abort_source setup wire route sign seed selectedScalar localScalar owner
                  { owner with phase := .aborted aborted } env _ afterPrivate
            | Ok accepted =>
                have retained : RegistrationBeaconResponseMetadata.Retained pending accepted := by
                  cases packet with
                  | none =>
                      apply RegistrationBeaconResponseMetadata.simulated_metadata
                        (trusted setup wire route sign seed selectedScalar ∘ₛ
                          (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ
                            RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify))
                        pending .None accepted before afterPrivate
                      simpa only [QueryImpl.simulateQ_compose] using supported
                  | some value =>
                      apply RegistrationBeaconResponseMetadata.simulated_metadata
                        (trusted setup wire route sign seed selectedScalar ∘ₛ
                          (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ
                            RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify))
                        pending (.Some value) accepted before afterPrivate
                      simpa only [QueryImpl.simulateQ_compose] using supported
                have correct : accepted.control.expected_server_binding = accepted.binding.server_pin.binding := by
                  rw [retained.1, retained.2.1]
                  exact coherent pending oneTime phase
                have actual := RegistrationNativePlatformPublicFinishPhase.phase_native setup wire route sign seed selectedScalar localScalar
                  owner { owner with phase := .aborted aborted } oneTime accepted correct env erased afterPrivate
                rw [← RegistrationBeaconReferenceGenericCallbacks.lower_program] at actual
                simp only [RegistrationBeaconReferenceGenericStage.lower,
                  simulateQ_bind, StateT.run, state_bind_apply, state_lift_apply, state_pure_apply,
                  pure_bind, bind_assoc, sameScalar,
                  map_bind, bind_map_left, RegistrationNativePlatformBeaconContinuation.sourceAfter,
                  RegistrationNativePlatformBeaconMaterialKnown.postRoot] at actual ⊢
                convert actual using 1; rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishLocal.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishLocal.finish_source
