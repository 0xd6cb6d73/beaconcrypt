-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPhase
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeFinish

/-! The complete selected/ordinary incoming controller runs the actual response verifier, native root preparation and first-record completion. Ordinary preparation retains the translated return name. The source comparison names only the already derived private-memo, owner-scalar and record-request analysis projections. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState)
open RegistrationNativeProviderCallbacks (implementation)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeProviderBeaconPreparation (drop)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (eraseOwner Spec effect)
open RegistrationBeaconReferenceNativeContinuation (view)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

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
    (provider : Provider KemSK ProviderState)
    (work : OracleComp (EnvEffects n) Value) (before : NativeState n KemSK ProviderState) :
    (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
      (simulateQ (adapt setup localScalar) (simulateQ effect work))).run before =
      (simulateQ (trusted setup wire route sign seed selectedScalar provider)
        (simulateQ RegistrationBeaconReferenceNativeRecord.environment work)).run before := by
  rw [adapt_effects, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 2
  funext query
  simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.trustedLift]

private theorem adapt_abort (setup : Setup base KemSK) (localScalar : Option ScalarBytes)
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (env : EnvState RegistrationServerRoleBackend.State) (value : Value) :
    simulateQ (adapt setup localScalar)
      (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
          mlSource Value).run current).run env) =
      (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
          mlSource Value).run current).run env) := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar =>
      simp only [adapt, RegistrationBeaconReferenceFinish.abort, seqRight_eq_bind,
        StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map, effect,
        simulateQ_spec_query, RegistrationNativePublicOwners.ordinary]

private theorem abort_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource)
    (env : EnvState RegistrationServerRoleBackend.State) (empty : env.recordRequests = [])
    (value : Value) (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (((RegistrationBeaconReferenceFinish.abort (eraseOwner owner) *> pure value :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
              mlSource Value).run (eraseOwner current)).run env))).run before =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar provider)
          (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource Value).run current).run env)).run before := by
  have erased : RegistrationBeaconReferenceNativeRecord.erase env = env := by
    cases env
    simp_all only [RegistrationBeaconReferenceNativeRecord.erase]
  rw [adapt_abort, ← erased,
    RegistrationNativeProviderBeaconContinuation.abort_native setup wire route sign seed selectedScalar provider owner current env value before]
  simp only [Functor.map_map, Prod.map_def, id_eq]
  rw [erased]

/-- Complete incoming execution is the actual native owner controller, retaining original authentication, failures, state consumption, first opening and installation. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (packet : Option registration.ResponsePacket)
    (sameScalar : owner.prekeyScalar = localScalar.getD selectedScalar)
    (coherent : ∀ pending oneTime, owner.phase = .initSent pending oneTime →
      pending.control.expected_server_binding = pending.binding.server_pin.binding)
    (env : EnvState RegistrationServerRoleBackend.State) (empty : env.recordRequests = [])
    (erased : Std.Array U8 357#usize) (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (((RegistrationBeaconReferenceFinish.finish setup mlSource packet :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner owner)).run env))).run before =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar provider)
          (((RegistrationBeaconReferenceNativeOwner.finish setup mlSource wire packet :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run owner).run env)).run before := by
  have sameEnv : RegistrationBeaconReferenceNativeRecord.erase env = env := by
    cases env
    simp_all only [RegistrationBeaconReferenceNativeRecord.erase]
  rw [RegistrationBeaconReferenceNativeFinish.reference_factor]
  have phaseView : (eraseOwner owner).phase = owner.phase := rfl
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [RegistrationBeaconReferenceNativeFinish.incoming, RegistrationBeaconReferenceNativeOwner.finish,
        StateT.run_bind, StateT.run_get, pure_bind, phaseView, phase, StateT.run_pure,
        simulateQ_pure, map_pure, Prod.map_def, id_eq, view, sameEnv]
  | initSent pending oneTime =>
      simp only [RegistrationBeaconReferenceNativeFinish.incoming, RegistrationBeaconReferenceNativeOwner.finish,
        StateT.run_bind, StateT.run_get, pure_bind, phaseView, phase]
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq, view, sameEnv]
      | ok aborted =>
          simp only [StateT.run_modify, pure_bind, StateT.run_bind, StateT.run_lift,
            bind_pure_comp, simulateQ_bind, map_bind, bind_map_left,
            RegistrationBeaconReferenceNativeOwner.authentication]
          rw [effects_source]
          apply bind_congr_of_forall_mem_support
          rintro ⟨authenticated, afterPrivate⟩ supported
          cases authenticated with
          | fail error | div =>
              exact abort_source setup wire route sign seed selectedScalar localScalar provider owner
                { owner with phase := .aborted aborted } env empty _ afterPrivate
          | ok result => cases result with
            | Err error =>
                exact abort_source setup wire route sign seed selectedScalar localScalar provider owner
                  { owner with phase := .aborted aborted } env empty _ afterPrivate
            | Ok accepted =>
                have retained : accepted.pending = pending := by
                  cases packet with
                  | none =>
                      apply RegistrationBeaconResponseMetadata.simulated_pending
                        (trusted setup wire route sign seed selectedScalar provider ∘ₛ
                          (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ
                            RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify))
                        pending .None accepted before afterPrivate
                      simpa only [QueryImpl.simulateQ_compose] using supported
                  | some value =>
                      apply RegistrationBeaconResponseMetadata.simulated_pending
                        (trusted setup wire route sign seed selectedScalar provider ∘ₛ
                          (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ
                            RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify))
                        pending (.Some value) accepted before afterPrivate
                      simpa only [QueryImpl.simulateQ_compose] using supported
                have correct : accepted.pending.control.expected_server_binding = accepted.pending.binding.server_pin.binding := by
                  rw [retained]
                  exact coherent pending oneTime phase
                have actual := RegistrationNativeProviderBeaconPhase.phase_native setup wire route sign seed selectedScalar localScalar provider
                  owner { owner with phase := .aborted aborted } oneTime accepted correct env empty erased afterPrivate
                rw [← RegistrationBeaconReferenceGenericCallbacks.lower_program] at actual
                simp only [RegistrationBeaconReferenceGenericStage.lower,
                  simulateQ_bind, StateT.run, state_bind_apply, state_lift_apply, state_pure_apply,
                  pure_bind, bind_assoc, sameScalar,
                  map_bind, bind_map_left, RegistrationBeaconReferenceNativeContinuation.sourceAfter,
                  RegistrationBeaconReferenceNativeKnown.postRoot] at actual ⊢
                convert actual using 1; rfl

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFinish.finish_source
