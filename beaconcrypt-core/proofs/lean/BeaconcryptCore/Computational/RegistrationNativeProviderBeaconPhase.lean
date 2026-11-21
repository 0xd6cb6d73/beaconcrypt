-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconFrame

/-! The full native Beacon phase keeps the arbitrary KEM provider through agreement and runs the genuine source108 terminal continuation afterward. The inaccessible reference memo is canonicalized only through the proved adaptive memo-frame law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPhase
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState implementation)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeProviderBeaconPreparation (Frame drop)
open RegistrationNativeProviderBeaconFrame (put)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt phase)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec)
open RegistrationBeaconReferenceNativePreparation (restored)
open RegistrationBeaconReferenceNativeContinuation (view sourceAfter afterPrepared)
variable {n : Nat} {ι KemSK ProviderState Auxiliary : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem adapted_after (setup : Setup base KemSK) (localScalar : Option ScalarBytes)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    simulateQ (adapt setup localScalar)
      (((afterPrepared setup.source owner result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((afterPrepared setup.source owner result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar =>
      cases result with
      | fail error | div =>
          simp only [adapt, afterPrepared, RegistrationBeaconReferenceFinish.abort, seqRight_eq_bind,
            StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map,
            RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query,
            RegistrationNativePublicOwners.ordinary]
      | ok result => cases result with
        | none =>
            simp only [adapt, afterPrepared, RegistrationBeaconReferenceFinish.abort, seqRight_eq_bind,
              StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map,
              RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query,
              RegistrationNativePublicOwners.ordinary]
        | some ready => exact RegistrationNativeOrdinaryFinishSourceWrapper.complete_program setup scalar owner current env ready

noncomputable def continueSource (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) :
    RustM agreement.AgreementEffect × (EnvState Auxiliary × Frame n KemSK ProviderState) →
      ProbComp (((RustM (Option Pqxdh.Bytes) × SelectedOwner mlSource) × EnvState Auxiliary) × Frame n KemSK ProviderState) :=
  fun reached => Prod.map view drop <$>
    (simulateQ (trusted setup wire route sign seed selectedScalar provider)
      (((sourceAfter setup wire owner reached.1 :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run
          (put RegistrationNativeReferenceInterpreter.initial reached.2.2)

private theorem phase_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (empty : env.recordRequests = [])
    (erased : Std.Array U8 227#usize) (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (((phase setup (eraseOwner owner) oneTime authenticated :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run env))).run before =
      ((fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup
          (trusted setup wire route sign seed selectedScalar provider)
          (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)) >>=
            continueSource setup wire route sign seed selectedScalar provider owner current := by
  have combined := congrArg (fun script => script >>= continueSource setup wire route sign seed selectedScalar provider owner current)
    (RegistrationNativeProviderBeaconAgreement.agreement_source setup wire route sign seed selectedScalar localScalar provider
      (eraseOwner owner) oneTime authenticated coherent env before)
  rw [← combined]
  simp only [phase, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨result, afterEnv⟩, afterPrivate⟩ supported
  have adaptedSupport : (result, afterEnv) ∈ support
      (simulateQ (adapt setup localScalar)
        ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup (eraseOwner owner) oneTime authenticated).run env)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (implementation setup wire route sign seed selectedScalar provider false) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ adaptedSupport
  have kept := RegistrationBeaconReferenceAgreementScope.agreement_keeps setup (eraseOwner owner) oneTime authenticated
    env afterEnv result original
  have afterEmpty : afterEnv.recordRequests = [] := kept.trans empty
  have erasedAfter : RegistrationBeaconReferenceNativeRecord.erase afterEnv = afterEnv := by
    cases afterEnv
    simp_all only [RegistrationBeaconReferenceNativeRecord.erase]
  rw [adapted_after]
  have continuation := RegistrationNativeProviderBeaconContinuation.continuation_native setup wire route sign seed selectedScalar provider
    owner current afterEnv authenticated result erased afterPrivate
  rw [erasedAfter] at continuation
  rw [continuation]
  have framed := congrArg (fun distribution => Prod.map view id <$> distribution)
    (RegistrationNativeProviderBeaconFrame.program_frame setup wire route sign seed selectedScalar provider
      RegistrationNativeReferenceInterpreter.initial
      (((sourceAfter setup wire owner (restored afterPrivate.1.extra.1 authenticated result) :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run afterEnv)
      afterPrivate)
  simpa only [Functor.map_map, Prod.map_def, id_eq, continueSource,
    RegistrationNativeProviderBeaconFrame.reset] using framed

private theorem continue_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource)
    (result : RustM agreement.AgreementEffect) (env : EnvState Auxiliary) (before : NativeState n KemSK ProviderState) :
    continueSource setup wire route sign seed selectedScalar provider owner current (result, (env, drop before)) =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar provider)
          (((sourceAfter setup wire owner result :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  have framed := congrArg (fun distribution => Prod.map view id <$> distribution)
    (RegistrationNativeProviderBeaconFrame.program_frame setup wire route sign seed selectedScalar provider
      RegistrationNativeReferenceInterpreter.initial
      (((sourceAfter setup wire owner result :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, continueSource,
    RegistrationNativeProviderBeaconFrame.reset] using framed.symm

/-- The complete provider-dependent native agreement and source108 continuation agree, dropping only the inaccessible reference memo and explicit owner/request analysis view. -/
theorem phase_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (empty : env.recordRequests = [])
    (erased : Std.Array U8 227#usize) (before : NativeState n KemSK ProviderState) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (((phase setup (eraseOwner owner) oneTime authenticated :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run env))).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceGenericStage.native setup
        (trusted setup wire route sign seed selectedScalar provider) (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar provider)
          (((sourceAfter setup wire owner reached.1 :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run
              reached.2.2) := by
  rw [phase_source setup wire route sign seed selectedScalar localScalar provider owner current oneTime authenticated coherent env empty erased before,
    bind_map_left]
  apply bind_congr
  rintro ⟨result, afterEnv, afterPrivate⟩
  exact continue_frame setup wire route sign seed selectedScalar provider owner current result afterEnv afterPrivate

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPhase.phase_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPhase.phase_native
