-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceAgreement
import BeaconcryptCore.Computational.RegistrationNativeSelectedFinishSourceAgreement
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase

/-! Selected and ordinary owners share one actual finishing phase. Only ordinary preparation materializes its own two prekey-DH inputs; later operations are literal forwards. The comparison drops only the private reference memo, after proving the root-free continuation cannot read it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (Frame drop put)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec)
open RegistrationBeaconReferenceNativePreparation (restored)
open RegistrationBeaconReferenceNativeContinuation (view sourceAfter afterPrepared)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def adapt (setup : Setup base KemSK) : Option ScalarBytes → QueryImpl (Spec n KemSK) (OracleComp (Spec n KemSK))
  | none => QueryImpl.id' _
  | some scalar => RegistrationNativePublicOwners.ordinary setup scalar

/-- The source interpreter follows either the selected private scalar or the ordinary scalar retained by that owner. -/
theorem agreement_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1.1, (result.1.2, drop result.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env))).run before =
      (fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup (trusted setup wire route sign seed selectedScalar)
          (localScalar.getD selectedScalar) owner oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before) := by
  cases localScalar with
  | none =>
      simp only [adapt, simulateQ_id', Option.getD_none]
      exact RegistrationNativeSelectedFinishSourceAgreement.agreement_source setup wire route sign seed selectedScalar
        owner oneTime authenticated coherent env before
  | some scalar =>
      exact RegistrationNativeOrdinaryFinishSourceAgreement.agreement_source setup wire route sign seed selectedScalar scalar
        owner oneTime authenticated coherent env before

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
    (seed : IdentitySeed) (selectedScalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) :
    RustM agreement.AgreementEffect × (EnvState Auxiliary × Frame n KemSK) →
      ProbComp (((RustM (Option Pqxdh.Bytes) × SelectedOwner mlSource) × EnvState Auxiliary) × Frame n KemSK) :=
  fun reached => Prod.map view drop <$>
    (simulateQ (trusted setup wire route sign seed selectedScalar)
      (((sourceAfter setup wire owner reached.1 :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run
          (put RegistrationNativeReferenceInterpreter.initial reached.2.2)

noncomputable def phase (setup : Setup base KemSK) (owner : SelectedOwner mlSource)
    (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
      mlSource (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated)
  afterPrepared setup.source owner result

/-- The whole post-authentication phase runs the actual native agreement followed by its actual terminal/open/install continuation. Canonicalizing its inaccessible memo is justified by the root-free program equation. -/
theorem phase_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (empty : env.recordRequests = [])
    (erased : Std.Array U8 227#usize) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((phase setup (eraseOwner owner) oneTime authenticated :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run env))).run before =
      ((fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup (trusted setup wire route sign seed selectedScalar)
          (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)) >>=
            continueSource setup wire route sign seed selectedScalar owner current := by
  have combined := congrArg (fun script => script >>= continueSource setup wire route sign seed selectedScalar owner current)
    (agreement_source setup wire route sign seed selectedScalar localScalar (eraseOwner owner) oneTime
      authenticated coherent env before)
  rw [← combined]
  simp only [phase, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨result, afterEnv⟩, afterPrivate⟩ supported
  have adaptedSupport : (result, afterEnv) ∈ support
      (simulateQ (adapt setup localScalar)
        ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup (eraseOwner owner) oneTime authenticated).run env)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (implementation setup wire route sign seed selectedScalar) _ before
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
  have continuation := RegistrationNativeOrdinaryFinishSourceContinuation.continuation_native setup wire route sign seed selectedScalar
    owner current afterEnv authenticated result erased afterPrivate
  rw [erasedAfter] at continuation
  rw [continuation]
  have framed := congrArg (fun distribution => Prod.map view id <$> distribution)
    (RegistrationNativeOrdinaryFinishSourceFrame.program_frame setup wire route sign seed selectedScalar
      RegistrationNativeReferenceInterpreter.initial
      (((sourceAfter setup wire owner (restored afterPrivate.extra.1 authenticated result) :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run afterEnv)
      afterPrivate)
  simpa only [Functor.map_map, Prod.map_def, id_eq, continueSource,
    RegistrationNativeOrdinaryFinishSourceFrame.reset] using framed

/-- Canonicalizing the inaccessible memo changes no result or retained native frame in the actual root-free continuation. -/
theorem continue_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource)
    (result : RustM agreement.AgreementEffect) (env : EnvState Auxiliary) (before : Private n KemSK) :
    continueSource setup wire route sign seed selectedScalar owner current (result, (env, drop before)) =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((sourceAfter setup wire owner result :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run
              before := by
  have framed := congrArg (fun distribution => Prod.map view id <$> distribution)
    (RegistrationNativeOrdinaryFinishSourceFrame.program_frame setup wire route sign seed selectedScalar
      RegistrationNativeReferenceInterpreter.initial
      (((sourceAfter setup wire owner result :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, continueSource,
    RegistrationNativeOrdinaryFinishSourceFrame.reset] using framed.symm

/-- The actual native agreement and continuation retain their reached private state; only the proved memo-independent observation is projected. -/
theorem phase_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : EnvState Auxiliary) (empty : env.recordRequests = [])
    (erased : Std.Array U8 227#usize) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((phase setup (eraseOwner owner) oneTime authenticated :
            RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
              mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run env))).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceGenericStage.native setup
        (trusted setup wire route sign seed selectedScalar) (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((sourceAfter setup wire owner reached.1 :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run
              reached.2.2) := by
  rw [phase_source setup wire route sign seed selectedScalar localScalar owner current oneTime authenticated coherent env empty erased before,
    bind_map_left]
  apply bind_congr
  rintro ⟨result, afterEnv, afterPrivate⟩
  exact continue_frame setup wire route sign seed selectedScalar owner current result afterEnv afterPrivate

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.agreement_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.phase_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.continue_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.continue_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.phase_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase.phase_native
