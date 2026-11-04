-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPhase
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishMaterial
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase
/-! An ordinary owner's reference translation changes preparation only. Corrected material demand, charged opening, assigned-ID installation and abort forward literally, for arbitrary prior record markers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationNativePlatformBeaconMaterialFrontend (chosen complete abort)
open RegistrationNativePlatformBeaconMaterialInterpreter (demand)
variable {n : Nat} {I KemSK Auxiliary Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- Corrected terminal abort does not translate any reference. -/
theorem abort (setup : Setup base KemSK) (localScalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : Value) :
    simulateQ (adapt setup localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK)) Value).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value :
        RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK)) Value).run current).run env) := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar =>
    simp only [adapt, RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind,
      StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map, effect,
      simulateQ_spec_query, RegistrationNativePublicOwners.ordinary]

/-- The complete corrected material program is a literal Env program under either reference route. -/
theorem chosen (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (localScalar : Option PqxdhJointGapDh.ScalarBytes) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState Auxiliary) :
    simulateQ (adapt setup localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite effect owner ready choice).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite effect owner ready choice).run current).run env) := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar =>
    exact RegistrationNativeOrdinaryFinishSourceWrapper.effects_program setup scalar _

/-- The actual demand and all optional material outcomes retain the same returned reference. -/
theorem complete (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (localScalar : Option PqxdhJointGapDh.ScalarBytes) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    simulateQ (adapt setup localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete (n := n) setup.source wire.frameWrite effect demand owner ready).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete (n := n) setup.source wire.frameWrite effect demand owner ready).run current).run env) := by
  cases localScalar with
  | none => exact simulateQ_id' _
  | some scalar =>
    simp only [adapt, RegistrationNativePlatformBeaconMaterialFrontend.complete,
      StateT.run_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
      demand, RegistrationNativePublicOwners.ordinary, bind_map_left]
    congr 1
    funext choice
    cases choice with
    | none => exact abort setup (some scalar) owner current env (.ok none : RustM (Option Pqxdh.Bytes))
    | some choice => exact chosen setup wire (some scalar) owner current ready choice env

/-- The corrected full post-preparation source continuation is literal after ordinary reference translation. -/
theorem after_prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (localScalar : Option PqxdhJointGapDh.ScalarBytes) (owner current : SelectedOwner source)
    (env : EnvState Auxiliary) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    simulateQ (adapt setup localScalar)
      (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner result :
        RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK))
          (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner result :
        RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK))
          (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  cases result with
  | fail error | div => exact abort setup localScalar owner current env _
  | ok result => cases result with
    | none => exact abort setup localScalar owner current env _
    | some ready => exact BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.complete setup wire localScalar owner current ready env
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt

namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishContinuation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler (eraseOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (drop)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationNativePlatformBeaconContinuation (view sourceAfter afterPrepared)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The corrected post-preparation continuation consumes the actual returned memo cell and retains the entire reached source frame. -/
theorem continuation_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner source) (env : EnvState Auxiliary)
    (authenticated : registration.AuthenticatedResponse) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (erased : Std.Array U8 357#usize) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((afterPrepared setup.source wire.frameWrite (eraseOwner owner) result :
            RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Spec n KemSK))
              (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run env))).run before =
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((sourceAfter setup wire owner (restored before.extra.1 authenticated result) :
            RegistrationNativePlatformBeaconOwner.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  rw [RegistrationNativePlatformPublicFinishAdapt.after_prepared]
  cases result with
  | fail error =>
    have compared := congrArg (fun action => Prod.map id drop <$> action)
      (RegistrationNativePlatformPublicFinishMaterial.abort_source setup wire route sign seed selectedScalar owner current env (.fail error : RustM (Option Pqxdh.Bytes)) before)
    simpa only [afterPrepared, sourceAfter, restored, RegistrationBeaconReferenceRoot.restored,
      Functor.map_map, Prod.map_def, id_eq] using compared
  | div =>
    have compared := congrArg (fun action => Prod.map id drop <$> action)
      (RegistrationNativePlatformPublicFinishMaterial.abort_source setup wire route sign seed selectedScalar owner current env (.div : RustM (Option Pqxdh.Bytes)) before)
    simpa only [afterPrepared, sourceAfter, restored, RegistrationBeaconReferenceRoot.restored,
      Functor.map_map, Prod.map_def, id_eq] using compared
  | ok ready => cases ready with
    | none =>
      have compared := congrArg (fun action => Prod.map id drop <$> action)
        (RegistrationNativePlatformPublicFinishMaterial.abort_source setup wire route sign seed selectedScalar owner current env (.ok none : RustM (Option Pqxdh.Bytes)) before)
      simpa only [afterPrepared, sourceAfter, restored, RegistrationBeaconReferenceRoot.restored, RegistrationBeaconAgreementRoot.rejected,
        Functor.map_map, Prod.map_def, id_eq] using compared
    | some ready =>
      cases found : before.extra.1 ready.reference with
      | none =>
        rw [afterPrepared, RegistrationNativePlatformPublicFinishMaterial.complete_missing setup wire route sign seed selectedScalar _ _ ready env before found]
        have compared := congrArg (fun action => Prod.map id drop <$> action)
          (RegistrationNativePlatformPublicFinishMaterial.abort_source setup wire route sign seed selectedScalar owner current env (.ok none : RustM (Option Pqxdh.Bytes)) before)
        simpa only [sourceAfter, restored, found, RegistrationBeaconAgreementRoot.rejected,
          Functor.map_map, Prod.map_def, id_eq] using compared
      | some root =>
        rw [afterPrepared, RegistrationNativePlatformPublicFinishMaterial.complete_source setup wire route sign seed selectedScalar owner current ready root env before found erased]
        simp only [sourceAfter, restored, found, Functor.map_map, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishContinuation

namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishPhase
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler (eraseOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (Frame drop put)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationNativePlatformBeaconContinuation (view sourceAfter)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private noncomputable def continuation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner current : RegistrationNativeBeaconFrontend.Owner source) :
    RustM agreement.AgreementEffect × (EnvState RegistrationServerRoleBackend.State × Frame n KemSK) →
      ProbComp (((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) ×
        EnvState RegistrationServerRoleBackend.State) × Frame n KemSK) := fun reached =>
  Prod.map view drop <$>
    (simulateQ (trusted setup wire route sign seed scalar)
      (((sourceAfter setup wire owner reached.1 : RegistrationNativePlatformBeaconOwner.M n KemSK
        RegistrationServerRoleBackend.State source (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run
          (put RegistrationNativeReferenceInterpreter.initial reached.2.2)

/-- Actual source root preparation and the corrected charged first-record continuation compose without discarding prior record markers. -/
theorem phase_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner source) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (env : EnvState RegistrationServerRoleBackend.State) (erased : Std.Array U8 357#usize) (before : Private n KemSK) :
    Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((RegistrationNativePlatformBeaconPhase.phase setup wire (eraseOwner owner) oneTime authenticated).run
            (eraseOwner current)).run env))).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceGenericStage.native setup
        (trusted setup wire route sign seed selectedScalar) (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)
      Prod.map view drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((sourceAfter setup wire owner reached.1 : RegistrationNativePlatformBeaconOwner.M n KemSK
            RegistrationServerRoleBackend.State source (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2) := by
  let next := continuation (n := n) setup wire route sign seed selectedScalar owner current
  have agreement := RegistrationNativeOrdinaryFinishSourcePhase.agreement_source setup wire route sign seed selectedScalar localScalar
    (eraseOwner owner) oneTime authenticated coherent env before
  have combined := congrArg (fun action => action >>= next) agreement
  have framed : Prod.map id drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (adapt setup localScalar)
          (((RegistrationNativePlatformBeaconPhase.phase setup wire (eraseOwner owner) oneTime authenticated).run
            (eraseOwner current)).run env))).run before =
      ((fun result => (result.1, (result.2.1, drop result.2.2))) <$>
        (simulateQ (RegistrationBeaconReferenceGenericStage.native setup (trusted setup wire route sign seed selectedScalar)
          (localScalar.getD selectedScalar) (eraseOwner owner) oneTime)
          (RegistrationAgreementExecutor.beacon authenticated)).run (env, before)) >>= next := by
    rw [← combined]
    simp only [RegistrationNativePlatformBeaconPhase.phase, StateT.run_bind, StateT.run_lift,
      bind_pure_comp, simulateQ_bind, map_bind, bind_map_left]
    apply bind_congr
    rintro ⟨⟨result, afterEnv⟩, afterPrivate⟩
    rw [RegistrationNativePlatformPublicFinishContinuation.continuation_source setup wire route sign seed selectedScalar localScalar
      owner current afterEnv authenticated result erased afterPrivate]
    have unchanged := congrArg (fun distribution => Prod.map view id <$> distribution)
      (RegistrationNativeOrdinaryFinishSourceFrame.program_frame setup wire route sign seed selectedScalar
        RegistrationNativeReferenceInterpreter.initial
        (((sourceAfter setup wire owner (restored afterPrivate.extra.1 authenticated result) :
          RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State source
            (RustM (Option Pqxdh.Bytes))).run current).run afterEnv) afterPrivate)
    simpa only [Functor.map_map, Prod.map_def, id_eq, next, continuation,
      RegistrationNativeOrdinaryFinishSourceFrame.reset] using unchanged
  rw [framed, bind_map_left]
  apply bind_congr
  rintro ⟨result, afterEnv, afterPrivate⟩
  have unchanged := congrArg (fun distribution => Prod.map view id <$> distribution)
    (RegistrationNativeOrdinaryFinishSourceFrame.program_frame setup wire route sign seed selectedScalar
      RegistrationNativeReferenceInterpreter.initial
      (((sourceAfter setup wire owner result : RegistrationNativePlatformBeaconOwner.M n KemSK
        RegistrationServerRoleBackend.State source (RustM (Option Pqxdh.Bytes))).run current).run afterEnv) afterPrivate)
  simpa only [Functor.map_map, Prod.map_def, id_eq, next, continuation,
    RegistrationNativeOrdinaryFinishSourceFrame.reset] using unchanged.symm
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.abort

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.chosen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.after_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAdapt.after_prepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishContinuation.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishContinuation.continuation_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishPhase.phase_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishPhase.phase_native
