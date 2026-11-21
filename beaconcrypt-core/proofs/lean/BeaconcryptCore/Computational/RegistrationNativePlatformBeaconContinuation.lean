-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion

/-! The corrected finite post-agreement continuation is reconstructed from the actual private root memo. Source failures and absent preparation abort; successful preparation uses the complete source sequence-one controller with assigned-ID installation. Only the selected scalar and private reference bookkeeping are projected; the entire local environment and Native state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def view (value : (Value × Owner mlSource) × EnvState Auxiliary) :=
  ((value.1.1, eraseOwner value.1.2), value.2)

noncomputable def sourceAfter (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (owner : Owner mlSource) :
    RustM agreement.AgreementEffect →
      RegistrationNativePlatformBeaconOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativePlatformBeaconOwner.abort owner *> pure (.fail error)
  | .div => RegistrationNativePlatformBeaconOwner.abort owner *> pure .div
  | .ok (.BeaconComplete agreement) => RegistrationNativePlatformBeaconMaterialKnown.postRoot setup wire owner agreement
  | .ok _ => RegistrationNativePlatformBeaconOwner.abort owner *> pure (.ok none)

noncomputable def afterPrepared (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner : SelectedOwner mlSource) : RustM (Option RegistrationBeaconReferenceRoot.Ready) →
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.fail error)
  | .div => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure .div
  | .ok none => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.ok none)
  | .ok (some ready) => RegistrationNativePlatformBeaconMaterialFrontend.complete source writer effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready

private theorem through (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (source : OracleComp (Trusted n KemSK) ((Value × Owner mlSource) × EnvState Auxiliary))
    (target : OracleComp (Trusted n KemSK) ((Value × SelectedOwner mlSource) × EnvState Auxiliary))
    (equal : view <$> source = target) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map view id <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) source).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) target).run before := by
  have lifted := congrArg (fun program =>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) program).run before) equal
  simpa only [simulateQ_map, StateT.run_map, Prod.map_def, id_eq] using lifted

private theorem abort_projection (owner current : Owner mlSource)
    (env : EnvState Auxiliary) (value : Value) :
    view <$>
      (((RegistrationNativePlatformBeaconOwner.abort owner *> pure value :
        RegistrationNativePlatformBeaconOwner.M n KemSK Auxiliary mlSource Value).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceNativeRecord.environment (eraseOwner owner) *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Trusted n KemSK) (Auxiliary := Auxiliary) mlSource Value).run
          (eraseOwner current)).run env) := by
  simp only [RegistrationNativePlatformBeaconOwner.abort, RegistrationNativePlatformBeaconMaterialFrontend.abort,
    seqRight_eq_bind, StateT.run_lift, bind_pure_comp, StateT.run_map,
    RegistrationBeaconReferenceNativeRecord.environment, Functor.map_map, view]
  rfl

theorem abort_owner_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (value : Value) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect (eraseOwner owner) *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource Value).run (eraseOwner current)).run
              env)).run before =
      Prod.map view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationNativePlatformBeaconOwner.abort owner *> pure value :
            RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource Value).run current).run env)).run
              before.2.2 := by
  have projected := through setup checks representation created _ _ (abort_projection owner current env value) before.2.2
  have compiled := RegistrationNativePlatformBeaconMaterialInterpreter.abort_source setup checks wire representation created scalar credential
    (eraseOwner owner) (eraseOwner current) env value before
  have observed := congrArg (fun work => RegistrationBeaconReferenceNativeCompletion.drop <$> work) compiled
  simp only [Functor.map_map, RegistrationBeaconReferenceNativeCompletion.drop, Prod.mk.eta, id_map'] at observed
  simpa only [RegistrationBeaconReferenceNativeCompletion.drop] using observed.trans projected.symm


/-- The entire post-agreement continuation is the actual native source continuation, with only private preparation bookkeeping and the selected scalar projected; its complete local environment is retained. -/
theorem continuation_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (authenticated : registration.AuthenticatedResponse) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (erased : Std.Array U8 227#usize) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((afterPrepared setup.source wire.frameWrite (eraseOwner owner) result :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run
              env)).run before =
      Prod.map view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((sourceAfter setup wire owner (RegistrationBeaconReferenceNativePreparation.restored before.1 authenticated result) :
            RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  cases result with
  | fail error | div => exact abort_owner_source setup checks wire representation created scalar credential owner current env _ before
  | ok ready => cases ready with
    | none => exact abort_owner_source setup checks wire representation created scalar credential owner current env _ before
    | some ready =>
        cases root : before.1 ready.reference with
        | none =>
            simp only [RegistrationBeaconReferenceNativePreparation.restored, root, sourceAfter]
            rw [afterPrepared, RegistrationNativePlatformBeaconMaterialInterpreter.complete_missing setup checks wire representation
              created scalar credential (eraseOwner owner) (eraseOwner current) ready env before root]
            simp only [Functor.map_map, RegistrationBeaconReferenceNativeCompletion.drop, Prod.mk.eta, id_map']
            exact (through setup checks representation created _ _
              (abort_projection owner current env (.ok none : RustM (Option Pqxdh.Bytes))) before.2.2).symm
        | some rootValue =>
            simp only [RegistrationBeaconReferenceNativePreparation.restored, root, sourceAfter]
            rw [afterPrepared, RegistrationNativePlatformBeaconMaterialInterpreter.complete_known setup checks wire representation
              created scalar credential (eraseOwner owner) (eraseOwner current) ready rootValue env before root]
            simp only [Functor.map_map, RegistrationBeaconReferenceNativeCompletion.drop, Prod.mk.eta, id_map']
            exact (through setup checks representation created _ _
              (RegistrationNativePlatformBeaconMaterialKnown.known_source setup wire erased owner current ready rootValue env)
              before.2.2).symm

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation.abort_owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation.abort_owner_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation.continuation_source

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation
