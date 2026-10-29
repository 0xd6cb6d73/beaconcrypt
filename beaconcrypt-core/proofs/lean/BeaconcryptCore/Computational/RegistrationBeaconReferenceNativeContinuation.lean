-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion

/-! The finite post-agreement continuation is reconstructed from the actual private root memo. Source failures and absent preparation abort; successful preparation uses the full actual sequence-one controller. The public continuation contains neither the selected scalar nor a root or kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def view (value : (Value × Owner mlSource) × EnvState Auxiliary) :=
  ((value.1.1, eraseOwner value.1.2), RegistrationBeaconReferenceNativeRecord.erase value.2)

noncomputable def sourceAfter (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (owner : Owner mlSource) :
    RustM agreement.AgreementEffect →
      RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationBeaconReferenceNativeOwner.abort owner *> pure (.fail error)
  | .div => RegistrationBeaconReferenceNativeOwner.abort owner *> pure .div
  | .ok (.BeaconComplete agreement) => RegistrationBeaconReferenceNativeKnown.postRoot setup wire owner agreement
  | .ok _ => RegistrationBeaconReferenceNativeOwner.abort owner *> pure (.ok none)

noncomputable def afterPrepared (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) : RustM (Option RegistrationBeaconReferenceRoot.Ready) →
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationBeaconReferenceFinish.abort owner *> pure (.fail error)
  | .div => RegistrationBeaconReferenceFinish.abort owner *> pure .div
  | .ok none => RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none)
  | .ok (some ready) => RegistrationBeaconReferenceFinish.complete source owner ready

private theorem through (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
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
      (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource Value).run current).run env) =
      (((RegistrationBeaconReferenceCompletion.abort RegistrationBeaconReferenceNativeRecord.environment (eraseOwner owner) *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Trusted n KemSK) (Auxiliary := Auxiliary) mlSource Value).run
          (eraseOwner current)).run (RegistrationBeaconReferenceNativeRecord.erase env)) := by
  simp only [RegistrationBeaconReferenceNativeOwner.abort, RegistrationBeaconReferenceCompletion.abort,
    seqRight_eq_bind, StateT.run_lift, bind_pure_comp, StateT.run_map,
    RegistrationBeaconReferenceNativeRecord.environment, Functor.map_map, view]
  rfl

theorem abort_owner_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (value : Value) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceCompletion.abort effect (eraseOwner owner) *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource Value).run (eraseOwner current)).run
              (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource Value).run current).run env)).run
              before.2.2 := by
  have projected := through setup checks representation created _ _ (abort_projection owner current env value) before.2.2
  exact (RegistrationBeaconReferenceNativeCompletion.abort_source setup checks wire representation created scalar credential
    (eraseOwner owner) (eraseOwner current) (RegistrationBeaconReferenceNativeRecord.erase env) value before).trans projected.symm

/-- The entire post-agreement continuation is the actual native source continuation, with only private preparation bookkeeping, the selected scalar and the request analysis ledger projected. -/
theorem continuation_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (authenticated : registration.AuthenticatedResponse) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (erased : Std.Array U8 357#usize) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((afterPrepared setup.source (eraseOwner owner) result :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run
              (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((sourceAfter setup wire owner (RegistrationBeaconReferenceNativePreparation.restored before.1 authenticated result) :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  cases result with
  | fail error | div => exact abort_owner_source setup checks wire representation created scalar credential owner current env _ before
  | ok ready => cases ready with
    | none => exact abort_owner_source setup checks wire representation created scalar credential owner current env _ before
    | some ready =>
        cases root : before.1 ready.reference with
        | none =>
            simp only [RegistrationBeaconReferenceNativePreparation.restored, root, sourceAfter]
            rw [afterPrepared, RegistrationBeaconReferenceNativeCompletion.complete_missing setup checks wire representation
              created scalar credential (eraseOwner owner) (eraseOwner current) (RegistrationBeaconReferenceNativeRecord.erase env)
              ready before root]
            exact (through setup checks representation created _ _
              (abort_projection owner current env (.ok none : RustM (Option Pqxdh.Bytes))) before.2.2).symm
        | some rootValue =>
            simp only [RegistrationBeaconReferenceNativePreparation.restored, root, sourceAfter]
            rw [afterPrepared, RegistrationBeaconReferenceNativeCompletion.complete_known setup checks wire representation
              created scalar credential (eraseOwner owner) (eraseOwner current) (RegistrationBeaconReferenceNativeRecord.erase env)
              ready rootValue before root]
            exact (through setup checks representation created _ _
              (RegistrationBeaconReferenceNativeKnown.post_root setup wire erased owner current ready.descriptor rootValue env)
              before.2.2).symm

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation.continuation_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation.abort_owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation.abort_owner_source
