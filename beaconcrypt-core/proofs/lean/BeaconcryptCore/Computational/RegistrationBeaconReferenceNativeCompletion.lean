-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement

/-! Finite completion continuations use the actual reached native World and the earlier returned root. Root memo/family bookkeeping stays private. Scalar-free owner phases and the full mutable environment remain in the compared output. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhRecordLiftInterface (EnvEffects)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def drop (result : Value × State n KemSK mlSource) := (result.1, result.2.2.2)

def aborting (owner : Nat) (value : Value) : OracleComp (EnvEffects n) Value := do
  let _ ← (EnvEffects n).query (.inr (.advanceOwner owner .aborted))
  pure value

private theorem abort_run {Index Auxiliary : Type} {target : OracleSpec Index}
    (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary) (value : Value) :
    (((RegistrationBeaconReferenceCompletion.abort environment owner *> pure value :
      RegistrationBeaconReferenceCompletion.M (target := target) (Auxiliary := Auxiliary) mlSource Value).run current).run env) =
      (fun answer => ((answer, current), env)) <$> simulateQ environment (aborting owner.worldOwner value) := by
  simp only [RegistrationBeaconReferenceCompletion.abort, aborting, seqRight_eq_bind,
    StateT.run_lift, StateT.run_map, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, Functor.map_map]

private theorem actual_effect (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
  funext query
  simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
    simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]

private theorem actual_raw (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    RegistrationNativeExperiment.trusted (n := n) setup checks representation created mlSource ∘ₛ
      (RegistrationBeaconReferenceNativeRecord.environment ∘ₛ RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created ∘ₛ
        RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite := by
  funext query
  simp only [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose, actual_effect]

/-- Terminal abort uses the same existing World effect, retaining every native state field and the current owner/environment. -/
theorem abort_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : SelectedOwner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (value : Value) (before : State n KemSK mlSource) :
    drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceCompletion.abort effect owner *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource Value).run current).run env)).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceCompletion.abort RegistrationBeaconReferenceNativeRecord.environment owner *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource Value).run current).run env)).run before.2.2 := by
  rw [abort_run, abort_run]
  simp only [simulateQ_map, StateT.run_map]
  have actual := congrArg (fun work => (fun result => (((result.1, current), env), result.2.2.2)) <$> work)
    (RegistrationBeaconReferenceNativeMaterial.effects_program setup checks wire representation created scalar credential
      (aborting owner.worldOwner value) before)
  simpa only [Functor.map_map, drop, ← QueryImpl.simulateQ_compose, actual_effect] using actual

/-- Every successful or failed scalar-free settling branch uses exactly the same concrete native World and owner phase. -/
theorem after_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : SelectedOwner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (result : RustM RegistrationNativePairedBeaconService.Result) (before : State n KemSK mlSource) :
    drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceCompletion.after effect owner result :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceCompletion.after RegistrationBeaconReferenceNativeRecord.environment owner result :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  cases result with
  | fail error | div => exact abort_source setup checks wire representation created scalar credential owner current env _ before
  | ok result => cases result with
    | Err error => exact abort_source setup checks wire representation created scalar credential owner current env _ before
    | Ok completed =>
        simp only [RegistrationBeaconReferenceCompletion.after, StateT.run_bind, StateT.run_modify,
          pure_bind, StateT.run_pure, simulateQ_pure, map_pure, drop]

noncomputable def knownEffects (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner : SelectedOwner mlSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput) :
    OracleComp (EnvEffects n) (RustM RegistrationNativePairedBeaconService.Result) := do
  let result ← simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer)
    (RegistrationNativePairedBeaconService.program source descriptor (PqxdhServerAuthKeySchedule.fromRoot source root))
  RegistrationNativePairedBeaconService.after owner.worldOwner owner.pin.binding.identity_key_id
    (fun completed => .known completed.kernel) result

private theorem reference_settle (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready) :
    RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK)
      (Auxiliary := RegistrationServerRoleBackend.State) source owner ready = (do
        let completed ← StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceFinish.service
          (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id
            ready.descriptor ready.reference)))
        RegistrationBeaconReferenceCompletion.after effect owner completed) := by
  unfold RegistrationBeaconReferenceFinish.complete
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

private theorem native_settle (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner mlSource) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationBeaconReferenceNativeKnown.factored (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      setup wire owner descriptor root = (do
        let completed ← StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
          (knownEffects setup.source wire.frameWrite owner descriptor root)))
        RegistrationBeaconReferenceCompletion.after RegistrationBeaconReferenceNativeRecord.environment owner completed) := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [RegistrationBeaconReferenceNativeKnown.factored, RegistrationBeaconReferenceNativeKnown.after,
    knownEffects, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, bind_map_left, bind_assoc]

/-- A completed reference uses the root actually prepared earlier and the same complete native opening, installation and owner-phase continuation. -/
theorem complete_known (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : SelectedOwner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (before : State n KemSK mlSource) (prepared : before.1 ready.reference = some root) :
    drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceNativeKnown.factored setup wire owner ready.descriptor root :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  rw [reference_settle, native_settle]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, map_bind, bind_map_left]
  rw [RegistrationBeaconReferenceNativeMaterial.admitted_known setup checks wire representation created scalar credential
    owner.worldOwner owner.pin.binding.identity_key_id ready root before prepared,
    RegistrationBeaconReferenceNativeMaterial.known_source]
  simp only [knownEffects, simulateQ_bind, ← QueryImpl.simulateQ_compose, actual_effect, actual_raw, bind_map_left]
  apply bind_congr
  rintro ⟨completed, afterNative⟩
  exact after_source setup checks wire representation created scalar credential owner current env completed
    (before.1, (before.2.1, afterNative))

/-- An unprepared reference rejects before any source108 opening; its actual terminal abort is retained on the reached World. -/
theorem complete_missing (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : SelectedOwner mlSource) (env : EnvState RegistrationServerRoleBackend.State)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : State n KemSK mlSource)
    (missing : before.1 ready.reference = none) :
    drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceCompletion.abort RegistrationBeaconReferenceNativeRecord.environment owner *>
          pure (.ok none) :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.2.2 := by
  rw [reference_settle]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, StateT.run_map,
    simulateQ_bind, simulateQ_map, map_bind, bind_map_left,
    RegistrationNativePairedBeaconService.admitted, simulateQ_spec_query, RegistrationBeaconReferenceFinish.service]
  rw [RegistrationBeaconReferenceNativeInterpreter.demand_missing setup checks wire representation created scalar credential
    ready.reference before missing]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure, RegistrationBeaconReferenceCompletion.after]
  exact abort_source setup checks wire representation created scalar credential owner current env _ before

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.abort_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.after_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.complete_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.complete_known
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.complete_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion.complete_missing
