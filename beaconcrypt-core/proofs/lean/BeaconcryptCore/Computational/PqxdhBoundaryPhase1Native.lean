-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleCosts

/-! Literal source14 and CE Phase-1 bundle consumers, retaining complete native state on every optional result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRegistrationSchedule (Owner)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- The addressed native owner executes the existing generator/signature/writer callbacks. -/
def ownerProgram (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : Owner KemSK) : ProbComp (Option Pqxdh.Bytes × Owner KemSK) :=
  simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
    (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner)

/-- Native callbacks sign the exact projected retained key material, then invoke the original optional writer. -/
def preparedResult (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (owner : Owner KemSK) :
    Option Pqxdh.Bytes × Owner KemSK :=
  match PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => (none, owner)
  | some prepared =>
      let identity := (setup.joint.publicKeys owner.beacon.identity).ed25519
      let keys : PqxdhEd25519EufCma.Phase1KeyTuple :=
        ⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩
      let candidate := PqxdhJointPhase1SourceWriter.signedCandidate setup.joint
        owner.beacon.identity identity keys
      match codec.write1 candidate with
      | none => (none, owner)
      | some bytes => (some bytes, PqxdhBeaconPhase1Publication.publish
          (PqxdhLivePhase1Bundle.identityArray identity) prepared owner)

/-- Native preparation consumes the same three source signing messages and literal writer result, preserving failure as an unchanged complete role state. -/
theorem native_prepared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (generated : Option PqxdhJointGapDh.ScalarBytes) (owner : Owner KemSK) :
    simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.afterGenerated (PqxdhRegistrationSchedule.projection setup index) generated owner) =
      pure (preparedResult setup codec generated owner) := by
  unfold PqxdhLivePhase1Bundle.afterGenerated preparedResult
  cases chosen : PqxdhBeaconPhase1Publication.prepare owner generated <;> simp only [simulateQ_pure, simulateQ_bind, PqxdhDeploymentCompileFootprint.signing_run, pure_bind, PqxdhDeploymentCompileFootprint.writing_run, chosen]
  rfl

/-- The original Fresh branch samples exactly the local one-time scalar before preparation; retained coins and inactive phases make no such draw. -/
theorem owner_source_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : Owner KemSK) :
    ownerProgram setup codec index owner =
      match owner.beacon.phase with
      | .fresh _ _ _ => (fun generated => preparedResult setup codec (some generated) owner) <$>
          PqxdhJointGapDh.sampleScalar
      | .freshWithCoins _ _ _ _ => pure (preparedResult setup codec none owner)
      | _ => pure (none, owner) := by
  cases phase : owner.beacon.phase <;> simp only [ownerProgram, PqxdhLivePhase1Bundle.bundle, phase, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, native_prepared]
  simp only [PqxdhRegistrationSchedule.bundleCallbacks, bind_pure_comp, Functor.map_map]

/-- The actual source14 bundle reinstalls precisely the returned owner; every other owner and shared field is retained on success and failure. -/
theorem source14_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (state : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.bundle setup codec index).run state =
      match state.owners[index]? with
      | none => pure (none, state)
      | some owner => (fun result => (result.1, { state with owners := state.owners.set index result.2 })) <$>
        ownerProgram setup codec index owner := by
  simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : state.owners[index]? <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_lift, StateT.run_modify, pure_bind]
  simp only [bind_pure_comp, ownerProgram, Functor.map_map]

/-- CE's literal bundle command has the exact source14 optional reply and complete deployment poststate, with counters and produced-record log unchanged. -/
theorem native_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.bundle index))).run state =
      match state.native.owners[index]? with
      | none => pure (none, state)
      | some owner => (fun result => (result.1,
          { state with native := { state.native with owners := state.native.owners.set index result.2 } })) <$>
        ownerProgram setup codec index owner := by
  change (fun result => (result.1, { state with native := result.2 })) <$>
    (PqxdhRegistrationSchedule.bundle setup codec index).run state.native = _
  rw [source14_bundle]
  cases state.native.owners[index]? <;> simp only [map_pure, Functor.map_map]

/-- The full CE continuation consumes the actual generator and optional writer outcome at the source position; no success conditioning or marginal-state equality is used. -/
theorem native_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (state : PqxdhDeploymentNative.State KemSK)
    (next : Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK → ProbComp Result) :
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.bundle index))).run state >>= next =
      match state.native.owners[index]? with
      | none => next (none, state)
      | some owner =>
          let resume := fun result : Option Pqxdh.Bytes × Owner KemSK =>
            next (result.1, { state with native := { state.native with owners := state.native.owners.set index result.2 } })
          match owner.beacon.phase with
          | .fresh _ _ _ => PqxdhJointGapDh.sampleScalar >>= fun generated =>
              resume (preparedResult setup codec (some generated) owner)
          | .freshWithCoins _ _ _ _ => resume (preparedResult setup codec none owner)
          | _ => resume (none, owner) := by
  rw [native_bundle]
  cases found : state.native.owners[index]? <;> simp only [pure_bind, owner_source_order]
  rename_i owner
  cases owner.beacon.phase <;> simp only [map_pure, pure_bind, Functor.map_map]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]

/-- The whole actual native attempt retains the source cap of 32 uniform byte queries; deterministic signing, serialization and state updates remain explicit local work. -/
theorem native_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    ((PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.bundle index))).run state).IsTotalQueryBound 32 := by
  change ((fun result => (result.1, { state with native := result.2 })) <$>
    (PqxdhRegistrationSchedule.bundle setup codec index).run state.native).IsTotalQueryBound 32
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhRegistrationSchedule.bundle_uniform setup codec index state.native

end BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_prepared

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.owner_source_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.owner_source_order

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.source14_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.source14_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native.native_uniform
