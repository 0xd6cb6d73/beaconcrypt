-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompileStep
import BeaconcryptCore.Computational.PqxdhDeploymentCompileGame

/-! The admission compiler preserves the generated Server experiment jointly over public Server data, the adaptive program output, the complete merged deployment state and runtime state. Successful Server construction initializes its public assignment counter, so the initialized game/source join needs only the existing Phase 1 and Phase 2 read-back contracts. This operational equality does not identify canonical transcript events with a physical raw-response secrecy ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCompileGame
open PqxdhServerAuthExperiment PqxdhJointIdentity
open CborAdmissionCompiler (Local merge compile)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A generated Server starts with the requested identity and allocation counter and no installed peer. -/
theorem construct_fields (primitives : Primitives) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (sender : Std.U64) (runtime : A) (created : PqxdhLiveServerConstruction.Created Unit) (after : A)
    (supported : (some created, after) ∈ support
      ((PqxdhLiveServerConstruction.construct primitives ensureInit identityIndex sender none).run runtime)) :
    created.server.server.metadata.sender = sender ∧
      created.control.last_key_id = sender ∧ ∀ keyId, created.server.server.peers keyId = none := by
  simp only [PqxdhLiveServerConstruction.construct, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨ready, _, supported⟩ := supported
  split at supported
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨seed, _, rfl, _⟩ := supported
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- The generated-Server experiment with the fixed-codec native size-admission handler. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentNative.State KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
      (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2), born.2)) <$>
        (simulateQ (CborAdmissionCompiler.nativeHandler setup codec checks route created.seed) adversary).run
          (PqxdhDeploymentNative.initial created)

/-- Merge all final compiler copies while retaining the generated Server's public data and runtime state. -/
def mergeOutcome (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK (X × Local)) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentNative.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1.1, merge result.2.1.2 result.2.2), outcome.2)

/-- Generated initialization and adaptive source14 compilation jointly preserve every reply, merged state and runtime state. -/
theorem compile_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) (runtime : A) :
    mergeOutcome <$> (PqxdhRegistrationJointInitializedSchedule.native setup codec checks ensureInit identityIndex none
        (compile setup codec route adversary)).run runtime =
      (game setup codec checks route ensureInit identityIndex adversary).run runtime := by
  simp only [PqxdhRegistrationJointInitializedSchedule.native, game, StateT.run, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | created, after⟩ born
  · simp only [map_pure, mergeOutcome, Option.map_none]
  · obtain ⟨sender, lastId, peers⟩ := construct_fields setup.joint ensureInit identityIndex setup.serverKeyId runtime
      created after born
    have compiled := CborAdmissionCompileStep.compile_native setup codec checks route created.seed phase1 phase2
      adversary (PqxdhRegistrationSchedule.initial created) sender lastId peers rfl (fun _ => rfl)
    simp only [StateT.run] at compiled
    simp only [PqxdhDeploymentNative.initial]
    rw [← compiled, Functor.map_map, Functor.map_map]
    rfl

/-- The existing initialized source erasure gives the same generated size-admission game after merging compiler copies. -/
theorem compile_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeOutcome (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)) <$>
      (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
        (compile setup codec route adversary)).run state =
      (game setup codec checks route ensureInit state.1.1.seeds.length adversary).run state.2 := by
  rw [← compile_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 adversary state.2,
    ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup codec checks ensureInit none
      (compile setup codec route adversary) state, Functor.map_map]

end BeaconcryptCore.Computational.CborAdmissionCompileGame

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileGame.construct_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileGame.construct_fields
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileGame.compile_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileGame.compile_game
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileGame.compile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileGame.compile_source
