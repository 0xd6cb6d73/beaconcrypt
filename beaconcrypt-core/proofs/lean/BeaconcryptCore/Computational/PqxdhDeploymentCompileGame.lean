-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant

/-! Theorem CE-COMPILE for the whole common deployment experiment (CE-3 trial). The deployment game, which constructs the Server from a generated seed and runs the adversary against the native handler, is the initialized source14 native execution of the compiled program, after merging the compiled program's final local copies into the final source14 state; through the existing erasure equality it is also the image of the initialized source14 execution that the KEM and root theorems are stated for. The statements use exactly two codec contracts, `Phase1ReadBack` and `Phase2ReadBack`, both approved for the common experiment; no other premise is added. The compiled program reads Server kernels and established Beacon kernels internally; these reads are never answered to the deployment adversary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileGame
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentCompile (Local merge compile)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A Server constructed from a generated seed has the requested key ID and no installed peer. -/
theorem construct_fields (primitives : Primitives) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (sender : Std.U64) (runtime : A) (created : PqxdhLiveServerConstruction.Created Unit) (after : A)
    (supported : (some created, after) ∈ support
      ((PqxdhLiveServerConstruction.construct primitives ensureInit identityIndex sender none).run runtime)) :
    created.server.server.metadata.sender = sender ∧ ∀ kid, created.server.server.peers kid = none := by
  simp only [PqxdhLiveServerConstruction.construct, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨ready, _, supported⟩ := supported
  split at supported
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨seed, _, rfl, _⟩ := supported
    exact ⟨rfl, fun _ => rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- The merged outcome of the compiled program's initialized execution. -/
def mergeOutcome (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK (X × Local)) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentNative.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1.1, merge result.2.1.2 result.2.2), outcome.2)

/-- Theorem CE-COMPILE: under the approved Phase 1 and Phase 2 read-back contracts, the deployment game with a generated Server seed is exactly the initialized source14 native execution of the compiled program with the merged final state, jointly over the constructed Server's public data, the adversary's output, the complete deployment state and the runtime state. -/
theorem compile_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) (runtime : A) :
    mergeOutcome <$> (PqxdhRegistrationJointInitializedSchedule.native setup codec checks ensureInit identityIndex none
        (compile setup codec route adversary)).run runtime =
      (PqxdhDeploymentNative.game setup codec checks route ensureInit identityIndex adversary).run runtime := by
  simp only [PqxdhRegistrationJointInitializedSchedule.native, PqxdhDeploymentNative.game, StateT.run, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | created, after⟩ born
  · simp only [map_pure, mergeOutcome, Option.map_none]
  · obtain ⟨sender, peers⟩ := construct_fields setup.joint ensureInit identityIndex setup.serverKeyId runtime
      created after born
    have compiled := PqxdhDeploymentCompileInvariant.compile_native setup codec checks route created.seed phase1 phase2
      adversary (PqxdhRegistrationSchedule.initial created) sender peers rfl (fun _ => rfl)
    simp only [StateT.run] at compiled
    simp only [PqxdhDeploymentNative.initial]
    rw [← compiled, Functor.map_map, Functor.map_map]
    rfl

/-- CE-COMPILE at the level of the initialized source14 execution used by the KEM and root theorems: erasing the private service annotations and merging the compiled program's local copies maps that execution of the compiled program exactly onto the deployment game, whose Server identity index is the private identity pool's current size. -/
theorem compile_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeOutcome (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
          (compile setup codec route adversary)).run state =
      (PqxdhDeploymentNative.game setup codec checks route ensureInit state.1.1.seeds.length adversary).run state.2 := by
  rw [← compile_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 adversary state.2,
    ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup codec checks ensureInit none
      (compile setup codec route adversary) state, Functor.map_map]

end BeaconcryptCore.Computational.PqxdhDeploymentCompileGame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.construct_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.construct_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.compile_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.compile_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.compile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileGame.compile_source
