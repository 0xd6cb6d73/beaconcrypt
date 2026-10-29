-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordNativeAdmission
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin

/-! Reassembly of registration and record state retains precisely the native public sending cursors. Legacy associated-data admissibility is internal to this existing reassembly; cursor equality reads no chain, cache or signing material. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordWorldMerge
variable {n : Nat} {KemSK Bk : Type}
open CborRecordWorldCursor (worldShell)
open CborRecordNativeAdmission (nativeShell)

private theorem shell_ext (left right : CborRecordWorldClient.Shell)
    (server : left.server = right.server) (owners : left.owners = right.owners) : left = right := by
  cases left
  cases right
  cases server
  cases owners
  rfl

/-- The actual filled native state and World have identical sender/counter metadata at every admitted join. -/
theorem merge_shell (created : PqxdhLiveServerConstruction.Created Unit)
    (env : PqxdhDeploymentEnvironment.EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : PqxdhDeploymentEnvironmentJoin.Good created env world) :
    nativeShell (PqxdhDeploymentEnvironmentJoin.merge env world).base = worldShell world := by
  apply shell_ext
  · obtain ⟨server, existing, senderEq, _⟩ := good.server
    simp only [nativeShell, worldShell, PqxdhDeploymentEnvironmentJoin.merge,
      PqxdhDeploymentEnvironmentJoin.fill, PqxdhDeploymentEnvironmentJoin.fillServer,
      existing, Option.map_some, MldsaLegacyServerRouting.forgetServer,
      Option.map_map, MldsaLegacyServerRouting.forgetPeer, Function.comp_def, senderEq]
  · funext index
    simp only [nativeShell, worldShell, PqxdhDeploymentEnvironmentJoin.merge,
      PqxdhDeploymentEnvironmentJoin.fill, List.getElem?_mapIdx]
    cases present : env.native.owners[index]? with
    | none =>
      have absent : world.owners[index]? = none := List.getElem?_eq_none_iff.mpr
        (by rw [good.ownersLength]; exact List.getElem?_eq_none_iff.mp present)
      simp only [absent, Option.map_none, Option.bind_none]
    | some owner =>
      have matched := good.owners index owner present
      cases phaseEq : world.owners[index]? with
      | none => simp only [phaseEq, Option.map_none, reduceCtorEq] at matched
      | some phase =>
        simp only [phaseEq, Option.map_some, Option.some.injEq] at matched
        rcases PqxdhDeploymentEnvironmentJoin.phase_cases phase owner matched with inactive | established
        · obtain ⟨filled, tag, phaseSame, notEstablished⟩ := inactive
          simp only [Option.map_some, Option.bind_some, phaseSame]
          cases nativePhase : owner.beacon.phase <;>
            simp only [PqxdhDeploymentEnvironmentJoin.fillOwner, nativePhase, RawCtxBeaconLifecycle.Established, not_true_eq_false] at notEstablished ⊢
        · obtain ⟨control, ad, stale, kernel, nativePhase, phaseSame⟩ := established
          simp only [Option.map_some, Option.bind_some,
            PqxdhDeploymentEnvironmentJoin.fillOwner, phaseSame, nativePhase]

end BeaconcryptCore.Computational.CborRecordWorldMerge

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldMerge.merge_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldMerge.merge_shell
