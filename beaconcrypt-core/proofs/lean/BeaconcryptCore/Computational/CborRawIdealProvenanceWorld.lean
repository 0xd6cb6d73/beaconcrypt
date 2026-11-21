-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenance

/-! Full-state admissibility of raw public registration with the actual guarded record World. The proof uses the existing concrete split only for registration and the existing metadata-preserving record interpreter for fixed commands. In particular, identity-based legacy AD is derived and preserved rather than inferred from a view that forgets metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec)
open PqxdhDeploymentInterface (Entry Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good Splits Stable)
open PqxdhDeploymentIdealOrigins (IsFixed QuietEntry aEffects)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
open CborRecordWorldCursor (worldShell)
open CborRawIdealProvenanceStep (worldStep)
variable {ι KemSK Reader Response Bk : Type} {baseSpec : OracleSpec ι} {n : Nat}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Every fixed actual raw step preserves the complete concrete environment admissibility and private ideal invariant. -/
theorem fixed_keeps (env : Environment n (EnvState KemSK Bk)) (serverKid : Std.U64)
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv) (query : Spec.Domain) (isFixed : IsFixed query)
    (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n) (origins : Origins n)
    (good : Good created state.2 world) (holds : inv state.2 world)
    (result : Spec.Range query × ((Public × EnvState KemSK Bk) × PqxdhRecordLiftOrigins.State n))
    (supported : result ∈ support ((worldStep setup codec route
      (CborRawEnvironment.environment env serverKid) query).run (state, (world, origins)))) :
    Good created result.2.1.2 result.2.2.1 ∧ inv result.2.1.2 result.2.2.1 := by
  rw [CborRawIdealProvenanceStep.worldStep_body] at supported
  cases refused : CborRawGuardedJoin.refusal (n := n) query (worldShell world) with
  | some reply =>
      rw [refused, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨good, holds⟩
  | none =>
      rw [refused, CborRawIdealProvenance.ordinary_fixed_public setup codec route env serverKid query isFixed,
        support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhDeploymentIdealOrigins.aWorldStep_good setup codec route env reg created inv stable splits
        query state.2 world origins good holds inner reached

/-- Registration preserves the same concrete admissibility on every supported annotated outcome. -/
theorem registration_keeps (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (splits : Splits created reg env.step inv) (query : EnvQuery)
    (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n) (origins : Origins n)
    (good : Good created state.2 world) (holds : inv state.2 world)
    (result : (EnvSpec.Range query × (Public × EnvState KemSK Bk)) × PqxdhRecordLiftOrigins.State n)
    (supported : result ∈ support ((simulateQ (aEffects setup codec route)
      ((CborRawEnvironment.step env query).run state)).run (world, origins))) :
    Good created result.1.2.2 result.2.1 ∧ inv result.1.2.2 result.2.1 := by
  have erased : (result.1, result.2.1) ∈ support
      ((simulateQ PqxdhRecordLiftWorld.effects ((CborRawEnvironment.step env query).run state)).run world) := by
    rw [← PqxdhDeploymentIdealOrigins.aEffects_erase setup codec route _ (world, origins), support_map]
    exact ⟨result, supported, rfl⟩
  exact CborRawEnvironmentJoin.step_keeps env reg created inv splits query state world good holds _ erased

end BeaconcryptCore.Computational.CborRawIdealProvenanceWorld

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceWorld.fixed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceWorld.fixed_keeps

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceWorld.registration_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceWorld.registration_keeps
