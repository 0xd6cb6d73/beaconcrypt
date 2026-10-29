-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineStartup

/-! Equality through the actual counted startup retains the complete reached World, including request bills. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawStartupEquality
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentEnvironmentJoin (uncount)
open CborRawHeadlineStartup (coins coins_projection coins_fresh)
variable {ι KemSK Reader Response Value : Type} {baseSpec : OracleSpec ι} {n : Nat}

/-- Pointwise continuation probabilities lift exactly through counted startup coins. -/
theorem bind_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (draw : ProbComp Value) (left : Value → ProbComp Bool)
    (right : Value → PqxdhRecordLiftWorld.State n → ProbComp Bool) (state : PqxdhRecordLiftWorld.State n)
    (same : ∀ value ∈ support draw, ∀ world, uncount world = uncount state →
      𝒟[left value] {true} = 𝒟[right value world] {true}) :
    𝒟[draw >>= left] {true} = 𝒟[coins setup codec route draw state >>= fun value => right value.1 value.2] {true} := by
  have initialDraw : draw >>= left = coins setup codec route draw state >>= fun value => left value.1 := by
    calc draw >>= left = (Prod.fst <$> coins setup codec route draw state) >>= left :=
        congrArg (fun work : ProbComp Value => work >>= left) (coins_projection setup codec route draw state).symm
      _ = _ := by rw [bind_map_left]
  rw [initialDraw, ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
  apply le_antisymm
  all_goals
    apply prEvent_bind_mono_of_forall_le_of_support
    intro value reached
    have original : value.1 ∈ support draw := by
      rw [← coins_projection setup codec route draw state, support_map]
      exact ⟨value, reached, rfl⟩
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
  · exact le_of_eq (same value.1 original value.2 (coins_fresh setup codec route draw state value reached))
  · exact le_of_eq (same value.1 original value.2 (coins_fresh setup codec route draw state value reached)).symm

end BeaconcryptCore.Computational.CborRawStartupEquality
/-- info: 'BeaconcryptCore.Computational.CborRawStartupEquality.bind_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawStartupEquality.bind_eq
