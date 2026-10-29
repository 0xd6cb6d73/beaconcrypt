-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyInitialized
import BeaconcryptCore.Computational.CborRawHeadlineStartup

/-! Actual counted startup can be forgotten only after its complete continuation has been proved to depend on the original draw. The non-counting World state remains explicit in every supported branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyStartup
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentEnvironmentJoin (uncount)
open CborRawHeadlineStartup (coins coins_projection coins_fresh)
variable {n : Nat} {ι KemSK Reader Response A Value X : Type} {baseSpec : OracleSpec ι}

/-- A supported bound on every actual counted continuation gives its bound under the exact original uncounted draw. -/
theorem counted_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (draw : ProbComp Value)
    (left : Value → PqxdhRecordLiftWorld.State n → ProbComp Bool) (right : Value → ProbComp Bool)
    (state : PqxdhRecordLiftWorld.State n)
    (bounded : ∀ value ∈ support draw, ∀ world, uncount world = uncount state →
      𝒟[left value world] {true} ≤ 𝒟[right value] {true}) :
    𝒟[coins setup codec route draw state >>= fun value => left value.1 value.2] {true} ≤
      𝒟[draw >>= right] {true} := by
  have projected : draw >>= right = coins setup codec route draw state >>= fun value => right value.1 := by
    calc draw >>= right = (Prod.fst <$> coins setup codec route draw state) >>= right :=
        congrArg (fun work : ProbComp Value => work >>= right) (coins_projection setup codec route draw state).symm
      _ = _ := by rw [bind_map_left]
  rw [projected, ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro value reached
  have original : value.1 ∈ support draw := by
    rw [← coins_projection setup codec route draw state, support_map]
    exact ⟨value, reached, rfl⟩
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
  exact bounded value.1 original value.2 (coins_fresh setup codec route draw state value reached)

/-- Removing only the private pool result from the exact source Server birth gives the actual native predictor startup. -/
theorem fixed_source (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ((PqxdhRegistrationJointServerBirth.source (KemSK := KemSK) setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
      match born.1 with
      | none => pure none
      | some created => CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary) =
    CborRawAnomalyPool.fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary := by
  simp only [CborRawAnomalyPool.fixed, PqxdhRegistrationJointServerBirth.source, StateT.run,
    PqxdhDynamicIdentityPool.initialState, List.length_nil, bind_map_left]
  rfl

end BeaconcryptCore.Computational.CborRawAnomalyStartup

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyStartup.counted_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyStartup.counted_le
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyStartup.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyStartup.fixed_source
