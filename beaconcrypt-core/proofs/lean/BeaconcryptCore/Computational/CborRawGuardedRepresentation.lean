-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedErasure

/-! The hidden-slot representation change is valid for arbitrary guarded native clients. Registration service naturality is the existing concrete core theorem; record refusal reads only native cursors and commutes with service-state projection. This preserves the independent record/source codecs used by the raw environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedRepresentation
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhRecordLiftInterface (EnvQuery)
open PqxdhDeploymentBackend (RegImpl XState)
open PqxdhDeploymentSeedSplit (mapBackend SlotService CoreNatural ServiceProj)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response Bk Γ Result : Type} {baseSpec : OracleSpec ι} {n : Nat}
section Representation
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Native admission forwards every restricted registration request directly to its actual handler. -/
theorem native_env (reg : RegImpl KemSK Bk n) (query : EnvQuery) :
    CborRawGuardedJoin.nativeHandler setup codec route reg (.inr query.val) = reg query := by
  rcases query with ⟨command, valid⟩
  cases command
  all_goals first | rfl | exact absurd valid id

/-- Changing the hidden service representation leaves all actual send cursors and refusal decisions unchanged. -/
theorem fixed_mapBackend {S₁ S₂ : Type} (proj : S₁ → S₂) (reg₁ : RegImpl KemSK (S₁ × Γ) n)
    (reg₂ : RegImpl KemSK (S₂ × Γ) n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) (state : XState KemSK (S₁ × Γ) n) :
    Prod.map id (mapBackend proj) <$>
        (CborRawGuardedJoin.nativeHandler setup codec route reg₁ query).run state =
      (CborRawGuardedJoin.nativeHandler setup codec route reg₂ query).run (mapBackend proj state) := by
  simp only [CborRawGuardedJoin.nativeHandler, StateT.run]
  have same : CborRecordNativeAdmission.nativeShell (mapBackend proj state).base =
      CborRecordNativeAdmission.nativeShell state.base := rfl
  rw [same]
  cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | some reply => simp only [map_pure]; rfl
  | none => exact PqxdhDeploymentSeedSplit.fixed_mapBackend setup codec route proj reg₁ reg₂ query notEnv state

/-- A refused send and every ordinary fixed step retain the complete private service backend. -/
theorem fixed_backend (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) (state : XState KemSK Bk n)
    (value : Spec.Range query × XState KemSK Bk n)
    (supported : value ∈ support ((CborRawGuardedJoin.nativeHandler setup codec route reg query).run state)) :
    value.2.backend = state.backend := by
  simp only [CborRawGuardedJoin.nativeHandler, StateT.run] at supported
  cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | some reply =>
      rw [refused, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | none =>
      rw [refused] at supported
      exact PqxdhDeploymentSeedSplit.fixed_backend setup codec route reg query notEnv state value supported

/-- The hidden-service representation step for every adaptive guarded native program. -/
theorem represent_run
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂)
    (svc₁ : SlotService S₁ n) (svc₂ : SlotService S₂ n) (related : ServiceProj inv proj svc₁ svc₂)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result)
    (state : XState KemSK (S₁ × Γ) n) (holds : inv state.backend.1) :
    LawEq (Prod.map id (mapBackend proj) <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route (core svc₁ created)) work).run state)
      ((simulateQ (CborRawGuardedJoin.nativeHandler setup codec route (core svc₂ created)) work).run
        (mapBackend proj state)) := by
  apply PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj
    (CborRawGuardedJoin.nativeHandler setup codec route (core svc₁ created))
    (CborRawGuardedJoin.nativeHandler setup codec route (core svc₂ created)) (fun current => inv current.backend.1)
    (mapBackend proj) ?_ ?_ work state holds
  · intro query current valid
    by_cases registration : ∃ command : EnvQuery, query = .inr command.val
    · obtain ⟨command, rfl⟩ := registration
      rw [native_env, native_env]
      exact (natural inv proj svc₁ svc₂ related created command current valid).1
    · exact LawEq.of_eq (fixed_mapBackend setup codec route proj _ _ query
        (fun command same => registration ⟨command, same⟩) current)
  · intro query current valid value supported
    by_cases registration : ∃ command : EnvQuery, query = .inr command.val
    · obtain ⟨command, rfl⟩ := registration
      rw [native_env] at supported
      exact (natural inv proj svc₁ svc₂ related created command current valid).2 value supported
    · rw [fixed_backend setup codec route _ query (fun command same => registration ⟨command, same⟩) current value
        supported]
      exact valid

end Representation
section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {SourceReader SourceResponse : Type}

/-- Concrete table-to-split representation of the erased ideal registration under native admission. The actual initial states discharge both service invariants. -/
theorem represent_ideal (setup : Setup baseSpec KemSK) (recordCodec : Codec Reader Response)
    (sourceCodec : Codec SourceReader SourceResponse) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) :
    LawEq (Prod.map id (mapBackend Prod.fst) <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealCoreErased setup sourceCodec route checks target parameters
            PqxdhDeploymentSeedSplit.tableService created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      (Prod.map id (mapBackend PqxdhDeploymentSeedSplit.joinTable) <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealCoreErased setup sourceCodec route checks target parameters
            PqxdhDeploymentSeedSplit.splitService created)) work).run
          (PqxdhDeploymentBackend.xinitial created ((∅, ∅),
            (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhDeploymentIdealSteps.IdealCore.initial)))) := by
  let core := fun {S} svc created => PqxdhDeploymentIdealSteps.idealCoreErased setup sourceCodec route checks target
    parameters (S := S) svc created
  have natural : CoreNatural core := PqxdhDeploymentIdealSteps.idealCoreErased_natural setup sourceCodec route checks target parameters
  have table := represent_run setup recordCodec route core natural (fun _ => True) Prod.fst
    PqxdhDeploymentSeedSplit.tableService PqxdhDeploymentSeedSplit.lazyService
    PqxdhDeploymentSeedSplit.table_service_proj created work
    (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) trivial
  have split := represent_run setup recordCodec route core natural PqxdhDeploymentSeedSplit.BothOrNeither
    PqxdhDeploymentSeedSplit.joinTable PqxdhDeploymentSeedSplit.splitService PqxdhDeploymentSeedSplit.lazyService
    PqxdhDeploymentSeedSplit.split_service_proj created work
    (PqxdhDeploymentBackend.xinitial created ((∅, ∅),
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhDeploymentIdealSteps.IdealCore.initial)))
    (fun _ => rfl)
  have same : mapBackend Prod.fst
      (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := 2) created (PqxdhDeploymentIdealSteps.idealInit created)) =
      mapBackend PqxdhDeploymentSeedSplit.joinTable
        (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := 2) created ((∅, ∅),
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhDeploymentIdealSteps.IdealCore.initial))) := rfl
  rw [same] at table
  exact table.trans split.symm

end Ideal
end BeaconcryptCore.Computational.CborRawGuardedRepresentation

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedRepresentation.native_env' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedRepresentation.native_env
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedRepresentation.fixed_mapBackend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedRepresentation.fixed_mapBackend
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedRepresentation.fixed_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedRepresentation.fixed_backend
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedRepresentation.represent_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedRepresentation.represent_run
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedRepresentation.represent_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedRepresentation.represent_ideal
