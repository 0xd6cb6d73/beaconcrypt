-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend
open RegistrationNativeHiddenAllocationOwners (NativeIndexed)
open RegistrationNativeHiddenBeaconAllocationCaps (Allowed)
variable {n : Nat} {I KemSK Auxiliary Runtime Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable (callback : QueryImpl (Trusted n KemSK) (StateT Runtime ProbComp)) (count : Runtime → Nat)
variable (quiet : ∀ query before result, Allowed query → result ∈ support ((callback query).run before) → count result.2 = count before)

include quiet in
private theorem program_noappend (work : OracleComp (Trusted n KemSK) Value)
    (before : Runtime) (result : Value × Runtime) (safe : AllQueriesSatisfy work (Allowed (KemSK := KemSK)))
    (supported : result ∈ support ((simulateQ callback work).run before)) : count result.2 = count before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact (ih middle.1 middle.2 (later middle.1) continued).trans (quiet query before middle first reached)
private theorem source_support {Index : Type} {spec : OracleSpec Index} {Private : Type}
    (implementation : QueryImpl spec (StateT Private ProbComp)) (work : OracleComp spec Value)
    (before : Private) (result : Value × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) : result.1 ∈ support work := by
  apply support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩


include quiet in
/-- The genuine unchanged native constructor derives physical index correspondence from its actual per-leaf allocator receipts. -/
theorem create (setup : Setup base KemSK)
    (appended : ∀ sender identity phase before result,
      result ∈ support ((callback (.inl (.inr (.appendOwner sender identity phase)))).run before) →
      result.1 = count before ∧ count result.2 = count before + 1)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : Runtime)
    (result : ((RustM (Option Nat) × State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Runtime)
    (length : count before = owners.length) (indexed : NativeIndexed owners)
    (supported : result ∈ support ((simulateQ callback
      (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env)).run before)) :
    count result.2 = result.1.1.2.length ∧ NativeIndexed result.1.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have unchanged := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env middle.1
    (source_support _ _ before middle reached)
  have kept := program_noappend callback count quiet
    (((prepare source edPin mlPin keyId).run owners).run env) before middle
    (RegistrationNativeHiddenBeaconAllocationCaps.prepare_safe edPin mlPin keyId owners env) reached
  have leadingLength : count middle.2 = middle.1.1.2.length := by rw [kept, unchanged, length]
  have leadingIndexed : NativeIndexed middle.1.1.2 := by rw [unchanged]; exact indexed
  cases selected : middle.1.1.1 with
  | fail error | div =>
      simp only [selected, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact ⟨leadingLength, leadingIndexed⟩
  | ok chosen => cases chosen with
    | none =>
        simp only [selected, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
        exact ⟨leadingLength, leadingIndexed⟩
    | some prepared =>
        simp only [selected] at continued
        obtain ⟨born, afterBorn, worldOwner, afterAppend, generated, allocated, returned⟩ :=
          RegistrationNativeBeaconBirth.append_supported setup source
            callback edPin keyId prepared.pin
            prepared.identity prepared.prekey middle.1.1.2 middle.1.2 middle.2 result continued
        have kemKept := quiet
          (.inr (.inr (.inl .create))) middle.2 (born, afterBorn) trivial generated
        have appendReceipt := appended
          keyId edPin .fresh afterBorn (worldOwner, afterAppend) allocated
        cases returned
        constructor
        · simp only [List.length_append, List.length_singleton]
          exact appendReceipt.2.trans (congrArg (· + 1) (kemKept.trans leadingLength))
        · apply RegistrationNativeHiddenAllocationOwners.append _ _ leadingIndexed
          exact appendReceipt.1.trans (kemKept.trans leadingLength)

end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth.create
