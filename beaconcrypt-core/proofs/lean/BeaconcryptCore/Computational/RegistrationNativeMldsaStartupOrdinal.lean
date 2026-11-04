-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart

/-! Successful actual native Server initialization uses attempted ML generation ordinal zero. Constructor failure performs no generation, ML failure produces no initialized Server, and the subsequent real pin hash is ordinary source work with no second generation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStartupOrdinal
open RegistrationNativeMldsaOpaque (Pool handleSource birth)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
private theorem evaluate_bind {Value Next : Type}
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (next : Value → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Next) (pool : Pool source) :
    evaluate source (work >>= next) pool = (do
      let middle ← evaluate source work pool
      evaluate source (next middle.1) middle.2) := by
  simp only [evaluate, simulateQ_bind, StateT.run_bind]

private theorem evaluate_pure {Value : Type} (value : Value) (pool : Pool source) :
    evaluate source (pure value) pool = pure (value, pool) := by
  simp only [evaluate, simulateQ_pure, StateT.run_pure]


/-- Every successful actual opaque startup has empty raw primitive signing attempts and empty native payload receipts, including the real initialization prefix. -/
theorem server_ordinal (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64)
    (result : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ result.1) :
    initial.credential.secret = 0 ∧ result.2.bornAt = [0] ∧ result.2.attempts = 1 := by
  simp only [RegistrationNativeMldsaCreation.start, evaluate_bind,
    RegistrationNativeMldsaTableProgram.ordinary, mem_support_bind_iff] at supported
  obtain ⟨constructor, drawn, continued⟩ := supported
  rw [support_map] at drawn
  obtain ⟨constructed, _possible, same⟩ := drawn
  cases same
  cases selected : constructed.1.1 with
  | none =>
      simp only [selected, evaluate_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      cases member
  | some created =>
      simp only [selected] at continued
      rw [evaluate_bind] at continued
      change result ∈ support
        (runState source (RegistrationNativeMldsaProgram.call .native .generate) constructed.2 {} >>= _) at continued
      rw [RegistrationNativeMldsaTableProgram.generate_source, mem_support_bind_iff] at continued
      obtain ⟨generation, drawn, suffix⟩ := continued
      rw [support_map] at drawn
      obtain ⟨generated, _actual, same⟩ := drawn
      cases same
      rcases generated with ⟨generated, count⟩
      cases generated with
      | none =>
          simp only [birth, evaluate_pure, support_pure, Set.mem_singleton_iff] at suffix
          cases suffix
          cases member
      | some key =>
          simp only [birth] at suffix
          rw [evaluate_bind, RegistrationNativeMldsaTableProgram.ordinary, mem_support_bind_iff] at suffix
          obtain ⟨initialization, drawn, finished⟩ := suffix
          rw [support_map] at drawn
          obtain ⟨initialized, _actual, same⟩ := drawn
          cases same
          cases outcome : initialized.1 with
          | fail error | div =>
              simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
              cases finished
              cases member
          | ok option => cases option with
            | none =>
                simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
                cases finished
                cases member
            | some native =>
                simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
                cases finished
                simp only [Option.mem_some_iff] at member
                cases member
                exact ⟨rfl, rfl, rfl⟩
end BeaconcryptCore.Computational.RegistrationNativeMldsaStartupOrdinal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStartupOrdinal.server_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStartupOrdinal.server_ordinal
