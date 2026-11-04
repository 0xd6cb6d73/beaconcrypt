-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableRun

/-! Actual opaque startup uses the same constructor, source ML generation and current cache as the original native startup. A successful private key lookup restores the literal generated Server credential, and the initial owner invariant follows from the actual empty owner list. Failed prefixes retain their private table state without producing an initialized native session. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore birth Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (StateLive)
open RegistrationNativeMldsaTableProgram (evaluate runState)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)

def restored (result : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source) :
    Option (RegistrationNativeExperiment.Initial n KemSK source) :=
  result.1.bind fun initial =>
    (result.2.keys[initial.credential.secret]?).map fun key =>
      RegistrationNativeMldsaMap.initial (restore source key result.2) initial

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

/-- Actual private-table startup restores the complete original initialized native distribution, including all constructor and cache failures. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) :
    restored source <$> evaluate source
      (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {} =
      RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId := by
  unfold RegistrationNativeMldsaCreation.start RegistrationNativeExperiment.start
  rw [evaluate_bind, RegistrationNativeMldsaTableProgram.ordinary]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro constructed
  cases selected : constructed.1.1 with
  | none => simp only [evaluate_pure, map_pure, restored, Option.bind_none]
  | some created =>
      simp only
      rw [evaluate_bind]
      change (RegistrationNativeMldsaTableStart.restored source <$>
        (runState source (RegistrationNativeMldsaProgram.call .native .generate) constructed.2 {} >>= _)) = _
      rw [RegistrationNativeMldsaTableProgram.generate_source]
      simp only [bind_map_left, map_bind]
      have native := congrFun (RegistrationNativeMldsaProgram.eval_call (n := n) (source := source) .native .generate) constructed.2
      change RegistrationNativeMldsaProgram.evaluate
        ((RegistrationNativeMldsaProgram.call .native .generate).run constructed.2) =
          (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)).run constructed.2 at native
      rw [← native]
      simp only [RegistrationNativeMldsaProgram.evaluate, RegistrationNativeMldsaProgram.call, StateT.run,
        simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaProgram.actual, bind_pure_comp]
      rw [bind_map_left]
      apply bind_congr
      intro generated
      rcases generated with ⟨generated, count⟩
      cases generated with
      | none => simp only [birth, evaluate_pure, map_pure, restored, Option.bind_none]
      | some key =>
          simp only [birth]
          rw [evaluate_bind, RegistrationNativeMldsaTableProgram.ordinary]
          simp only [bind_map_left, map_bind]
          apply bind_congr
          intro initialized
          cases outcome : initialized.1 with
          | fail error | div => simp only [evaluate_pure, map_pure, restored, Option.bind_none]
          | ok option => cases option with
            | none => simp only [evaluate_pure, map_pure, restored, Option.bind_none]
            | some native =>
                simp only [evaluate_pure, map_pure, restored, Option.bind_some,
                  RegistrationNativeMldsaMap.initial,
                  RegistrationNativeMldsaMap.credential, restore]
                rfl

/-- Every actual successful startup supplies its reached real Server key and the initial live-owner invariant. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (result : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ result.1) :
    ∃ key, Live source result.2 initial.credential key ∧ StateLive source result.2 initial.state := by
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
                exact ⟨key, RegistrationNativeMldsaOpaque.birth_live source {} key count,
                  RegistrationNativeMldsaPoolMap.owners_empty source _⟩

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart.initialized
