-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix

/-! The selected KEM candidate has no influence on the source's post-encapsulation queries. A private marker can therefore replace its retained bytes until the root-input interpreter, while preserving the complete original suffix and stateful effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix
open PqxdhServerRootPreparation
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
variable {Reader E Shared : Type}

/-- Replace only the retained KEM output; all actual source values and private handles remain intact. -/
def replaceKem (value : Word32) (input : Inputs Reader E Shared) : Inputs Reader E Shared :=
  { input with kem := value }

/-- Every post-encapsulation request is independent of the retained KEM bytes. This is an equality of complete oracle programs, including all failures and reply continuations. -/
theorem after_replace (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : Ciphertext) (first second : Word32) :
    Option.map (replaceKem second) <$>
      PqxdhRegistrationJointKemCollected.afterEncapsulation (Shared := Shared) verified ephemeral (some (ciphertext, first)) =
    PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral (some (ciphertext, second)) := by
  unfold PqxdhRegistrationJointKemCollected.afterEncapsulation
  repeat
    first
    | rfl
    | (fail_if_no_progress simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
        OptionT.run_monadLift, Option.elimM, Option.elim_some,
        bind_map_left, map_bind, pure_bind,
        Bool.not_true, Bool.false_eq_true, ite_false])
    | (apply bind_congr; intro answer; cases answer)

abbrev Token := PqxdhPhase2DecapsulationRouting.Shared

/-- Private source preparation without selected KEM bytes. Every other original field is retained, including the actual ephemeral scalar and all DH outputs. The marker is not a public reply. -/
structure Prepared (Reader E Shared : Type) where
  verified : Verified Reader
  ephemeral : Ephemeral E
  ciphertext : Ciphertext
  convertedIdentity : Word32
  first : Shared
  second : Word32
  third : Word32
  fourth : Word32
  shared : Token

def erase (token : Token) (input : Inputs Reader E Shared) : Prepared Reader E Shared :=
  ⟨input.verified, input.ephemeral, input.ciphertext, input.convertedIdentity,
    input.first, input.second, input.third, input.fourth, token⟩

/-- Selected bytes occur only in this mathematical interpreter, never in the marker-bearing executable suffix. -/
def materialize (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Prepared Reader E Shared) : Inputs Reader E Shared :=
  ⟨input.verified, input.ephemeral, input.ciphertext, input.convertedIdentity,
    input.first, input.second, input.third, input.fourth,
    PqxdhRootTableInitialization.rootArray (PqxdhPhase2DecapsulationRouting.materialize candidate input.shared)⟩

/-- Erasure removes only the selected-byte slot; the interpreter restores that slot and keeps all original fields. -/
theorem materialize_erase (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (token : Token) (input : Inputs Reader E Shared) :
    materialize candidate (erase token input) =
      replaceKem (PqxdhRootTableInitialization.rootArray
        (PqxdhPhase2DecapsulationRouting.materialize candidate token)) input := rfl

/-- A fixed local dummy is used only to run candidate-independent source requests; it is erased before the program returns. -/
def placeholder : Word32 := PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)

/-- Execute the original suffix once and retain a private shared-secret marker. It has no candidate argument and preserves every actual query and optional failure. -/
def program (verified : Verified Reader) (ephemeral : Ephemeral E) (ciphertext : Ciphertext)
    (token : Token) : OracleComp (Spec Reader E Shared) (Option (Prepared Reader E Shared)) :=
  Option.map (erase token) <$> PqxdhRegistrationJointKemCollected.afterEncapsulation
    verified ephemeral (some (ciphertext, placeholder))

/-- Interpreting the private marker gives the complete original source suffix, for every candidate value and every optional callback reply. -/
theorem program_native (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (verified : Verified Reader) (ephemeral : Ephemeral E) (ciphertext : Ciphertext) (token : Token) :
    Option.map (materialize candidate) <$> program (Shared := Shared) verified ephemeral ciphertext token =
      PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral
        (some (ciphertext, PqxdhRootTableInitialization.rootArray
          (PqxdhPhase2DecapsulationRouting.materialize candidate token))) := by
  simp only [program, Functor.map_map, Option.map_map, Function.comp_def, materialize_erase]
  exact after_replace verified ephemeral ciphertext placeholder _

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Response : Type}

/-- Compile the actual candidate-free suffix with the same initialized source handler and consumed-registration state. -/
noncomputable def compiled (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : Ciphertext) (token : Token) :=
  simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
    (program (Shared := Word32) verified ephemeral ciphertext token)

/-- The initialized stateful suffix preserves every consumed-state update and optional result; only the private marker is interpreted. This equality retains the complete evaluated state, not a result marginal. -/
theorem compiled_native (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : Ciphertext) (token : Token) (consumed : List Pqxdh.Bytes) :
    (fun result => (Option.map (materialize candidate) result.1, result.2)) <$>
      (compiled setup codec checks identityIndex raw verified ephemeral ciphertext token).run consumed =
      (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
        (some (ciphertext, PqxdhRootTableInitialization.rootArray
          (PqxdhPhase2DecapsulationRouting.materialize candidate token)))).run consumed := by
  have same := congrArg (fun work =>
    (simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run consumed)
    (program_native (Shared := Word32) candidate verified ephemeral ciphertext token)
  simpa only [simulateQ_map, StateT.run_map, compiled,
    PqxdhRegistrationJointKemSourceSuffix.suffix] using same

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.after_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.after_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.materialize_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.materialize_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.program_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.compiled_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix.compiled_native
