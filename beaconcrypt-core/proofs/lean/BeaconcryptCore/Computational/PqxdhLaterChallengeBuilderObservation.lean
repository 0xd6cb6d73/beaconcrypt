-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollectorBefore
import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor

/-! Observe the actual initial Builder callback as well as before-admission callbacks, retaining the complete native state and all complementary mass. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderObservation
open PqxdhLaterChallengeCapture PqxdhLaterChallengeSavedMonitor
variable {ι M P I D K Local : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Keep an actual initial Builder cut, replacing only its outside continuation by the pure returned Builder result. Wrapper cuts and completed runs retain their complementary None outcome. -/
noncomputable def builderKey (cut : PqxdhLaterChallengeBuilderCoupling.Outcome
    (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Bool) (Local := Local) (S := S) (B := B)) :
    Option (PqxdhInitialOriginContext.Context extra M P I D K PqxdhInitialBuilderContext.BuildResult Bool S B × Local) :=
  match cut with
  | .pending (context, none) state =>
      match context.original with
      | .inr saved => some (builderOnly saved context.trace context.origin, state)
      | _ => none
  | _ => none

/-- Both complete source-prefix worlds have the same initial Builder callback and full native state, including the entire complementary probability mass. -/
theorem related_builder (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (left right : PqxdhLaterChallengeBuilderCoupling.Outcome
      (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Bool) (Local := Local) (S := S) (B := B))
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary left right) :
    builderKey left = builderKey right := by
  rcases related with ⟨callback, state, rfl, rfl⟩ | ⟨left, right, rfl, rfl, wrapper⟩
  · rcases callback with ⟨original, trace, origin⟩
    rcases original with (record | finish) | builder <;> rfl
  · cases left <;> cases right <;> rfl

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderObservation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderObservation.related_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderObservation.related_builder
