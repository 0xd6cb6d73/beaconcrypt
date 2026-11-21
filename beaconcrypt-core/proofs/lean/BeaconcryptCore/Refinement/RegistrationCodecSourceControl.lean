-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCodecControlNormalization

/-! The source preparer records the exact typed statements, Boolean conditions and terminal expressions of each generated control fragment. This syntax gives each unchanged statement an arbitrary effect on the complete local environment. The certificate proves continuation distribution for that concrete syntax without assuming a codec law. The source checker must separately reconstruct both original and prepared Rust from the recorded transformation. -/

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.RegistrationCodecSourceControl

universe v

structure Statement where
  binding : String
  rustType : String
  expression : String
  source : String

inductive Control where
  | done (value : Bool)
  | statement (work : Statement) (next : Control)
  | branch (condition : String) (yes no : Control)
  | expression (source : String)

structure Semantics (m : Type → Type v) (Environment : Type) where
  statement : Statement → Environment → m Environment
  boolean : String → Environment → m (Bool × Environment)

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {Environment Result : Type}

open RegistrationCodecControlNormalization

def controlTree (semantics : Semantics m Environment) :
    Control → Environment → Tree m (Bool × Environment)
  | .done value, environment => .done (value, environment)
  | .statement work next, environment =>
      .leaf (semantics.statement work environment) (controlTree semantics next)
  | .branch condition yes no, environment =>
      .leaf (semantics.boolean condition environment) fun result =>
        .branch result.1 (controlTree semantics yes result.2)
          (controlTree semantics no result.2)
  | .expression source, environment =>
      .leaf (semantics.boolean source environment) Tree.done

theorem fragment_preserved (source : Control) (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics source environment) =
      evaluate (controlTree semantics source environment) >>= next :=
  cps_preserves _ _

end BeaconcryptCore.Refinement.RegistrationCodecSourceControl

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceControl.fragment_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceControl.fragment_preserved
