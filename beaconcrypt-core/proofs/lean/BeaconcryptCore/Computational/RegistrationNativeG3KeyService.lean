-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-! The two actual prepare/demand compilers inline to a descriptor-flag service whose only protected material operation is the original108-byte table query. The inner byte-preparation fact follows from the outer successful descriptor flag; it is not supplied as a protocol security premise. Metadata counters are private analysis fields and remain in the stacked interpretation for their separate bills. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KeyService
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Flags)
open RegistrationNativeKeyPhases (Meta)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeKeyCompiler (KeySpec)
variable {Value : Type}
attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot

abbrev Spec := RegistrationNativeRetainedService.Spec
abbrev State := Flags × Meta

def Valid (input : Message → Option Pqxdh.Bytes) (before : State) : Prop :=
  ∀ message, before.1 message = true → ∃ bytes, input message = some bytes ∧ before.2.prepared bytes = true

private theorem state_map_apply {S Input Result : Type} (f : Input → Result)
    (work : StateT S (OracleComp KeySpec) Input) (before : S) :
    (f <$> work) before = (fun result => (f result.1, result.2)) <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  rw [bind_pure_comp]

def direct (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT Flags (OracleComp KeySpec))
  | .inl coin => StateT.lift (RegistrationNativeKeyCompiler.coins coin)
  | .inr (.prepare message) => fun before =>
      pure ((input message).map (fun _ => message), Function.update before message (input message).isSome)
  | .inr (.demand message) => fun before =>
      if before message then match input message with
      | none => pure (none, before)
      | some bytes => if inside bytes then
          (fun output => (some output, before)) <$> (KeySpec.query (.inr bytes) : OracleComp KeySpec _)
        else pure (some (PqxdhServerAuthKeySchedule.fromRoot source
          (RegistrationNativeRelatedRoot.nativeRoot source bytes)), before)
      else pure (none, before)

def stacked (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State (OracleComp KeySpec)) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeKeyCompiler.compiler source input inside)
      ((RegistrationNativeRetainedService.compiler query).run before.1)).run before.2

/-- The actual cold two-compiler state satisfies the flag/byte-preparation relation without an initial invariant premise. -/
theorem initial_valid (input : Message → Option Pqxdh.Bytes) : Valid input ((fun _ => false), RegistrationNativeKeyPhases.emptyMeta) := by
  intro message impossible
  cases impossible

/-- The actual stacked probability branch forwards its original coin and changes neither flag nor metadata. -/
theorem coin (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : unifSpec.Domain) (before : State) :
    (stacked source input inside (.inl query)).run before =
      (fun reply => (reply, before)) <$> RegistrationNativeKeyCompiler.coins query := by
  simp only [stacked, StateT.run, RegistrationNativeRetainedService.compiler,
    StateT.lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeKeyCompiler.compiler]
  rfl

/-- A successful literal preparation stores its descriptor flag and the actual realized full input in the inner compiler metadata. -/
theorem prepare_some (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (bytes : Pqxdh.Bytes) (realized : input message = some bytes) (before : State) :
    (stacked source input inside (.inr (.prepare message))).run before = pure
      (some message, (Function.update before.1 message true,
        { before.2 with prepared := Function.update before.2.prepared bytes true, prepares := before.2.prepares + 1, roots := before.2.roots + 1 })) := by
  simp only [stacked, StateT.run, StateT.monad_bind_def, StateT.bind, RegistrationNativeRetainedService.compiler,
    simulateQ_bind, simulateQ_spec_query, RegistrationNativeKeyCompiler.compiler,
    RegistrationNativeKeyCompiler.liftProb, RegistrationNativeKeyPhases.prepareMeta,
    realized, simulateQ_pure, pure_bind]
  rfl

/-- Invalid optional DH input is retained as failed preparation and cannot create a descriptor flag. -/
theorem prepare_none (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (realized : input message = none) (before : State) :
    (stacked source input inside (.inr (.prepare message))).run before = pure
      (none, (Function.update before.1 message false, { before.2 with prepares := before.2.prepares + 1 })) := by
  simp only [stacked, StateT.run, StateT.monad_bind_def, StateT.bind, RegistrationNativeRetainedService.compiler,
    simulateQ_bind, simulateQ_spec_query, RegistrationNativeKeyCompiler.compiler,
    RegistrationNativeKeyCompiler.liftProb, RegistrationNativeKeyPhases.prepareMeta,
    realized, simulateQ_pure, pure_bind]
  rfl

/-- An unprepared descriptor is refused before the inner material compiler or any private key table is accessed. -/
theorem demand_unprepared (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : State) (missing : before.1 message = false) :
    (stacked source input inside (.inr (.demand message))).run before = pure (none, before) := by
  simp only [stacked, StateT.run, RegistrationNativeRetainedService.compiler, missing,
    Bool.false_eq_true, ite_false, simulateQ_pure]
  rfl

/-- The protected branch asks exactly the original full-input key oracle after both derived preparation checks. -/
theorem demand_hidden (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (bytes : Pqxdh.Bytes) (before : State)
    (prepared : before.1 message = true) (realized : input message = some bytes)
    (inner : before.2.prepared bytes = true) (protectedInput : inside bytes = true) :
    (stacked source input inside (.inr (.demand message))).run before =
      (fun output => (some output, (before.1, { before.2 with demands := before.2.demands + 1, material := before.2.material + 1 }))) <$> (KeySpec.query (.inr bytes) : OracleComp KeySpec _) := by
  simp only [stacked, StateT.run, state_map_apply, StateT.monad_bind_def, StateT.bind, RegistrationNativeRetainedService.compiler, prepared, ite_true,
    simulateQ_map, simulateQ_spec_query, RegistrationNativeKeyCompiler.compiler,
    RegistrationNativeKeyCompiler.liftProb, RegistrationNativeKeyPhases.demandMeta, realized, inner,
    simulateQ_pure, pure_bind, protectedInput, StateT.lift, bind_pure_comp,
    Functor.map_map]
  rfl

/-- Off-protected requests keep the literal actual source schedule while updating only their real material metadata. -/
theorem demand_known (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (bytes : Pqxdh.Bytes) (before : State)
    (prepared : before.1 message = true) (realized : input message = some bytes)
    (inner : before.2.prepared bytes = true) (outside : inside bytes = false) :
    (stacked source input inside (.inr (.demand message))).run before = pure
      (some (PqxdhServerAuthKeySchedule.fromRoot source (RegistrationNativeRelatedRoot.nativeRoot source bytes)),
        (before.1, { before.2 with demands := before.2.demands + 1, material := before.2.material + 1 })) := by
  simp only [stacked, StateT.run, state_map_apply, StateT.monad_bind_def, StateT.bind, RegistrationNativeRetainedService.compiler, prepared, ite_true,
    simulateQ_map, simulateQ_spec_query, RegistrationNativeKeyCompiler.compiler,
    RegistrationNativeKeyCompiler.liftProb, RegistrationNativeKeyPhases.demandMeta, realized, inner,
    simulateQ_pure, pure_bind, outside, Bool.false_eq_true, ite_false]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeG3KeyService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.initial_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.initial_valid
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.prepare_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.prepare_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.prepare_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.prepare_none
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_unprepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_unprepared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyService.demand_known
