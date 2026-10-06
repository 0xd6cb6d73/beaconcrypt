-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule

/-! The literal generated-or-supplied Server constructor starts the complete receipt-annotated source schedule. Historical receipts arise from actual Beacon births and signing attempts; they are private analysis only and do not change any constructor, source command or continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointAttemptLedger PqxdhRegistrationJointAttemptInvariant
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointServerBirth (ClientCreated encode)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

abbrev Outcome (KemSK Result : Type) := ClientCreated Unit × Result × State KemSK

def erase (result : Outcome KemSK Result) : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result :=
  (result.1, result.2.1, result.2.2.1)

/-- The same literal Server initialization and same complete adaptive native schedule, retaining only an additional private constructor/attempt ledger. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    StateT (PqxdhRegistrationJointServerPrefix.State KemSK A) ProbComp (Option (Outcome KemSK Result)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
      (fun result => (some (encode created, result.1, result.2), (result.2.1.pool, born.2.2))) <$>
        (simulateQ (handler setup codec checks created.seed created.server.server.metadata.identityIndex) work).run
          (initial (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared))

/-- Erasing the ledger retains the entire original initialized source distribution, including the constructor origin, rejection, all private/native state and the adaptive final result. -/
theorem source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => (result.1.map erase, result.2)) <$> (run setup codec checks ensureInit supplied work).run state =
      (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run state := by
  simp only [run, PqxdhRegistrationJointInitializedSchedule.source, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · rfl
  · simpa only [StateT.run, Functor.map_map, erase, initial, Option.map_some] using congrArg
      (fun execution => (fun result : Result × PqxdhRegistrationJointSchedule.State KemSK =>
        (some (encode created, result.1, result.2), (result.2.pool, after.2))) <$> execution)
      (PqxdhRegistrationJointAttemptLedger.program_source setup codec checks created.seed created.server.server.metadata.identityIndex work
        (initial (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared)))

/-- Generated and imported Server initialization issue no signature; the complete prior signing history stays unchanged. -/
theorem install_messages {P : Type} (created : PqxdhLiveServerConstruction.Created P)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (index : Nat) :
    messagesAt index (PqxdhRegistrationJointServerBirth.install created pool).1.transcript =
      messagesAt index pool.1.transcript := by
  cases origin : created.origin <;>
    simp [PqxdhRegistrationJointServerBirth.install, origin, PqxdhDynamicIdentityPool.record,
      messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]

/-- The actual complete initialized execution derives the receipt invariant from constructor order and source commands, for generated or caller-supplied Server origin. -/
theorem invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state after : PqxdhRegistrationJointServerPrefix.State KemSK A) (outcome : Outcome KemSK Result)
    (unsigned : ∀ index, messagesAt index state.1.1.transcript = [])
    (supported : (some outcome, after) ∈ support ((run setup codec checks ensureInit supplied work).run state)) :
    Invariant setup outcome.2.2 := by
  simp only [run, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, member, reached⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached
  · simp only [support_map, Set.mem_image] at reached
    obtain ⟨returned, continued, equal⟩ := reached
    have outcomeEqual : outcome = (encode created, returned.1, returned.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [outcomeEqual]
    apply PqxdhRegistrationJointAttemptSchedule.program_invariant setup codec checks created.seed
      created.server.server.metadata.identityIndex work _ returned _ continued
    apply initial_invariant setup born.1 (PqxdhRegistrationSchedule.initial created).shared
    intro index
    rw [(PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId supplied state born created member).1,
      install_messages, unsigned]

/-- Starting from the actual empty private service pools discharges every constructor/signing-history premise for the full initialized source run. -/
theorem generated_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (runtime : A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A) (outcome : Outcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((run setup codec checks ensureInit supplied work).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    Invariant setup outcome.2.2 :=
  invariant setup codec checks ensureInit supplied work _ after outcome (fun _ => rfl) supported

/-- Every actual original initialized source result has a same-execution private ledger witness satisfying the derived constructor and issued-attempt invariant. This is a support witness of the full source run, not an assumed history reconstruction. -/
theorem source_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (runtime : A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    ∃ ledger, (some (outcome.1, outcome.2.1, (outcome.2.2, ledger)), after) ∈
      support ((run setup codec checks ensureInit supplied work).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) ∧
      Invariant setup (outcome.2.2, ledger) := by
  rw [← source, support_map] at supported
  obtain ⟨⟨(_ | annotated), final⟩, member, equal⟩ := supported
  · simp only [Option.map_none, Prod.mk.injEq, reduceCtorEq, false_and] at equal
  · simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    exact ⟨annotated.2.2.2, member,
      generated_invariant setup codec checks ensureInit supplied work runtime final annotated member⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.install_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.install_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.generated_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.generated_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.source_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInitialized.source_witness
