-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend

/-! The actual initialized adaptive command program with joint identity/KEM requests left open. Runtime initialization and caller-known imports retain their existing local constructor interface; generated seeds never enter the compiled client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhRegistrationJointServerPrefix (State)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

abbrev Spec (KemSK : Type) := PqxdhRegistrationJointServerBirth.Spec KemSK
abbrev Outcome (KemSK Result : Type) := ClientCreated Unit × Result × NativeState KemSK × List EncodedEntry

def poolLift : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inl query)

/-- Forwarding the complete service program through the constructor interface retains its exact private pools and the entire runtime coordinate. -/
theorem lifted_run (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : State KemSK A) :
    (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit) (simulateQ poolLift program)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) program).run state.1 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, poolLift, StateT.run_bind,
        PqxdhRegistrationJointServerBirth.impl]
      simp only [ih]
      simp only [PqxdhRegistrationJointServerPrefix.onPool, StateT.run, bind_map_left, map_bind]
      rfl

/-- The actual constructor followed by the actual adaptive source-command client. Only generated public handles and caller-known supplied material enter this open program. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    OracleComp (Spec KemSK) (Option (Outcome KemSK Result)) := do
  let born ← PqxdhRegistrationJointServerBirth.client (P := Unit) setup.serverKeyId supplied
  match born with
  | none => pure none
  | some created =>
    (fun result => some (created, result.1.1, result.2, result.1.2)) <$>
      simulateQ poolLift
        ((PqxdhRegistrationJointOpenBackend.compile setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) []).run
            (PqxdhRegistrationJointInitializedAccept.initial created))

/-- Reattach only interpreter-private representation state to the retained analysis output; this does not add an adversary observation. -/
def attach (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (result : Outcome KemSK Result) :
    PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result :=
  (result.1, result.2.1, ⟨pool, result.2.2.1, result.2.2.2⟩)

/-- Final interpretation supplies runtime initialization, known imports and the ordinary private identity/KEM services, retaining every final coordinate. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK A) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A) :=
  (fun result => (result.1.map (attach result.2.1), result.2)) <$>
    (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
      (client setup codec checks supplied program)).run state

/-- The complete open initialized program is exactly the already checked actual initialized scheduler after private interpretation. All constructor failures, full state and origin records stay in the same run. -/
theorem initialized_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK A) :
    run setup codec checks ensureInit supplied program state =
      (PqxdhRegistrationJointInitializedSchedule.client setup codec checks ensureInit supplied program).run state := by
  simp only [run, client, simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, Option.map_none]
  · simp only [simulateQ_map, StateT.run_map, lifted_run]
    rw [← PqxdhRegistrationJointOpenBackend.execute_run]
    simp only [PqxdhRegistrationJointOpenBackend.execute, PqxdhRegistrationJointOpenBackend.run,
      PqxdhRegistrationJointInitializedSchedule.initial, Functor.map_map, Option.map_some, attach]


/-- Actual source construction and the complete adaptive source commands supply the same whole outcome, private histories and native/runtime state as the open initialized client. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK A) :
    run setup codec checks ensureInit supplied program state =
      (fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run state := by
  rw [initialized_run, PqxdhRegistrationJointInitializedSchedule.initialized_source]

/-- Leaving services open does not erase their eventual work: actual initialization plus every adaptive source attempt keeps the complete evaluated native/base uniform bill. -/
theorem interpreted_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : State KemSK A) :
    ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
      (client setup codec checks supplied program)).run state).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + ∑ source, PqxdhRegistrationJointRevealCosts.uniformCost caps source * budget source) := by
  have bound := PqxdhRegistrationJointInitializedSchedule.initialized_uniform setup codec checks ensureInit qInit
    initBound caps bounded supplied program budget certified state
  rw [← initialized_run] at bound
  simpa only [run, IsTotalQueryBound, isQueryBound_map_iff] using bound

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.lifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.lifted_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.initialized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.initialized_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.initialized_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.interpreted_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitialization.interpreted_uniform
