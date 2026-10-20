-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands

/-! Actual Server construction precedes the complete source command scheduler. The selected KEM reservation starts with the constructor's unchanged empty KEM pool; generated and imported identity origins, rejection and runtime state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option linter.deprecated false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization
open PqxdhKemIndCca PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhRegistrationJointKemCommands (SourceSpec Budget)
open PqxdhRegistrationJointServerPrefix (State)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Neither generated nor caller-known initialization touches the KEM pool or its full service transcript. -/
theorem constructor_kem (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (state after : State KemSK A) (created : Option (ClientCreated Unit))
    (supported : (created, after) ∈ support
      ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
        (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run state)) :
    after.1.2 = state.1.2 := by
  rw [PqxdhRegistrationJointServerBirth.client_source] at supported
  simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨⟨actual, native⟩, _, equality⟩ := supported
  have same := congrArg (fun value => value.2.1.2) equality
  cases actual <;> exact same.symm

/-- Reinstall exactly the complete interpreted command result, private pools and constructor runtime. Outer reservation refusal remains an explicit absent result. -/
def finish (created : ClientCreated Unit) (runtime : A)
    (result : Option (PqxdhRegistrationJointKemCommands.Outcome KemSK Result) × PqxdhLiveKemBirth.State KemSK) :
    Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A :=
  (result.1.map (fun answer => (created, answer.1.1, ⟨result.2, answer.2, answer.1.2⟩)), (result.2, runtime))

/-- Complete monitored source commands after the actual initializer. The reserved selected key remains in the private interpreter and does not become a client argument. -/
noncomputable def commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (created : ClientCreated Unit) (client : OracleComp (SourceSpec KemSK) Result)
    (joint : PqxdhDynamicIdentityPool.SourceState) (runtime : A)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A) :=
  finish created runtime <$> (Prod.map id (PqxdhDynamicKemJointSource.project pairs) <$>
    (((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected pairs)
      (PqxdhRegistrationJointKemCommands.program setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity client [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
          (joint, PqxdhDynamicKemRouter.empty)))

/-- Reserve one chosen creation and every remaining bounded creation after literal Server initialization. Ordinary initialization failure remains unchanged. -/
noncomputable def reserved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (count : Nat) (selected : Fin (count + 1)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created => do
    let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    commands setup codec checks created client born.2.1.1 born.2.2 selected.val
      (List.ofFn (selected.insertNth chosen others))

/-- Whole actual initialized source-client equality to the concrete bounded reservation. The constructor's preserved empty KEM pool and all source caps are derived, without conditioning on any successful or honest owner. -/
theorem initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (empty : state.1.2 = PqxdhLiveKemBirth.empty) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (room : budget (.inl 1) ≤ count + 1) :
    𝒮[(PqxdhRegistrationJointInitializedSchedule.client setup codec checks ensureInit supplied client).run state] =
      𝒮[reserved setup codec checks ensureInit supplied client state count selected] := by
  simp only [PqxdhRegistrationJointInitializedSchedule.client, StateT.run, reserved]
  apply evalSPMF_bind_congr
  rintro ⟨(_ | created), after⟩ supported
  · rfl
  · have emptyAfter := (constructor_kem setup ensureInit supplied state after (some created) supported).trans empty
    dsimp only
    rw [← PqxdhRegistrationJointOpenBackend.execute_run]
    simp only [PqxdhRegistrationJointOpenBackend.execute, PqxdhRegistrationJointOpenBackend.run,
      PqxdhRegistrationJointInitializedSchedule.initial, Functor.map_map]
    have source := PqxdhRegistrationJointKemCommands.selected_source setup codec checks
      created.server.server.metadata.identityIndex created.publicIdentity client budget certified []
      (PqxdhRegistrationJointInitializedAccept.initial created) after.1.1 count selected room
    have mapped := congrArg (fun distribution => finish created after.2 <$> distribution) source
    simpa only [← evalSPMF_map, Functor.map_map, map_bind, finish, Option.map_some,
      commands, PqxdhRegistrationJointKemCommands.program, ← emptyAfter, Prod.mk.eta] using mapped

/-- Selected-key-first mathematical source game. The actual initializer still keeps its complete runtime, rejection and generated/imported origin before any source command executes. -/
noncomputable def selectedFirst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (count : Nat) (selected : Fin (count + 1)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A) := do
  let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    commands setup codec checks created client born.2.1.1 born.2.2 selected.val
      (List.ofFn (selected.insertNth chosen others))

/-- The selected generator moves across the complete actual constructor and evaluated continuation. Failed initialization merely discards a lossless extra draw; this equality does not claim that draw is free. -/
theorem constructor_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (count : Nat) (selected : Fin (count + 1)) :
    𝒮[reserved setup codec checks ensureInit supplied client state count selected] =
      𝒮[selectedFirst setup codec checks ensureInit supplied client state count selected] := by
  rw [selectedFirst, ← PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy]
  unfold reserved
  apply evalSPMF_bind_congr'
  rintro ⟨(_ | created), after⟩
  · exact (OracleComp.ProgramLogic.Relational.evalSPMF_bind_const_of_no_failure _ _).symm
  · rfl

/-- Whole actual initialized source-client distribution with its selected KEM creation drawn first. Complete generator-order interchange and source counts, rather than marginal key equality, justify the embedding. -/
theorem initialized_first (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (empty : state.1.2 = PqxdhLiveKemBirth.empty) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (room : budget (.inl 1) ≤ count + 1) :
    𝒮[(PqxdhRegistrationJointInitializedSchedule.client setup codec checks ensureInit supplied client).run state] =
      𝒮[selectedFirst setup codec checks ensureInit supplied client state count selected] :=
  (initialized setup codec checks ensureInit supplied client state empty budget certified count selected room).trans
    (constructor_order setup codec checks ensureInit supplied client state count selected)

/-- Literal source constructor and source command execution have the same complete encoded distribution as the selected-first game. Only the already proved owner encoding is applied; all actual private pools, histories and runtime remain. -/
theorem actual_source_first (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (state : State KemSK A)
    (empty : state.1.2 = PqxdhLiveKemBirth.empty) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (room : budget (.inl 1) ≤ count + 1) :
    𝒮[(fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
      (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied client).run state] =
      𝒮[selectedFirst setup codec checks ensureInit supplied client state count selected] := by
  rw [← PqxdhRegistrationJointInitializedSchedule.initialized_source]
  exact initialized_first setup codec checks ensureInit supplied client state empty budget certified count selected room

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.constructor_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.constructor_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.constructor_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.constructor_order

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.initialized_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.initialized_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.actual_source_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization.actual_source_first
