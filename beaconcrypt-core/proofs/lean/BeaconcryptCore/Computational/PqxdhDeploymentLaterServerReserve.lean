-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut

/-! LQ-F: the selected-first KEM reservation for the logged source. The hidden logged command program (`commands` of the logged source under the actual encapsulator) is the simulation of one flattened handler (`flat`, `run_flat`). Every source14 request of that handler issues the KEM creations of the same request in the existing command compiler (`step_source`, through `LaterServerCommands.query_embed` and `KemEncapsulation.program_actual`), so at most one for a Beacon creation and none otherwise, and the Server read issues one identity-pool reveal and no KEM creation (`step_later`). Hence the hidden logged program has at most as many KEM creations as the program has Beacon creations (`creations`), and the generic selected-first reservation `PqxdhDynamicKemJointSource.selected_source` holds for it with the creation cap derived from the source budget (`selected_source`). This re-proves, for the logged source, the content of `KemCommands.creations` and `KemCommands.selected_source`; the initialized form, the counterpart of `KemInitialization.actual_source_first`, is `LaterServerInitialized.actual_source_first`, which adds the correspondence between the logged annotated source and the logged command compiler (`LaterServerInitialized.program_source`). No assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhDeploymentLaterServerSource (Log Spec)
open PqxdhDeploymentLaterServerCommands (Local impl commands)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The source kind of a logged-source request: the source14 kind, and `none` for the Server read. -/
def laterKind : (Spec KemSK).Domain → Option PqxdhRegistrationJointRevealCosts.SourceKind
  | .inl query => some (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query)
  | .inr _ => none

/-- The hidden logged command handler with owners, log and native state flattened into one state. -/
noncomputable def flat (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (Spec KemSK) (StateT (Local × NativeState KemSK) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))) :=
  fun query state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    simulateQ (actual setup) (((impl setup codec checks identityIndex publicIdentity query).run state.1).run state.2)

/-- One step of the flattened handler. -/
theorem flat_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (query : (Spec KemSK).Domain)
    (state : Local × NativeState KemSK) :
    (flat setup codec checks identityIndex publicIdentity query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        simulateQ (actual setup) (((impl setup codec checks identityIndex publicIdentity query).run state.1).run state.2) :=
  rfl

/-- The hidden logged run is the simulation of the flattened handler. -/
theorem run_flat (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (held : Local) (state : NativeState KemSK) :
    simulateQ (actual setup) (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
      work held.1 held.2 state) =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (flat setup codec checks identityIndex publicIdentity) work).run (held, state) := by
  induction work using OracleComp.inductionOn generalizing held state with
  | pure value => simp [PqxdhDeploymentLaterServerCommands.run]
  | query_bind query next ih =>
    simp only [PqxdhDeploymentLaterServerCommands.run] at ih ⊢
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, flat_run, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 result.2

/-- Every source14 request of the flattened handler issues the KEM creations of the same request in the existing command compiler: at most one for a Beacon creation and none otherwise. -/
theorem step_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (held : Local) (state : NativeState KemSK) :
    ((flat setup codec checks identityIndex publicIdentity (.inl query)).run (held, state)).IsQueryBoundP
      (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK))
      (if PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 1 then 1 else 0) := by
  have embedded := PqxdhDeploymentLaterServerCommands.query_embed setup codec checks identityIndex publicIdentity query
    held.1 held.2 state
  have hidden := congrArg (simulateQ (actual setup)) embedded
  rw [simulateQ_map, PqxdhRegistrationJointKemEncapsulation.program_actual] at hidden
  have single := PqxdhRegistrationJointKemCommands.creations setup codec checks identityIndex publicIdentity
    ((PqxdhRegistrationJointKemCommands.SourceSpec KemSK).query query)
    (fun source => if PqxdhRegistrationJointRevealCosts.sourceKind query = source then 1 else 0)
    (fun source => by
      rw [isQueryBoundP_query_iff]
      split_ifs with same <;> simp [same])
    held.1 state
  simp only [PqxdhRegistrationJointKemCommands.program, PqxdhRegistrationJointOpenBackend.compile,
    simulateQ_spec_query] at single
  rw [← hidden, isQueryBoundP_map_iff] at single
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$> simulateQ (actual setup)
    (((impl setup codec checks identityIndex publicIdentity (.inl query)).run (held.1, held.2)).run state)).IsQueryBoundP
      _ _
  rw [isQueryBoundP_map_iff]
  exact single

/-- The Server read issues one identity-pool reveal and no KEM creation. -/
theorem step_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (read : Unit) (held : Local) (state : NativeState KemSK) :
    ((flat setup codec checks identityIndex publicIdentity (.inr read)).run (held, state)).IsQueryBoundP
      (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$> simulateQ (actual setup)
    ((fun seed => (((seed, held.2), held), state)) <$>
      ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inl (.inl (.inr (.reveal identityIndex)))) :
        OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Option IdentitySeed)))).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff, simulateQ_map, isQueryBoundP_map_iff, simulateQ_spec_query]
  simp [PqxdhRegistrationJointKemEncapsulation.actual, PqxdhLiveKemReservation.IsCreate]

/-- The hidden logged command program has at most as many KEM creations as the logged-source program has Beacon creations, for every owner list, log and native state. -/
theorem creations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inl 1)) cap)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
      state)).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) cap := by
  rw [commands, simulateQ_map, run_flat setup codec checks identityIndex publicIdentity work (owners, log) state,
    Functor.map_map, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · rintro (query | read) create ⟨held, native⟩
    · have step := step_source setup codec checks identityIndex publicIdentity query held native
      simp only [laterKind, Option.some.injEq] at create
      rwa [ite_eq_left create] at step
    · simp [laterKind] at create
  · rintro (query | read) other ⟨held, native⟩
    · have step := step_source setup codec checks identityIndex publicIdentity query held native
      simp only [laterKind, Option.some.injEq] at other
      rwa [ite_eq_right other] at step
    · exact step_later setup codec checks identityIndex publicIdentity read held native

/-- The selected-first reservation for the logged source: the hidden logged command program under the actual KEM pool has the distribution of the selected-first monitored KEM source, with the creation cap derived from the source budget. -/
theorem selected_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1))
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK)
    (joint : PqxdhDynamicIdentityPool.SourceState) (selected : Fin (count + 1)) :
    EvalDistEq ((fun result => (some result.1, result.2)) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log state))).run
          (joint, PqxdhLiveKemBirth.empty))
      (do
        let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
        let others ← PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
        let pairs := List.ofFn (selected.insertNth chosen others)
        Prod.map id (PqxdhDynamicKemJointSource.project pairs) <$>
          (((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected.val pairs)
            (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
              state))).run).run (joint, PqxdhDynamicKemRouter.empty))) :=
  PqxdhDeploymentLaterServerCut.selected_first setup codec checks identityIndex publicIdentity work owners log state
    joint count selected (creations setup codec checks identityIndex publicIdentity work (count + 1) bounded owners log state)

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.flat_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.flat_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.run_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.run_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.step_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.step_later

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.creations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.creations

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve.selected_source
