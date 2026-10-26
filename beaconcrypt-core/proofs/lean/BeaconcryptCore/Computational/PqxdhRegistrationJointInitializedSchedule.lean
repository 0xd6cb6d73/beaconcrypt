-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient

/-! Actual Server construction feeds the complete adaptive one-Server/many-Beacon scheduler. Generated and caller-known initialization remain distinct, every public request and current-field reveal is preserved, and all ownership facts arise from the same execution. This is operational correspondence under the existing native primitive interpretation, not a cryptographic hop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServerBirth (ClientCreated encode)
open PqxdhRegistrationJointServerPrefix (State)
open PqxdhRegistrationJointGeneratedFinish (EncodedState encodeState)
open PqxdhRegistrationJointRevealSchedule (Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Private analysis retains the initialization origin, adaptive decision and complete encoded poststate. This record is not an additional adversary reply. -/
abbrev Outcome (KemSK Result : Type) := ClientCreated Unit × Result × EncodedState KemSK

/-- Source analysis additionally retains literal native owners alongside the private service pool. -/
abbrev SourceOutcome (KemSK Result : Type) := ClientCreated Unit × Result × PqxdhRegistrationJointSchedule.State KemSK

def encodeOutcome (setup : Setup baseSpec KemSK) (result : SourceOutcome KemSK Result) : Outcome KemSK Result :=
  (result.1, result.2.1, encodeState setup result.2.2)

def initial (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (created : ClientCreated Unit) : EncodedState KemSK :=
  ⟨pool, PqxdhRegistrationJointInitializedAccept.initial created, []⟩

/-- The client starts from exactly the encoded source initialization, including the complete shared state and empty owner registry. -/
theorem initial_encode (setup : Setup baseSpec KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    initial pool (encode created) = encodeState setup
      (PqxdhRegistrationJointSchedule.initial pool (PqxdhRegistrationSchedule.initial created).shared) := by
  rfl

/-- Actual initialized public-service client, with no generated Server seed argument. Constructor rejection and every adaptive source command remain ordinary outcomes. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) : StateT (State KemSK A) ProbComp (Option (Outcome KemSK Result)) := fun state => do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client (P := Unit) setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (created, result.1, result.2), (result.2.pool, born.2.2))) <$>
      PqxdhRegistrationJointServerClient.execute setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program)
          (initial born.2.1 created)

/-- The same constructor followed by all actual source commands; its seed stays inside this private mathematical interpretation. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) : StateT (State KemSK A) ProbComp (Option (SourceOutcome KemSK Result)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (encode created, result.1, result.2), (result.2.pool, born.2.2))) <$>
      (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks created.seed
        created.server.server.metadata.identityIndex) program).run
          (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared)

/-- The whole initialized adaptive execution equals the full encoded source run. Its representation premises follow from the actual generated or imported constructor and remain valid across every reached command. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) (state : State KemSK A) :
    (client setup codec checks ensureInit supplied program).run state =
      (fun result => (result.1.map (encodeOutcome setup), result.2)) <$>
        (source setup codec checks ensureInit supplied program).run state := by
  have born := PqxdhRegistrationJointServerBirth.client_source (P := Unit) setup ensureInit setup.serverKeyId supplied state
  simp only [StateT.run] at born
  simp only [client, source, StateT.run, born, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨(_ | created), after⟩ supported
  · rfl
  · simp only [Option.map_some, initial_encode setup]
    have owned : PqxdhRegistrationJointServerSchedule.Owned created.seed created.server.server.metadata.identityIndex
        (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨by simp [PqxdhRegistrationJointSchedule.Invariant, PqxdhRegistrationJointSchedule.initial],
        PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state after created supported⟩
    simp only [encode]
    rw [PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId supplied state after created supported]
    rw [PqxdhRegistrationJointServerClient.program_source setup codec checks created.seed created.server.server.metadata.identityIndex program _ owned]
    simp only [Functor.map_map, encodeOutcome, encodeState, Option.map_some, StateT.run]

/-- Erasure removes only the service pool, private histories and owner service indices. Every literal native owner and the complete shared state remain. -/
abbrev NativeOutcome (KemSK Result : Type) := ClientCreated Unit × Result × PqxdhRegistrationSchedule.State KemSK

def eraseOutcome (result : SourceOutcome KemSK Result) : NativeOutcome KemSK Result :=
  (result.1, result.2.1, PqxdhRegistrationJointSchedule.source result.2.2)

/-- Actual source constructor and the original adaptive native scheduler, including current-field reads and every optional command reply. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) : StateT A ProbComp (Option (NativeOutcome KemSK Result)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId supplied).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (encode created, result), born.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed) program).run
        (PqxdhRegistrationSchedule.initial created)

/-- The retained source witness is the actual initialized native experiment after erasing only service annotations. Combined with initialized_source, it relates the seedless executable client and native source through the same complete annotated run. -/
theorem initialized_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) (state : State KemSK A) :
    (fun result => (result.1.map eraseOutcome, result.2.2)) <$>
      (source setup codec checks ensureInit supplied program).run state =
        (native setup codec checks ensureInit state.1.1.seeds.length supplied program).run state.2 := by
  simp only [source, native, PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨(_ | created), runtime⟩
  · rfl
  · simpa only [StateT.run, Functor.map_map, eraseOutcome, Option.map_some,
      PqxdhRegistrationJointSchedule.source, PqxdhRegistrationJointSchedule.initial, PqxdhRegistrationSchedule.initial, List.map_nil] using congrArg
      (fun work => (fun result => (some (encode created, result), runtime)) <$> work)
      (PqxdhRegistrationJointServerSchedule.program_native setup codec checks created.seed
        created.server.server.metadata.identityIndex program
        (PqxdhRegistrationJointSchedule.initial (PqxdhRegistrationJointServerBirth.install created state.1)
          (PqxdhRegistrationSchedule.initial created).shared))

/-- The actual constructor and whole native adaptive schedule retain their complete evaluated uniform budget, including all rejected attempts, public primitive calls and initialization work. -/
theorem native_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (identityIndex : Nat) (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) :
    ((native setup codec checks ensureInit identityIndex supplied program).run runtime).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + ∑ source, PqxdhRegistrationJointRevealCosts.uniformCost caps source * budget source) := by
  simp only [native, StateT.run]
  apply isTotalQueryBound_bind (PqxdhLiveServerConstruction.construct_uniform setup.joint ensureInit qInit initBound
    identityIndex setup.serverKeyId supplied runtime)
  rintro ⟨(_ | created), after⟩
  · trivial
  · simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      (isQueryBoundP_true_iff _ _).mp
        (FinitePartitionQueryBounds.weighted_bound (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK))
          (PqxdhRegistrationJointRevealCosts.uniformCost caps) budget
          (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed) (fun _ => True)
          program certified (fun query before =>
            (PqxdhRegistrationJointRevealCosts.query_uniform setup codec checks created.seed caps bounded query before).isQueryBoundP)
          (PqxdhRegistrationSchedule.initial created))

/-- The same complete bill holds for the actual seedless initialized client, not merely a projected final answer. Mapping the complete source/native outputs preserves the entire underlying uniform request tree. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (program : OracleComp (Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (state : State KemSK A) :
    ((client setup codec checks ensureInit supplied program).run state).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + ∑ source, PqxdhRegistrationJointRevealCosts.uniformCost caps source * budget source) := by
  have nativeBound := native_uniform setup codec checks ensureInit qInit initBound caps bounded
    state.1.1.seeds.length supplied program budget certified state.2
  rw [← initialized_native setup codec checks ensureInit supplied program state] at nativeBound
  simpa only [initialized_source, IsTotalQueryBound, isQueryBound_map_iff] using nativeBound

/-- Every completed initialized source execution retains the constructor's exact indexed Server identity and every current Beacon owner. This representation fact follows from actual support, even after arbitrary public scheduling and permitted reads. -/
theorem source_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (Spec KemSK) Result) (state after : State KemSK A) (result : SourceOutcome KemSK Result)
    (supported : (some result, after) ∈ support ((source setup codec checks ensureInit supplied program).run state)) :
    ∃ seed, result.1.publicIdentity = setup.joint.publicKeys seed ∧
      PqxdhRegistrationJointServerSchedule.Owned seed result.1.server.server.metadata.identityIndex result.2.2 := by
  simp only [source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), bornState⟩, born, reached⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, rfl⟩ := reached
    refine ⟨created.seed, PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit
      setup.serverKeyId supplied state bornState created born, ?_⟩
    exact PqxdhRegistrationJointServerSchedule.program_invariant setup codec checks created.seed
      created.server.server.metadata.identityIndex program _ finished
      ⟨by simp [PqxdhRegistrationJointSchedule.Invariant, PqxdhRegistrationJointSchedule.initial],
        PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state bornState created born⟩ member

end BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initial_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initial_encode

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.native_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.initialized_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.source_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule.source_owned
