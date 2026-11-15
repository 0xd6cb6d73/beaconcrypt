-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompile
import BeaconcryptCore.Computational.CborAdmissionCompileGame
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! The raw-CBOR source model's secrecy ledger runs above the public compiler. Raw public replies, transcript entries, hidden-bit draws and fresh-message bytes are therefore exactly the modeled native ones, at the same positions. Generated initialization, every failure state, the complete ledger and every event transfer to the initialized source14 program. These are Lean source-model equalities under the stated codec and primitive contracts; they do not verify the external CBOR parser, concrete primitives or the reviewed Rust adapter transcriptions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawCompileSecrecy
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FullSpec ModeSpec Mode Budget FreshBounds asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentCompileBudget (cost)
open PqxdhDeploymentCompileSecrecy (wrapCost)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X Y : Type} {baseSpec : OracleSpec ι}

noncomputable def handler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.State KemSK) ProbComp) :=
  ((CborProductionBoundary.handler setup wire parse checks seed).mapStateTBase
    (ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds)).flattenStateT

theorem run_wrap (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (work : OracleComp FullSpec X) (state : PqxdhDeploymentNative.State KemSK) :
    (simulateQ (handler setup wire parse checks seed bounds) work).run (Ledger.empty, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (CborProductionBoundary.handler setup wire parse checks seed)
          (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds work)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [handler]
  exact (id_map _).symm

noncomputable def game (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (handler setup wire parse checks created.seed bounds) (asModeO mode adversary)).run
        (Ledger.empty, PqxdhDeploymentNative.initial created)

noncomputable def compileFull (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) ((X × Ledger) × CborAdmissionCompiler.Local) :=
  CborRawCompile.compile setup wire parse
    (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary))

def mergeFull (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK
    ((X × Ledger) × CborAdmissionCompiler.Local)) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1.1.1,
    (result.2.1.1.2, CborAdmissionCompiler.merge result.2.1.2 result.2.2)), outcome.2)

/-- The complete generated raw-CBOR experiment is the public compiled source14 execution, preserving every returned value, ledger entry and state field. -/
theorem compile_full_game (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    mergeFull <$> (PqxdhRegistrationJointInitializedSchedule.native setup (CborRawCompile.sourceCodec wire parse)
      checks ensureInit identityIndex none (compileFull setup wire parse bounds mode adversary)).run runtime =
      (game setup wire parse checks ensureInit identityIndex bounds mode adversary).run runtime := by
  simp only [PqxdhRegistrationJointInitializedSchedule.native, game, StateT.run, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | created, after⟩ born
  · simp only [map_pure, mergeFull, Option.map_none]
  · dsimp only
    obtain ⟨sender, lastId, _⟩ := CborAdmissionCompileGame.construct_fields setup.joint ensureInit identityIndex
      setup.serverKeyId runtime created after born
    have compiled := CborRawCompile.compile_native setup wire parse checks lengths parser created.seed phase1 phase2
      (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary))
      (PqxdhRegistrationSchedule.initial created) sender lastId (fun _ => rfl) rfl (fun _ => rfl)
    have wrapped := run_wrap setup wire parse checks created.seed bounds (asModeO mode adversary)
      (PqxdhDeploymentNative.initial created)
    simp only [StateT.run] at wrapped compiled
    rw [wrapped]
    simp only [PqxdhDeploymentNative.initial, compileFull]
    rw [← compiled]
    simp only [Functor.map_map]
    rfl

/-- The same equality reaches the annotated source14 execution used by the existing registration reductions. -/
theorem compile_full_source (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeFull (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)) <$>
      (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks
        ensureInit none (compileFull setup wire parse bounds mode adversary)).run state =
      (game setup wire parse checks ensureInit state.1.1.seeds.length bounds mode adversary).run state.2 := by
  rw [← compile_full_game setup wire parse checks lengths parser ensureInit state.1.1.seeds.length
    phase1 phase2 bounds mode adversary state.2,
    ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup (CborRawCompile.sourceCodec wire parse)
      checks ensureInit none (compileFull setup wire parse bounds mode adversary) state, Functor.map_map]

/-- Every full-outcome observation transfers exactly. This includes the actual raw transcript and the native fresh-message ledger used by the named events. -/
theorem observe_game (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (observe : (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK) × A) → Y) :
    observe <$> (game setup wire parse checks ensureInit identityIndex bounds mode adversary).run runtime =
      (observe ∘ mergeFull) <$>
        (PqxdhRegistrationJointInitializedSchedule.native setup (CborRawCompile.sourceCodec wire parse) checks
          ensureInit identityIndex none (compileFull setup wire parse bounds mode adversary)).run runtime := by
  rw [← compile_full_game setup wire parse checks lengths parser ensureInit identityIndex phase1 phase2
    bounds mode adversary runtime, Functor.map_map]
  rfl

/-- Event probabilities agree by the proved full-outcome equality; there is no event-correspondence premise and no success conditioning. -/
theorem prob_event (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (event : (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK) × A) → Bool) :
    𝒟[event <$> (game setup wire parse checks ensureInit identityIndex bounds mode adversary).run runtime] {true} =
      𝒟[(event ∘ mergeFull) <$>
        (PqxdhRegistrationJointInitializedSchedule.native setup (CborRawCompile.sourceCodec wire parse) checks
          ensureInit identityIndex none (compileFull setup wire parse bounds mode adversary)).run runtime] {true} := by
  rw [observe_game setup wire parse checks lengths parser ensureInit identityIndex phase1 phase2
    bounds mode adversary runtime event]

theorem compile_full_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (kind : SourceKind) :
    (compileFull setup wire parse bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full) :=
  CborRawCompile.compile_bound setup wire parse _ _
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto (boundaryWire wire parse)
      setup.serverKeyId bounds mode adversary budget respects core) kind

/-- The public compiler reads no identity, KEM, prekey or one-time field, independently of the adversary's budget. -/
theorem compile_full_unread (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (field : Fin 5) (notKernel : field ≠ 4) :
    (compileFull setup wire parse bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr field) 0 := by
  have zero : ∀ core, cost (.inr field) core = 0 := fun core => by
    fin_cases core <;> simp [cost, PqxdhDeploymentCompileBudget.unit, notKernel]
  exact PqxdhDeploymentCompileSecrecy.simulate_zero (CborRawCompile.compileImpl setup wire parse) _
    (fun query memory => by simpa only [zero] using
      CborRawCompile.step_bound setup wire parse (.inr field) query memory) _
    (CborAdmissionCompiler.Local.empty setup.serverKeyId)

end BeaconcryptCore.Computational.CborRawCompileSecrecy

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_source

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_bound

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.run_wrap

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_game

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.observe_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.observe_game

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.prob_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.prob_event

/-- info: 'BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompileSecrecy.compile_full_unread
