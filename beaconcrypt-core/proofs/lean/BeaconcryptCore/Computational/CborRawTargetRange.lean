-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawKemTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-! The original raw ledger designates only actual accepted sessions and created owners. The concrete raw compiler trace, exact source positional accepts and unchanged secrecy query bills give the tight original accept-times-create target domain. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawTargetRange
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentRegistrationTrace (Logged traceFrom acceptsOf)
open PqxdhDeploymentKemTransfer (Observed registrations observeGame happens designated target)
open PqxdhDeploymentTargetRange (ledger_count classCount accepts_count owners_count designate_created)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Every designation on an actual source raw compiler trace lies below the original accept and create budgets. -/
theorem traced_range_create (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      (((X × Ledger) × CborAdmissionCompiler.Local) × List Logged))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (reached : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup
      (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) [])).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (handle : Handle) (session owner : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto (boundaryWire wire parse) setup.serverKeyId
      outcome.2.1.1.1.2.transcript handle = some (session, owner)) :
    session < budget.accept ∧ owner < budget.create := by
  have result := PqxdhDeploymentRegistrationTrace.source_support setup (CborRawCompile.sourceCodec wire parse) checks
    ensureInit none _ _ _ outcome reached
  have logEq := CborRawKemTrace.compiled_trace setup wire parse bounds mode adversary outcome.2.1 result
  obtain ⟨traced, _⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup (CborRawCompile.sourceCodec wire parse)
    checks ensureInit none _ _ rfl after outcome reached
  have compiled := PqxdhDeploymentRegistrationTrace.traceFrom_support _ [] outcome.2.1 result
  have wrapped : outcome.2.1.1.1 ∈ support (PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse)
      setup.serverKeyId bounds (asModeO mode adversary)) := by
    apply support_simulateQ_run'_subset (CborRawCompile.compileImpl setup wire parse) _
      (CborAdmissionCompiler.Local.empty setup.serverKeyId)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have accepts := ledger_count setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds 3
    (asModeO mode adversary) (budget.cap 3)
    (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects 3) Ledger.empty _ wrapped
  have creates := ledger_count setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds 1
    (asModeO mode adversary) (budget.cap 1)
    (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects 1) Ledger.empty _ wrapped
  simp only [Ledger.empty, classCount, List.countP_nil, Nat.zero_add] at accepts creates
  obtain ⟨raw, _, _, _, rawFound, _, _, _, _⟩ := PqxdhDeploymentKemTransfer.designate_keys _ (boundaryWire wire parse)
    _ _ handle session owner designated
  have acceptLogged : (raw, some session) ∈ acceptsOf outcome.2.1.2 := by
    rw [logEq]
    simp only [acceptsOf, registrations, List.mem_filterMap]
    exact ⟨.accept raw (some session), ⟨_, PqxdhDeploymentKemTransfer.acceptOf_mem _ _ raw rawFound, rfl⟩, rfl⟩
  obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp acceptLogged
  have samePosition := traced.positional position raw session positionFound
  have bound := (List.getElem?_eq_some_iff.mp positionFound).1
  rw [logEq, accepts_count] at bound
  have created := designate_created _ (boundaryWire wire parse) _ _ handle session owner designated
  have owners := owners_count outcome.2.1.1.1.2.transcript
  simp only [classCount] at owners bound
  refine ⟨?_, ?_⟩
  · rw [samePosition]
    exact lt_of_lt_of_le bound accepts
  · exact lt_of_lt_of_le created (le_trans owners creates)

/-- Every actual native raw game designation has the same tight original target domain. -/
theorem range_game_create (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (reached : outcome ∈ support ((CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime))
    (observed : Observed X) (found : observeGame outcome.1 = some observed)
    (handle : Handle) (session owner : Nat)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto (boundaryWire wire parse) setup.serverKeyId
      observed.2.1.transcript handle = some (session, owner)) : session < budget.accept ∧ owner < budget.create := by
  have game := CborRawCompileSecrecy.compile_full_source setup wire parse checks lengths parser ensureInit phase1 phase2
    bounds mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change _ = (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime at game
  have traced := PqxdhDeploymentRegistrationTrace.source_map setup (CborRawCompile.sourceCodec wire parse) checks
    ensureInit none Prod.fst (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) [])
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at traced
  rw [← game, traced, Functor.map_map, support_map] at reached
  obtain ⟨⟨_ | source, after⟩, member, rfl⟩ := reached
  · cases found
  · have same : some (source.2.1.1.1.1, source.2.1.1.1.2, source.2.1.1.2.copies.produced) = some observed := found
    obtain rfl := Option.some.inj same
    exact traced_range_create setup wire parse checks ensureInit bounds mode adversary budget respects runtime source
      after member handle session owner designated

/-- The extra pool-reservation target is never designated in the actual raw game. -/
theorem designated_create (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (claim : Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (reached : outcome ∈ support ((CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime))
    (g : Fin budget.accept × Fin budget.capacity)
    (chosen : designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some g) :
    g.2.val < budget.create := by
  unfold designated target at chosen
  obtain ⟨observed, found, named⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨handle, _, inside⟩ := Option.bind_eq_some_iff.mp named
  exact (range_game_create setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode adversary budget
    respects runtime outcome reached observed found handle g.1.val g.2.val
    (PqxdhDeploymentKemTransfer.designateIn_some _ (boundaryWire wire parse) _ budget _ handle g inside)).2

end BeaconcryptCore.Computational.CborRawTargetRange

/-- info: 'BeaconcryptCore.Computational.CborRawTargetRange.traced_range_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetRange.traced_range_create
/-- info: 'BeaconcryptCore.Computational.CborRawTargetRange.range_game_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetRange.range_game_create
/-- info: 'BeaconcryptCore.Computational.CborRawTargetRange.designated_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetRange.designated_create
