-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordOpenSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3HonestKemSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-! The complete actual warm corrected public query tree retains terminal cache, produced frames and raw counters beside the original ledger, frontend and persistent platform state. Its honest on-demand KEM provider is reified as the literal indexed native KEM interface, then the original candidate-independent decision has the exact real reserved marginal and one ordinary CCA comparison. The candidate reaches only the final ghost observer; the source adversary still receives its original public challenge. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)



omit primitive in
private theorem reference_values {A P : Type}
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P)
    (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

/-- The actual complete known-material source decision at a reached warm cut equals its honest open KEM/key client with all terminal record data retained. -/
theorem fixed_source (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (context : Context source (budget.cap 4 + budget.cap 5)) (started : RegistrationNativePublicStartup.Started source)
    (success : context.2.2.2.1 = some started) :
    (do let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
        Prod.fst <$> RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selected selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget
          context.1 context.2.1 candidate materials seeds previous context.2.2.2) =ᵈ
      RegistrationNativePlatformG3RecordKem.observation source decision <$>
        (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup)
          (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected previous context)).run' ((PqxdhLiveKemBirth.empty, ()), ∅) := by
  let actual := RegistrationNativePlatformMaterializedWhole.tree (n := budget.cap 4 + budget.cap 5) setup wire
    (RegistrationNativeMldsa.owned source started.credential) context.2.1 checks source selected selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)
  have cap := RegistrationNativePlatformG3RepeatRun.demand_bound (n := budget.cap 4 + budget.cap 5) setup wire (RegistrationNativeMldsa.owned source started.credential)
    context.2.1 checks source selected selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous) budget (bounded _)
  have law := RegistrationNativePlatformG3RecordOpenSource.program_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
    (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 candidate (RegistrationNativeOpenRetainedReal.provider setup)
    actual cap (RegistrationNativeHiddenInterpreter.initial ()) context.2.2.2.2
  let observe := fun (result : (((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
      RegistrationNativePlatformPublicWorldObservation.RecordView)) => decision result.1.1 result.2
  have mapped := LazyOracleDiscard.LawEq.map observe law
  have values := reference_values (RegistrationNativeOpenRetainedReal.provider setup)
    (RegistrationNativePlatformG3RecordOpenSource.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 actual
      (RegistrationNativeHiddenInterpreter.initial ()) context.2.2.2.2) (PqxdhLiveKemBirth.empty, ()) ∅
  have valuesObserved := congrArg (Functor.map observe) values
  have traced := congrArg (fun tree => observe <$> (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup) tree).run'
      ((PqxdhLiveKemBirth.empty, ()), ∅))
    (RegistrationNativePlatformG3RecordOpenSource.client_erase setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 actual
      (RegistrationNativeHiddenInterpreter.initial ()) context.2.2.2.2)
  have distribution := _root_.EvalDistEq.of_evalDist_eq mapped.evalDist_eq
  simp only [RegistrationNativeHiddenInterpreter.initial] at distribution valuesObserved traced
  simp only [RegistrationNativePlatformG3HonestKemSource.honest] at traced
  rw [← valuesObserved] at distribution
  rw [← traced] at distribution
  simpa only [actual, observe, RegistrationNativePlatformPublicRecordMaterializedTables.after,
    RegistrationNativePlatformG3RecordKem.after, success, RegistrationNativePlatformG3RecordKem.observation,
    RegistrationNativePlatformMaterializedWhole.tree, RegistrationNativePlatformPublicRetainedRecordProfile.observed,
    PqxdhJointGapDh.challenge, RegistrationNativePlatformG3HonestKemSource.honest,
    RegistrationNativeSelectiveHiddenInterpreter.initial, simulateQ_map, StateT.run'_map',
    StateT.run_map, Functor.map_map, map_bind, RegistrationNativeHiddenInterpreter.initial,
    Prod.map_def, id_eq] using distribution
omit primitive in
private theorem honest_coins {A : Type} (work : ProbComp A)
    (before : (PqxdhLiveKemBirth.Pool KemSK × Unit) × RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup)
      (simulateQ RegistrationNativePlatformG3InitializedKem.coins work)).run before = (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativePlatformG3HonestKemSource.honest setup ∘ₛ RegistrationNativePlatformG3InitializedKem.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT _ ProbComp) := by
    funext query
    apply StateT.ext
    rintro ⟨⟨pool, marker⟩, table⟩
    cases marker
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformG3InitializedKem.coins,
      RegistrationNativeOpenKey.keyLift, RegistrationNativeKeyCompiler.coins, simulateQ_spec_query,
      RegistrationNativePlatformG3HonestKemSource.honest,
      PqxdhRegistrationJointKemSecondEntry.lazyImpl,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift, StateT.run]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The honest original decision forwards the exact full warm startup and persistent platform state before any indexed KEM query. -/
theorem honest_prefix (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) :
    RegistrationNativePlatformG3RecordKem.honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget selected previous =
      (do let context ← prior setup source ensureInit identityIndex serverKeyId budget
          RegistrationNativePlatformG3RecordKem.observation source decision <$>
            (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup)
              (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
                erased helper writer bounds mode adversary budget selected previous context)).run' ((PqxdhLiveKemBirth.empty, ()), ∅)) := by
  simp only [RegistrationNativePlatformG3RecordKem.honest, RegistrationNativePlatformG3RecordKem.program,
    StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [honest_coins setup]
  simp only [bind_map_left]

/-- At every startup result, including refusal, fresh materialization has the original complete honest decision law. -/
theorem after_source (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (context : Context source (budget.cap 4 + budget.cap 5)) :
    (do let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
        Prod.fst <$> RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selected selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget
          context.1 context.2.1 candidate materials seeds previous context.2.2.2) =ᵈ
      RegistrationNativePlatformG3RecordKem.observation source decision <$>
        (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup)
          (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected previous context)).run' ((PqxdhLiveKemBirth.empty, ()), ∅) := by
  cases success : context.2.2.2.1 with
  | some started =>
    exact fixed_source setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget bounded selected previous candidate context started success
  | none =>
    simp only [RegistrationNativePlatformPublicRecordMaterializedTables.after, RegistrationNativePlatformG3RecordKem.after,
      success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
      RegistrationNativePlatformG3RecordKem.observation]
    have seeds := OracleComp.EvalDistEq.bind_const ($ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)) (pure false : ProbComp Bool)
    have materials := OracleComp.EvalDistEq.bind_const ($ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (pure false : ProbComp Bool)
    exact (_root_.EvalDistEq.bind_right ($ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (fun _ => seeds)).trans materials

/-- The actual initialized known-material source decision has the honest on-demand open KEM law with its warm cache, original ledger, produced frames, raw counters and persistent P. -/
theorem game_source (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    RegistrationNativePlatformPublicRecordMaterializedTables.game setup checks wire route source ensureInit identityIndex serverKeyId selected selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous =ᵈ
      RegistrationNativePlatformG3RecordKem.honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget selected previous := by
  let normalized : ProbComp Bool := do
    let context ← prior setup source ensureInit identityIndex serverKeyId budget
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
    Prod.fst <$> RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selected selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget
      context.1 context.2.1 candidate materials seeds previous context.2.2.2
  have post : normalized =ᵈ RegistrationNativePlatformG3RecordKem.honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget selected previous := by
    rw [honest_prefix]
    exact _root_.EvalDistEq.bind_right (prior setup source ensureInit identityIndex serverKeyId budget) fun context => after_source setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget bounded selected previous candidate context
  refine _root_.EvalDistEq.trans ?_ post
  unfold RegistrationNativePlatformPublicRecordMaterializedTables.game normalized prior
  simp only [bind_assoc, pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  let tables := do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
    pure (materials, seeds)
  let startupDraw := (RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial
  let suffix := fun (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
      (table : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5) × RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)) => Prod.fst <$> RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selected selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget
    seed scalar candidate table.1 table.2 previous initialized
  have swapped := OracleComp.EvalDistEq.bind_bind_swap tables startupDraw (fun table initialized => suffix initialized table)
  have unused := OracleComp.EvalDistEq.bind_const ($ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5))
    (do let initialized ← startupDraw
        let table ← tables
        suffix initialized table)
  simpa only [tables, startupDraw, suffix, bind_assoc, pure_bind] using swapped.trans unused.symm


/-- The literal corrected known-material source decision pays one ordinary KEM CCA loss and unconditional correctness error to the record-aware uniform branch. -/
theorem game_close (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    (RegistrationNativePlatformPublicRecordMaterializedTables.game setup checks wire route source ensureInit identityIndex serverKeyId selected.val selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
        (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
        (simulateQ RegistrationNativeOpenKey.native
          (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected.val previous))
        (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result) budget.create selected false) ≤
      (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
          (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
          (simulateQ RegistrationNativeOpenKey.native
            (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous))
          (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result) budget.create selected).toINDCCA).toReal +
        RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem := by
  have same := (game_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary decision budget bounded selected.val previous candidate).prEvent_eq (fun result => result = true)
  have compared := RegistrationNativePlatformG3RecordKem.normal_close setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary functional decision budget bounded selected previous
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, same] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.fixed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.honest_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.honest_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.after_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.game_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.game_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKnownSource.game_close
