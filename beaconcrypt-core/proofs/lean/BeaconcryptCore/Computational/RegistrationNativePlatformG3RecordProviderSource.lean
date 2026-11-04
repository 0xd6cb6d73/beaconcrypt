-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordMaterializedTables
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource
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


variable {ProviderState : Type}

noncomputable def full (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (context : Context source (budget.cap 4 + budget.cap 5)) : ProbComp (RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform) :=
  match context.2.2.2.1 with
  | none => pure (context, none)
  | some started => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
    let result ← (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source started.credential)
      context.1 context.2.1 candidate provider)
      (RegistrationNativeG2Trace.program (RegistrationNativePlatformMaterializedWhole.tree setup wire
        (RegistrationNativeMldsa.owned source started.credential) context.2.1 checks source selected selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)))).run
          (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeHiddenInterpreter.initial providerState, ∅) ∅, context.2.2.2.2)
    pure (context, some (result.1, RegistrationNativePlatformPublicWorldObservation.recordView result.2.2))

/-- The actual complete materialized source preserves every original result and terminal record field while the same arbitrary provider remains opaque and stateful. -/
theorem provider_source (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Nat) (previous : Platform) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (context : Context source (budget.cap 4 + budget.cap 5)) :
    full setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary provider providerState budget selected previous candidate context =ᵈ
      (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
          (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT)
        (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected previous context)).run' ((PqxdhLiveKemBirth.empty, providerState), ∅) := by
  cases success : context.2.2.2.1 with
  | none =>
    simp only [full, RegistrationNativePlatformG3RecordKem.after, success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact .rfl
  | some started =>
    let actual := RegistrationNativeG2Trace.program (RegistrationNativePlatformMaterializedWhole.tree (n := budget.cap 4 + budget.cap 5) setup wire
      (RegistrationNativeMldsa.owned source started.credential) context.2.1 checks source selected selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous))
    have cap : actual.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
      apply RegistrationNativeG2Trace.program_bound
      exact RegistrationNativePlatformG3RepeatRun.demand_bound setup wire (RegistrationNativeMldsa.owned source started.credential)
        context.2.1 checks source selected selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous) budget (bounded _)
    have law := RegistrationNativePlatformG3RecordOpenSource.program_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 candidate provider actual cap
      (RegistrationNativeHiddenInterpreter.initial providerState) context.2.2.2.2
    have mapped := LazyOracleDiscard.LawEq.map (fun result => (context, some result)) law
    have values := reference_values provider
      (RegistrationNativePlatformG3RecordOpenSource.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
        (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 actual
        (RegistrationNativeHiddenInterpreter.initial providerState) context.2.2.2.2) (PqxdhLiveKemBirth.empty, providerState) ∅
    have valuesObserved := congrArg (Functor.map (fun result => (context, some result))) values
    let : MeasurableSpace (RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform) := ⊤
    let : DiscreteMeasurableSpace (RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform) :=
      ⟨fun _ => MeasurableSpace.measurableSet_top⟩
    have distribution := _root_.EvalDistEq.of_evalDist_eq mapped.evalDist_eq
    simp only [RegistrationNativeHiddenInterpreter.initial] at distribution valuesObserved
    rw [← valuesObserved] at distribution
    simpa only [full, RegistrationNativePlatformG3RecordKem.after, success, actual,
      RegistrationNativePlatformG3RecordOpenSource.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
      RegistrationNativeHiddenInterpreter.initial, simulateQ_map, StateT.run'_map', Functor.map_map, map_bind, bind_pure_comp] using distribution
noncomputable def game (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  let result ← full setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
    none budget selected.val previous candidate context
  pure (candidate, result)

/-- The complete actual uniform-provider materialized source has exactly the same original decision and terminal record observation as the conditional KEM branch. -/
theorem conditional_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : PqxdhKemIndCca.MlKemSharedSecret → RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) :
    RegistrationNativePlatformG3RecordUniformSource.conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous observe =ᵈ
      (fun pair => observe pair.1 pair.2) <$> game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous := by
  unfold RegistrationNativePlatformG3RecordUniformSource.conditional game
  simp only [map_bind, bind_pure_comp]
  apply _root_.EvalDistEq.bind_right
  intro context
  apply _root_.EvalDistEq.bind_right
  intro profile
  apply _root_.EvalDistEq.bind_right
  intro candidate
  have actual := (provider_source setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
    none budget bounded selected.val previous candidate context).symm.map (observe candidate)
  simpa only [RegistrationNativeOpenKeyKemEarlySource.reference, Functor.map_map] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource.provider_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource.provider_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource.conditional_source
