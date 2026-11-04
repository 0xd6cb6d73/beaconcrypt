-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem
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


abbrev Result (source : RegistrationNativeMldsa.Source) (cap : Nat) (Value Platform : Type) :=
  Context source cap × Option (RegistrationNativePlatformG3CheckedUniformSource.Result source Value Platform ×
    RegistrationNativePlatformPublicWorldObservation.RecordView)

omit primitive in
def drop {cap : Nat} (result : Result source cap Value Platform) : RegistrationNativePlatformG3InitializedKem.Result source cap Value Platform :=
  (result.1, result.2.map Prod.fst)

noncomputable def after (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform)
    (context : Context source (budget.cap 4 + budget.cap 5)) : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source (budget.cap 4 + budget.cap 5) Value Platform) :=
  match context.2.2.2.1 with
  | none => pure (context, none)
  | some started => (fun result => (context, some result)) <$>
      RegistrationNativePlatformG3RecordOpenSource.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
        (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1
        (RegistrationNativeG2Trace.program (RegistrationNativePlatformMaterializedWhole.tree setup wire
          (RegistrationNativeMldsa.owned source started.credential) context.2.1 checks source selected selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
          (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)))
        (RegistrationNativeHiddenInterpreter.initial ()) context.2.2.2.2

noncomputable def program (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) := do
  let context ← simulateQ RegistrationNativePlatformG3InitializedKem.coins (prior setup source ensureInit identityIndex serverKeyId budget)
  after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous context

/-- Keeping terminal record data adds no source request and projects to the same complete initialized native result. -/
theorem after_drop (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform)
    (context : Context source (budget.cap 4 + budget.cap 5)) :
    drop source <$> after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous context =
      RegistrationNativePlatformG3InitializedKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous context := by
  unfold after RegistrationNativePlatformG3InitializedKem.after
  cases success : context.2.2.2.1 with
  | none => simp only [map_pure, drop, Option.map_none]
  | some started =>
    have sourceEq := RegistrationNativePlatformG3RecordOpenSource.client_drop setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1
      (RegistrationNativeG2Trace.program (RegistrationNativePlatformMaterializedWhole.tree setup wire
        (RegistrationNativeMldsa.owned source started.credential) context.2.1 checks source selected selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)))
      (RegistrationNativeHiddenInterpreter.initial ()) context.2.2.2.2
    have observed := congrArg (Functor.map (fun result => (context, some result))) sourceEq
    simpa only [Functor.map_map, drop, Option.map_some, RegistrationNativeG3MaterializedRetainedLazy.client,
      RegistrationNativePlatformG3CheckedUniformSource.openProgram, RegistrationNativePlatformMaterializedWhole.tree,
      RegistrationNativeG3MaterializedRetainedSource.ordinary, RegistrationNativeHiddenInterpreter.initial,
      RegistrationNativeG3NativeUniformAuditBound.ordinary, RegistrationNativePlatformSecretWordOrdinary.evaluate,
      Prod.map_def, id_eq, RegistrationNativeG3NativeStartupFields.word_eval] using observed

/-- The full record-aware warm client preserves the exact original query tree and all initialization failures. -/
theorem program_drop (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) :
    drop source <$> program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous =
      RegistrationNativePlatformG3InitializedKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous := by
  simp only [program, RegistrationNativePlatformG3InitializedKem.program, map_bind, after_drop]

/-- Original raw query allowances bound actual private births and forbid generated-key reveals even with full terminal record data retained. -/
theorem resource_bounds (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) (selected : Nat) (previous : Platform) :
    (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create ∧
    (simulateQ RegistrationNativeOpenKey.native
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 := by
  have actual := RegistrationNativePlatformG3InitializedKem.resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected previous
  rw [← program_drop setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous] at actual
  simpa only [simulateQ_map, isQueryBoundP_map_iff] using actual

omit primitive in
def observation (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    {cap : Nat} (result : Result source cap Value Platform) : Bool :=
  match result.2 with
  | none => false
  | some observed => decision observed.1.1.1 observed.2

noncomputable def honest (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) : ProbComp Bool :=
  observation source decision <$> (simulateQ (RegistrationNativePlatformG3HonestKemSource.honest setup)
    (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)).run' ((PqxdhLiveKemBirth.empty, ()), ∅)

noncomputable def normal (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) : ProbComp Bool :=
  RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem (simulateQ RegistrationNativeOpenKey.native
    (observation source decision <$> program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous))

/-- The literal on-demand provider preserves the full original decision, ledger and terminal RecordView under indexed native KEM interpretation. -/
theorem honest_source (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Nat) (previous : Platform) :
    honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget selected previous =
      normal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget selected previous := by
  have actual := congrArg (Functor.map (observation source decision))
    (RegistrationNativePlatformG3HonestKemSource.values_source setup
      (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous) (∅, PqxdhLiveKemBirth.empty))
  simpa only [honest, normal, RegistrationNativeOpenKeyKemGame.normal, RegistrationNativePlatformG3HonestKemSource.native,
    RegistrationNativePlatformG3HonestKemSource.embed, ← QueryImpl.simulateQ_compose,
    StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using actual.symm

/-- One selected real presampled provider gives the original complete candidate-independent source decision, including dummy and mismatched getter routes. -/
theorem real_source (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget selected.val previous =ᵈ
      RegistrationNativeOpenKeyKemEarlyObservedReal.source setup.baseImpl setup.kem
        (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)
        (fun _ result => observation source decision result) budget.create selected := by
  rw [honest_source]
  have caps := resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected.val previous
  exact RegistrationNativeOpenKeyKemEarlyObservedMarginal.real_marginal setup.baseImpl setup.kem _ (observation source decision) budget.create selected caps.1 caps.2

/-- The same complete original source decision pays exactly one ordinary KEM CCA loss and unconditional correctness error before its uniform-side materialization and audit. -/
theorem normal_close (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    (honest setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget selected.val previous).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
        (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
        (simulateQ RegistrationNativeOpenKey.native
          (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected.val previous))
        (fun _ result => observation source decision result) budget.create selected false) ≤
      (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
          (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
          (simulateQ RegistrationNativeOpenKey.native
            (program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous))
          (fun _ result => observation source decision result) budget.create selected).toINDCCA).toReal +
        RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem := by
  rw [honest_source]
  have caps := resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected.val previous
  exact RegistrationNativeOpenKeyKemEarlyObservedMarginal.normal_close setup.baseImpl setup.kem functional _
    (observation source decision) budget.create selected caps.1 caps.2

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.after_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.after_drop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.program_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.program_drop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.resource_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.resource_bounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.honest_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.honest_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.real_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.normal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem.normal_close
