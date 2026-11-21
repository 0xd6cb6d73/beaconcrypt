-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
/-! The actual complete record observer has a provider-parametrized warm known/hidden comparison. The opaque provider and its state are kept literal; no on-demand/early-provider game is identified by definition. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {I KemSK Platform E ProviderState Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (serverKeyId : U64)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)

noncomputable def work (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) :=
  Prod.fst <$> (simulateQ
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate provider)
    (RegistrationNativeG2Trace.program (RegistrationNativePlatformMaterializedWhole.tree setup wire
      (RegistrationNativeMldsa.owned source started.credential) scalar checks source selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)))).run
      (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
        (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) providerState)
        (RegistrationNativeG3LocalMaterialCompletedSource.cache materials))

noncomputable def plainWork (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) :=
  RegistrationNativePlatformMaterializedWhole.world setup wire (RegistrationNativeMldsa.owned source started.credential)
    seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)
    (RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
      (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) providerState)
      (RegistrationNativeG3LocalMaterialCompletedSource.cache materials))

/-- Erasing the analysis chronology retains the actual complete source result and provider execution. -/
theorem work_erase (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) :
    Prod.fst <$> work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous started =
      Prod.fst <$> plainWork setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget seed scalar candidate materials previous started := by
  let tree := RegistrationNativePlatformMaterializedWhole.tree (n := budget.cap 4 + budget.cap 5) setup wire
    (RegistrationNativeMldsa.owned source started.credential) scalar checks source selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)
  let frame := RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
    (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) providerState) (RegistrationNativeG3LocalMaterialCompletedSource.cache materials)
  have erased := congrArg (fun requests =>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate provider) requests).run frame)
    (RegistrationNativeG2Trace.program_erase tree RegistrationNativeG2Trace.initial)
  have observed := congrArg (Functor.map Prod.fst) erased
  simpa only [work, plainWork, tree, frame, RegistrationNativeG2Trace.program, RegistrationNativePlatformMaterializedWhole.tree,
    RegistrationNativePlatformMaterializedWhole.world, simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq,
    ← QueryImpl.simulateQ_compose, RegistrationNativePlatformG3RepeatRun.backend] using observed

def observation {source : RegistrationNativeMldsa.Source}
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)
    (result : ((((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) ×
      RegistrationNativePlatformPublicWorldObservation.RecordView)) : Bool × Platform :=
  (decision result.1.1.1 result.2, result.1.1.2.2)

noncomputable def known (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ProbComp (Bool × Platform) :=
  match initialized.1 with
  | none => pure (false,previous)
  | some started => observation decision <$>
      RegistrationNativePlatformG3RecordUniform.knownGame setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started) initialized.2

noncomputable def hidden (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ProbComp (Bool × Platform) :=
  match initialized.1 with
  | none => pure (false,previous)
  | some started => observation decision <$>
      RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started) initialized.2

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) : ProbComp Bool :=
  match initialized.1 with
  | none => pure false
  | some started => do
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      let result ← RegistrationNativeG3GuardedCoupling.audit setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (RegistrationNativeG3GuardedCoupling.overlay initialized.2 seeds)
        (work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget seed scalar candidate materials previous started) initialized.2
      pure result.2.2

omit primitive in
private theorem known_map {A B : Type} {n : Nat}
    (map : A → B) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (job : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A) (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativePlatformG3RecordCoupling.known setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds (map <$> job) before =
      Prod.map map id <$> RegistrationNativePlatformG3RecordCoupling.known setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds job before := by
  simp only [RegistrationNativePlatformG3RecordCoupling.known, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The actual traced source preserves every terminal record field at the same warm cut. -/
theorem known_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) (reached : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (empty : reached.seeds = PqxdhRecordLiftLazyTable.initial) :
    (do
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
      observation decision <$> RegistrationNativePlatformG3RecordTraceKnown.full materials setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds wire
        (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate provider checks source selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)
        (RegistrationNativeSelectiveHiddenInterpreter.initial providerState) reached) =
      known setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous (some started,reached) := by
  simp only [known, RegistrationNativePlatformG3RecordUniform.knownGame, map_bind]
  apply bind_congr
  intro seeds
  have overlay : RegistrationNativeG3GuardedCoupling.overlay reached seeds = seeds := by
    funext slot
    simp [RegistrationNativeG3GuardedCoupling.overlay, empty, PqxdhRecordLiftLazyTable.initial, OracleComp.completeTable]
  rw [overlay]
  have actual := RegistrationNativePlatformG3RecordTraceKnown.known_source materials setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds wire
    (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate provider checks source selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)
    (RegistrationNativeSelectiveHiddenInterpreter.initial providerState) reached
  have observed := congrArg (Functor.map (observation (Platform := Platform) decision)) actual
  simpa only [work, known_map, Functor.map_map, Prod.map_def, id_eq] using observed

/-- The complete terminal-record observer at each literal startup cut pays only that same actual repeated-role audit. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (initialized : Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    ENNReal.ofReal (discreteDistance
      (known setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous initialized)
      (hidden setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous initialized)) ≤
      Pr{let flag ← (audit setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget seed scalar candidate materials previous initialized)}[flag = true] := by
  rcases initialized with ⟨_ | started, reached⟩
  · simp only [known, hidden, audit, discreteDistance_self, ENNReal.ofReal_zero, prEvent_pure, Bool.false_eq_true,
      ↓reduceIte]
    exact le_rfl
  · let job := work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous started
    have pointwise := RegistrationNativePlatformG3RecordUniform.bound setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached
    have distance := discreteDistance_map_le (observation (source := source) (Platform := Platform) decision)
      (RegistrationNativePlatformG3RecordUniform.knownGame setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
      (RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
    have compared := (ENNReal.ofReal_le_ofReal distance).trans pointwise
    simpa only [known, hidden, audit, job, OracleComp.prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map] using compared


omit primitive in
private theorem audit_map {A B : Type} {n : Nat} (map : A → B)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (job : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A)
    (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeG3GuardedCoupling.audit setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds (map <$> job) before =
      Prod.map map id <$> RegistrationNativeG3GuardedCoupling.audit setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds job before := by
  simp only [RegistrationNativeG3GuardedCoupling.audit, simulateQ_map, StateT.run_map]
  rfl

/-- At the genuine empty-seed warm cut the analysis observer has exactly the same original marked source audit. -/
theorem audit_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) (reached : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (empty : reached.seeds = PqxdhRecordLiftLazyTable.initial) :
    audit setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous (some started,reached) =
      (do
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
        let result ← RegistrationNativePlatformG3RepeatRun.original setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds wire
          (RegistrationNativeMldsa.owned source started.credential) seed scalar candidate provider checks source selectedOwner selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
          (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩) (started.frontend,previous)
          (RegistrationNativeSelectiveHiddenInterpreter.initial providerState) (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) reached
        pure result.2.2) := by
  simp only [audit]
  apply bind_congr
  intro seeds
  have overlay : RegistrationNativeG3GuardedCoupling.overlay reached seeds = seeds := by
    funext slot
    simp [RegistrationNativeG3GuardedCoupling.overlay, empty, PqxdhRecordLiftLazyTable.initial, OracleComp.completeTable]
  rw [overlay]
  have erased := congrArg (fun job => RegistrationNativeG3GuardedCoupling.audit setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds job reached)
    (work_erase setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous started)
  rw [audit_map, audit_map] at erased
  have observed := congrArg (Functor.map (fun result => result.2.2)) erased
  simpa only [plainWork, RegistrationNativePlatformG3RepeatRun.original, Functor.map_map, Prod.map_def, id_eq, bind_pure_comp] using observed


omit primitive in
private theorem hidden_map {A B : Type} {n : Nat} (map : A → B)
    (job : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A) (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativePlatformG3RecordCoupling.hidden setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route (map <$> job) before =
      Prod.map map id <$> RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job before := by
  simp only [RegistrationNativePlatformG3RecordCoupling.hidden, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- Dropping only the internal chronology recovers the exact untraced hidden source and the complete record observation. -/
theorem hidden_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) (reached : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    hidden setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous (some started,reached) =
      (fun result => (decision result.1.1.1 result.2,result.1.1.2.2)) <$>
        RegistrationNativePlatformG3RecordCoupling.hidden setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
          (plainWork setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget seed scalar candidate materials previous started) reached := by
  simp only [hidden]
  unfold observation
  have erased := congrArg (fun job => RegistrationNativePlatformG3RecordCoupling.hidden setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
    (work_erase setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget seed scalar candidate materials previous started)
  rw [hidden_map,hidden_map] at erased
  have observed := congrArg (Functor.map (fun result => (decision result.1.1 result.2,result.1.2.2))) erased
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.work_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.work_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.audit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.audit_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter.hidden_source
