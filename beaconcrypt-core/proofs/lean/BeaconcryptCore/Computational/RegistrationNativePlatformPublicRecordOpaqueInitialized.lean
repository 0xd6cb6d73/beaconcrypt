-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueAfter
/-! Initialized averaging preserves the literal warmed startup cache and common platform state. The actual known-material source reaches its opaque record interpretation with one same-run repeated-role audit charge, retaining the full terminal record observation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
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


abbrev Context (source : RegistrationNativeMldsa.Source) (cap : Nat) :=
  PqxdhJointIdentity.IdentitySeed × PqxdhJointGapDh.ScalarBytes × RegistrationNativeG3Tables.MaterialTable cap ×
    (Option (RegistrationNativePublicStartup.Started source) × PqxdhRecordLiftWorld.State cap)

noncomputable def prior (budget : PqxdhDeploymentInterface.Budget) : ProbComp (Context source (budget.cap 4 + budget.cap 5)) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let initialized ← (RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial
  pure (seed, scalar, materials, initialized)

omit primitive in
/-- Successful literal generated startup returns the cold public roster and sessions at its actual reached World. -/
theorem startup_cold {n : Nat} (identity : PqxdhJointIdentity.PublicIdentity)
    (before : PqxdhRecordLiftWorld.State n) (started : RegistrationNativePublicStartup.Started source)
    (after : PqxdhRecordLiftWorld.State n)
    (supported : (some started, after) ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before)) :
    started.frontend.server.sessions = [] ∧ started.frontend.beacons = [] ∧ started.frontend.parsedAccepts = 0 := by
  simp only [RegistrationNativePublicStartupFrame.startup, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨constructed, _built, supported⟩ := supported
  cases made : constructed.1.1 with
  | none => simp only [made, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | some created =>
    simp only [made, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨generated, _called, supported⟩ := supported
    cases born : generated.1 with
    | none => simp only [born, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
    | some credential =>
      simp only [born, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨installed, _initialized, supported⟩ := supported
      rw [StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl, rfl⟩

omit primitive in
/-- The one complete warm prior derives its own cold frontend, unused roles and empty protected seeds without changing its reached cache. -/
theorem prior_fields (budget : PqxdhDeploymentInterface.Budget)
    (context : Context source (budget.cap 4 + budget.cap 5)) (started : RegistrationNativePublicStartup.Started source)
    (supported : context ∈ support (prior setup source ensureInit identityIndex serverKeyId budget))
    (success : context.2.2.2.1 = some started) :
    started.frontend.server.sessions = [] ∧ started.frontend.beacons = [] ∧ started.frontend.parsedAccepts = 0 ∧
      (∀ slot role, context.2.2.2.2.used slot role = false) ∧ context.2.2.2.2.seeds = PqxdhRecordLiftLazyTable.initial := by
  simp only [prior, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨seed, _seed, scalar, _scalar, materials, _materials, initialized, reached, rfl⟩ := supported
  have actual : (some started, initialized.2) ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial) := by simpa only [← success] using reached
  have cold := startup_cold setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) _ started initialized.2 actual
  have fields := RegistrationNativePlatformPublicStartupFields.initialized setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) (some started, initialized.2) actual
  exact ⟨cold.1, cold.2.1, cold.2.2, fields.2, fields.1⟩

noncomputable def known (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) : ProbComp (Bool × Platform) := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  RegistrationNativePlatformPublicRecordOpaqueAfter.known setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
    budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2

noncomputable def hidden (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) : ProbComp (Bool × Platform) := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  RegistrationNativePlatformPublicRecordOpaqueAfter.hidden setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
    budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) : ProbComp Bool := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  RegistrationNativePlatformPublicRecordOpaqueAfter.audit setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
    budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2

attribute [local irreducible] RegistrationNativePlatformPublicRecordOpaqueAfter.known
  RegistrationNativePlatformPublicRecordOpaqueAfter.hidden RegistrationNativePlatformPublicRecordOpaqueAfter.audit
  RegistrationNativePlatformPublicRecordMaterializedTables.after RegistrationNativePublicStartupFrame.startup

/-- Actual startup and an independent private seed table may be reordered, after which the reached source cut supplies its own empty-seed receipt. -/
theorem source_eq (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    RegistrationNativePlatformPublicRecordMaterializedTables.game setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous =ᵈ
      Prod.fst <$> known setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous := by
  unfold RegistrationNativePlatformPublicRecordMaterializedTables.game known prior
  simp only [map_bind, bind_assoc, pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  apply _root_.EvalDistEq.bind_right
  intro materials
  have swapped := OracleComp.EvalDistEq.bind_bind_swap
    ($ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5))
    ((RegistrationNativePublicStartupFrame.startup (n := budget.cap 4 + budget.cap 5) setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed)).run PqxdhRecordLiftWorld.initial)
    (fun seeds initialized => Prod.fst <$> RegistrationNativePlatformPublicRecordMaterializedTables.after setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
      budget seed scalar candidate materials seeds previous initialized)
  refine swapped.trans ?_
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro initialized supported
  have actual := RegistrationNativePlatformPublicRecordOpaqueAfter.known_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
    budget seed scalar candidate materials previous initialized supported
  have observed := congrArg (Functor.map Prod.fst) actual
  simp only [map_bind] at observed ⊢
  rw [observed]

/-- The complete initialized opaque comparison pays the same chronological audit, with startup refusals and every final P retained. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (previous : Platform) :
    ENNReal.ofReal (discreteDistance
      (known setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous)
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget candidate previous)) ≤
      Pr{let flag ← audit setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget candidate previous}[flag = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent
    (prior setup source ensureInit identityIndex serverKeyId budget)
    (fun context => RegistrationNativePlatformPublicRecordOpaqueAfter.known setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2)
    (fun context => RegistrationNativePlatformPublicRecordOpaqueAfter.hidden setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2)
    (fun context => RegistrationNativePlatformPublicRecordOpaqueAfter.audit setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2)
    (fun _ flag => flag = true)
    (fun context _ => by
      have pointwise := ENNReal.toReal_mono (prEvent_ne_top _)
        (RegistrationNativePlatformPublicRecordOpaqueAfter.bound setup checks wire route source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget context.1 context.2.1 candidate context.2.2.1 previous context.2.2.2)
      simpa only [ENNReal.toReal_ofReal (discreteDistance_nonneg _ _)] using pointwise)
  have lifted := (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le
  simpa only [known, hidden, audit, OracleComp.prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map] using lifted

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.startup_cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.startup_cold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.source_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.source_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordOpaqueInitialized.bound
