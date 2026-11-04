-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordTraceKnown
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicStartupFields
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
/-! The provider-parametrized warm hidden source has the literal corrected typed compiler and complete genuine World startup. The original record observation and persistent platform result are preserved; its startup comparison uses only the named, separately billed accounting view. No known/hidden provider change is inferred. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative
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


noncomputable def privateState (budget : PqxdhDeploymentInterface.Budget)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) :=
  RegistrationNativeG3AuditTraceRun.cold (RegistrationNativeSelectiveHiddenInterpreter.initial
    (n := budget.cap 4 + budget.cap 5) (KemSK := KemSK) providerState)
    (RegistrationNativeG3LocalMaterialCompletedSource.cache materials)

noncomputable def work (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) :=
  RegistrationNativePlatformSelectiveEntropyExecution.run setup checks wire source started.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩)
    ((started.frontend,previous),privateState providerState budget materials)

/-- The complete untraced hidden source has the actual new typed compiler, with only its product association changed. -/
theorem work_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) :
    (fun result => (result.1.1,(result.1.2,result.2))) <$>
      RegistrationNativePlatformG3UniformOpaqueAfter.plainWork setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous started =
      work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous started := by
  have actual := RegistrationNativePlatformSelectiveEntropyExecution.run_source setup checks wire source started.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,started.credential.publicKey,serverKeyId⟩)
    ((started.frontend,previous),privateState providerState budget materials)
  simpa only [RegistrationNativePlatformG3UniformOpaqueAfter.plainWork,RegistrationNativePlatformMaterializedWhole.world,work,privateState] using actual

omit primitive in
private theorem hidden_map {A B : Type} {cap : Nat} (map : A → B)
    (job : OracleComp (PqxdhRecordLiftInterface.WorldSpec cap) A) (before : PqxdhRecordLiftWorld.State cap) :
    RegistrationNativePlatformG3RecordCoupling.hidden setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route (map <$> job) before =
      Prod.map map id <$> RegistrationNativePlatformG3RecordCoupling.hidden setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job before := by
  simp only [RegistrationNativePlatformG3RecordCoupling.hidden,simulateQ_map,StateT.run_map,Functor.map_map]
  rfl

/-- The warm hidden event has the actual corrected typed compiler and every original terminal record field. -/
theorem hidden_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : RegistrationNativePublicStartup.Started source) (reached : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    RegistrationNativePlatformG3UniformOpaqueAfter.hidden setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous (some started,reached) =
      (fun result => (decision result.1.1 result.2,result.1.2.1.2)) <$>
        RegistrationNativePlatformG3RecordCoupling.hidden setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
          (work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous started) reached := by
  rw [RegistrationNativePlatformG3UniformOpaqueAfter.hidden_source]
  have actual := congrArg (fun job => RegistrationNativePlatformG3RecordCoupling.hidden setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route job reached)
    (work_source setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous started)
  rw [hidden_map] at actual
  have observed := congrArg (Functor.map (fun result => (decision result.1.1 result.2,result.1.2.1.2))) actual
  simpa only [Functor.map_map,Prod.map_def,id_eq] using observed

noncomputable def body (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (started : Option (RegistrationNativePublicStartup.Started source)) :
    OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4 + budget.cap 5))
      (Option ((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformSelectiveEntropyEnvironment.State
        (budget.cap 4 + budget.cap 5) KemSK ProviderState Platform source)) :=
  match started with
  | none => pure none
  | some started => some <$> work setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous started

noncomputable def publicProgram (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) := do
  let born ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  body setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous (born.map RegistrationNativeHiddenStartup.Started.native)

/-- Omitting only the deterministic constructor envelope gives the same complete original source value, ledger, public/private and platform output. -/
theorem program_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) :
    Option.map Prod.snd <$> RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous (privateState providerState budget materials) bounds mode adversary =
      publicProgram setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous ensureInit identityIndex := by
  unfold RegistrationNativePlatformSelectiveEntropyStartup.program publicProgram
  simp only [map_bind]
  apply bind_congr
  intro born
  cases born with
  | none => simp only [map_pure,Option.map_none,body]
  | some born =>
    simp only [RegistrationNativePlatformSelectiveEntropyStartup.stage,body,work,Functor.map_map,Option.map_some]

omit primitive in
def observation (previous : Platform) {cap : Nat}
    (result : Option ((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK ProviderState Platform source) ×
      RegistrationNativePlatformPublicWorldObservation.RecordView) : Bool × Platform :=
  match result.1 with
  | none => (false,previous)
  | some actual => (decision actual.1 result.2,actual.2.1.2)

noncomputable def after (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) := do
  let initialized ← (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed)).run (PqxdhRecordLiftWorld.initial (n := budget.cap 4 + budget.cap 5))
  RegistrationNativePlatformG3UniformOpaqueAfter.hidden setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous initialized

noncomputable def actual (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) :=
  observation source decision previous <$> RegistrationNativePlatformG3RecordCoupling.hidden setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
    (publicProgram setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous ensureInit identityIndex)
    PqxdhRecordLiftWorld.initial

/-- The actual warm hidden source is the genuine complete World program; only the named accounting comparison connects the two startup samplers. -/
theorem after_source (budget : PqxdhDeploymentInterface.Budget)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)) (previous : Platform)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) :
    after setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous ensureInit identityIndex =
      actual setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous ensureInit identityIndex := by
  have startup := RegistrationNativePlatformG3RecordAccounting.startup_source setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) (body setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous) PqxdhRecordLiftWorld.initial
  have observed := congrArg (Functor.map (observation (KemSK := KemSK) (ProviderState := ProviderState) source decision previous)) startup
  let continuationGame : ProbComp (Bool × Platform) := do
    let initialized ← (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys seed)).run (PqxdhRecordLiftWorld.initial (n := budget.cap 4 + budget.cap 5))
    observation source decision previous <$> RegistrationNativePlatformG3RecordCoupling.hidden setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
      (body setup checks wire source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget seed scalar candidate materials previous initialized.1) initialized.2
  have actualEq : actual setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous ensureInit identityIndex = continuationGame := by
    simpa only [actual,continuationGame,publicProgram,RegistrationNativePlatformG3RecordCoupling.hidden,
      simulateQ_bind,StateT.run_bind,map_bind] using observed
  refine Eq.trans ?_ actualEq.symm
  unfold after continuationGame
  apply bind_congr
  rintro ⟨_ | started,reached⟩
  · simp only [RegistrationNativePlatformG3UniformOpaqueAfter.hidden,RegistrationNativePlatformG3RecordCoupling.hidden,body,simulateQ_pure,StateT.run_pure,map_pure,observation]
  · have stage := hidden_source setup checks wire route source serverKeyId provider providerState selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget seed scalar candidate materials previous started reached
    simpa only [RegistrationNativePlatformG3RecordCoupling.hidden,body,simulateQ_map,StateT.run_map,
      Functor.map_map,observation] using stage

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.work_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.work_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.hidden_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative.after_source
