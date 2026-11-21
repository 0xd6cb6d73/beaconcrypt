-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The actual genuine startup and current gated native run retain cross-handle commitment evidence in the same warmed CTX cache. The resulting bound includes both directions and all later source callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (route : RawCtxServerRouting.SenderDecoder)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "reference" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "FullResult" => RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState Platform source) Value

omit primitive in
private def project (result : ((RegistrationNativeEntropyRun.Outcome (State n KemSK ProviderState Platform source) Value ×
    CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n) : FullResult :=
  ((result.1.1.1,result.1.2),result.2)

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) : ProbComp FullResult :=
  project source <$> CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route reference
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial

/-- Splitting the actual warm startup retains the complete reached shell, control and cache before the native continuation. -/
theorem run_start (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace = (do
      let initialized ← CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial
      match initialized.1.1.1 with
      | none => pure ((none, initialized.1.2), initialized.2)
      | some born =>
          RegistrationNativePlatformGatedNativeEntropy.run modes replace setup codec route
            (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
            (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) serverKeyId bounds mode
            (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) born.created
            ((born.native.frontend,previous),privateBefore) initialized.1.1.2 initialized.1.2 initialized.2) := by
  rw [run, RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram,
    CborRawRecordOriginFlatten.interpret_bind, map_bind]
  apply bind_congr
  rintro ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · simp only [CborRawRecordOriginFlatten.interpret_pure, map_pure, project]
  · rfl

/-- Erasing only the outer cursor shell preserves the complete current source startup, native ledger, private cache and platform state in this run. -/
theorem source_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    project source <$> CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route
      (RegistrationNativePlatformSelectiveEntropyStartup.program (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial =
    run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace := by
  rw [RegistrationNativePlatformSelectiveEntropyStartup.program_source]
  rfl

/-- The complete source reference after genuine startup derives cross-handle conflict in its own final private cache. No ledger, cache or source-frame premise is supplied. -/
theorem cross_conflict (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : FullResult)
    (supported : result ∈ support (run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept codec route (RegistrationNativeRecordBindingEvent.view result)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2 := by
  rw [run, support_map] at supported
  obtain ⟨full, possible, rfl⟩ := supported
  unfold RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram at possible
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at possible
  obtain ⟨started, startReached, continued⟩ := possible
  rcases started with ⟨⟨⟨_ | born, shell⟩, control⟩, secret⟩
  · simp only [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at continued
    subst full
    simp only [RegistrationNativeRecordBindingEvent.view, project, PqxdhRecordLiftIdeal.CrossAccept,
      Option.map_none] at crossed
    obtain ⟨value, member, _⟩ := crossed
    cases member
  · have safe := (RegistrationNativeRecordHandleSlots.interpreted
      (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route _ _ _
      PqxdhRecordLiftProtocolHistory.initial_safe _ _ startReached).1
    apply RegistrationNativePlatformGatedNativeRecordBindingEvent.initialized_conflict modes ideal replace setup codec route readback
      (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) born.created
      ((born.native.frontend,previous),privateBefore) shell control safe secret (project source full) _ crossed
    rw [RegistrationNativePlatformGatedNativeEntropy.run, support_map]
    exact ⟨full, continued, rfl⟩

private theorem conflict_source (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    (fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace =
    (fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
        (RegistrationNativeRecordOriginProgram.program codec route reference)).run CtxPrivate.initial := by
  simp only [run, project, RegistrationNativeRecordOriginProgram.program, RegistrationNativeRecordPackage.client,
    CborRecordWorldClient.client, PqxdhRecordLiftProtocol.schedule, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- Actual complete warm source seal/hash bills bound commitment conflict in the same final private cache. -/
theorem conflict_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (RegistrationNativeRecordPackage.client reference))
    (hashCap : Nat) (hashes : PqxdhRecordLiftCtxProgramBounds.Weighted (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash)
      (RegistrationNativeRecordOriginProgram.program codec route reference) hashCap) :
    𝒟[(fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  rw [conflict_source]
  exact RegistrationNativeRecordBindingSource.conflict_bound modes replace setup codec route reference ideal budget records hashCap hashes

/-- Both cross-handle directions in the same warm native run consume one shared commitment-collision term, including publications after reception. -/
theorem cross_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (budget : PqxdhDeploymentInterface.Budget)
    (records : PqxdhRecordLiftLaterWorlds.RecordBounded budget (RegistrationNativeRecordPackage.client reference))
    (hashCap : Nat) (hashes : PqxdhRecordLiftCtxProgramBounds.Weighted (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash)
      (RegistrationNativeRecordOriginProgram.program codec route reference) hashCap) :
    𝒟[(fun result => PqxdhRecordLiftIdeal.crossEvent codec route (RegistrationNativeRecordBindingEvent.view result)) <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace] {true} ≤
      ((budget.sends * (budget.sends + hashCap) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  apply le_trans _ (conflict_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes ideal replace budget records hashCap hashes)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result supported crossed
  exact @decide_eq_true _ (Classical.propDecidable _) (cross_conflict setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes ideal replace readback
    result supported (@of_decide_eq_true _ (Classical.propDecidable _) crossed))

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.source_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.cross_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.cross_conflict

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.conflict_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.cross_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.cross_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.run_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup.run_start
