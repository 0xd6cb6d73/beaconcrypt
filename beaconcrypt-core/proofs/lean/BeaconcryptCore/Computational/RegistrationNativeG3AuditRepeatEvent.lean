-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun

/-! Every marked outcome of the actual full native frontend has its ordered repeat witness in that very same retained G2 chronology. The probability transport first preserves the joint traced execution exactly and then erases only the World audit bookkeeping; it never chooses an unrelated supported trace for an outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
  (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

local notation "input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

private theorem cold_good (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n) (unused : ∀ slot role, world.used slot role = false) :
    RegistrationNativeG3AuditTraceInvariant.Good input selected RegistrationNativePairedTrace.initial (cold frame materials) (world, false) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change RegistrationNativeHiddenServiceInvariant.Ordered RegistrationNativeHiddenService.initial ∧
      RegistrationNativeHiddenServiceInvariant.InjectiveSlots RegistrationNativeHiddenService.initial
    exact RegistrationNativeHiddenServiceInvariant.initial
  · intro message reference _active impossible
    cases impossible
  · intro slot role active
    rw [unused] at active
    cases active
  · intro impossible
    cases impossible

variable (checks : Checks) (source : RegistrationNativeMldsa.Source)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativePublicFrontend.State source)
  (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
  (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
  (world : PqxdhRecordLiftWorld.State n)

noncomputable def traced :=
  RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
          (cold frame materials)) world

noncomputable def original :=
  RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run
        (cold frame materials)) world

noncomputable def known :=
  RegistrationNativeG3GuardedCoupling.known setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
          (cold frame materials)) world

/-- A marked supported joint traced outcome has its ordered same-input role repeat in its own literal chronological trace, with all output and private state retained. -/
theorem trace_repeat (unused : ∀ slot role, world.used slot role = false)
    (result : (((((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) ×
      RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × (PqxdhRecordLiftWorld.State n × Bool)))
    (supported : result ∈ support (traced setup codec route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world))
    (marked : result.2.2 = true) :
    RegistrationNativeG2Trace.RepeatedRoleAttempt input selected result.1.1.2.events := by
  let before : RegistrationNativeG3AuditTrace.State n KemSK ProviderState :=
    ((RegistrationNativePairedTrace.initial, cold frame materials), (world, false))
  have exactSource := RegistrationNativeG3AuditTraceSource.trace_source setup codec route seeds wire sign seed scalar candidate provider
    (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front) before
  have same : (fun actual => (((actual.1, actual.2.1.1.trace), actual.2.1.2), actual.2.2)) <$>
      (simulateQ (RegistrationNativeG3AuditTrace.handler setup codec route seeds wire sign seed scalar candidate provider)
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run before =
      traced setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode work front frame materials world := by
    simpa only [traced, RegistrationNativeG3GuardedCoupling.audit, RegistrationNativeG3AuditQuiet.world,
      QueryImpl.simulateQ_compose, RegistrationNativeG2Trace.program, before, RegistrationNativePairedTrace.initial] using exactSource
  rw [← same, support_map] at supported
  obtain ⟨actual, reached, equal⟩ := supported
  have clean := RegistrationNativeG3AuditTraceRun.frontend_clean setup codec route seeds wire sign seed scalar candidate provider checks source
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front before rfl actual reached
  have valid := RegistrationNativeG3AuditTraceRun.program_good setup codec route seeds wire sign seed scalar candidate provider _ before
    (cold_good setup seed scalar candidate frame materials world unused) actual reached clean
  have flagged : actual.2.2.2 = true := by simpa only [← equal] using marked
  have repeated := valid.2.2 flagged
  simpa only [← equal] using repeated

private theorem audit_map {A B : Type} (map : A → B)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A) (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeG3GuardedCoupling.audit setup codec route seeds (map <$> work) before =
      Prod.map map id <$> RegistrationNativeG3GuardedCoupling.audit setup codec route seeds work before := by
  simp only [RegistrationNativeG3GuardedCoupling.audit, simulateQ_map, StateT.run_map]
  rfl

/-- Erasing only the actual final G2 chronology recovers the literal original marked full-ledger execution. -/
theorem erase_source :
    original setup codec route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        traced setup codec route seeds wire sign seed scalar candidate provider checks source
          selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world := by
  have erased := congrArg (fun program =>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) program).run (cold frame materials))
    (RegistrationNativeG2Trace.program_erase
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)
      RegistrationNativeG2Trace.initial)
  simp only [simulateQ_map, StateT.run_map] at erased
  have actual := congrArg (fun program => RegistrationNativeG3GuardedCoupling.audit setup codec route seeds program world) erased.symm
  rw [audit_map] at actual
  simpa only [original, traced, RegistrationNativeG2Trace.program, Functor.map_map, Prod.map_def, id_eq] using actual

/-- Forgetting only the World audit observation retains the exact native frontend, ledger, original G2 chronology and private selective state of the known materialized World execution. -/
theorem known_source :
    known setup codec route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world =
      Prod.fst <$> traced setup codec route seeds wire sign seed scalar candidate provider checks source
        selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world :=
  RegistrationNativeG3GuardedMarkedKnown.materialized_source setup codec route seeds _ world

/-- The actual repeated-role audit probability is bounded by the same selected-input repeat event in the actual known-side full-ledger chronological execution. -/
theorem mark_bound (unused : ∀ slot role, world.used slot role = false) :
    Pr{let result ← (original setup codec route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world)}[result.2.2 = true] ≤
      Pr{let result ← (known setup codec route seeds wire sign seed scalar candidate provider checks source
        selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world)}[
          RegistrationNativeG2Trace.RepeatedRoleAttempt input selected result.1.2.events] := by
  rw [erase_source, known_source, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result reached marked
  exact trace_repeat setup codec route seeds wire sign seed scalar candidate provider checks source
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world unused result reached marked

end BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.trace_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.trace_repeat
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.erase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.erase_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.known_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.mark_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent.mark_bound
