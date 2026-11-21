-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicPairedSafety
/-! A marked guarded audit is witnessed by a repeated-role event in that same complete source tree and the same reached private/World state. The actual corrected frontend supplies paired safety separately by its checked source theorem. No older complete frontend is substituted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {I KemSK ProviderState Reader Response A : Type} {base : OracleSpec I}
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

variable (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n)
noncomputable def traced :=
  RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program work)).run (cold frame materials)) world
noncomputable def original :=
  RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      work).run (cold frame materials)) world
noncomputable def known :=
  RegistrationNativeG3GuardedCoupling.known setup codec route seeds
    ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program work)).run (cold frame materials)) world

/-- Every marked supported source outcome has its ordered repeat witness in that same chronology, with full private and World state. -/
theorem trace_repeat (safe : RegistrationNativePairedTrace.Safe work)
    (unused : ∀ slot role, world.used slot role = false)
    (result : (((A × RegistrationNativeG2Trace.State) × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × (PqxdhRecordLiftWorld.State n × Bool)))
    (supported : result ∈ support (traced setup codec route seeds wire sign seed scalar candidate provider work frame materials world))
    (marked : result.2.2 = true) : RegistrationNativeG2Trace.RepeatedRoleAttempt input selected result.1.1.2.events := by
  let before : RegistrationNativeG3AuditTrace.State n KemSK ProviderState :=
    ((RegistrationNativePairedTrace.initial, cold frame materials), (world, false))
  have exactSource := RegistrationNativeG3AuditTraceSource.trace_source setup codec route seeds wire sign seed scalar candidate provider work before
  have same : (fun actual => (((actual.1, actual.2.1.1.trace), actual.2.1.2), actual.2.2)) <$>
      (simulateQ (RegistrationNativeG3AuditTrace.handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      traced setup codec route seeds wire sign seed scalar candidate provider work frame materials world := by
    simpa only [traced, RegistrationNativeG3GuardedCoupling.audit, RegistrationNativeG3AuditQuiet.world,
      QueryImpl.simulateQ_compose, RegistrationNativeG2Trace.program, before, RegistrationNativePairedTrace.initial] using exactSource
  rw [← same, support_map] at supported
  obtain ⟨actual, reached, equal⟩ := supported
  have clean := safe before.1.1 (actual.1, actual.2.1.1) rfl
    (RegistrationNativeG3AuditTraceSource.open_support setup codec route seeds wire sign seed scalar candidate provider work before actual reached)
  have valid := RegistrationNativeG3AuditTraceRun.program_good setup codec route seeds wire sign seed scalar candidate provider work before
    (cold_good setup seed scalar candidate frame materials world unused) actual reached clean
  have flagged : actual.2.2.2 = true := by simpa only [← equal] using marked
  simpa only [← equal] using valid.2.2 flagged

private theorem audit_map {V W : Type} (observe : V → W)
    (tree : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) V) (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeG3GuardedCoupling.audit setup codec route seeds (observe <$> tree) before =
      Prod.map observe id <$> RegistrationNativeG3GuardedCoupling.audit setup codec route seeds tree before := by
  simp only [RegistrationNativeG3GuardedCoupling.audit, simulateQ_map, StateT.run_map]
  rfl

/-- Erasing only the actual G2 chronology recovers the original marked source execution exactly. -/
theorem erase_source :
    original setup codec route seeds wire sign seed scalar candidate provider work frame materials world =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        traced setup codec route seeds wire sign seed scalar candidate provider work frame materials world := by
  have erased := congrArg (fun tree =>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) tree).run (cold frame materials))
    (RegistrationNativeG2Trace.program_erase work RegistrationNativeG2Trace.initial)
  simp only [simulateQ_map, StateT.run_map] at erased
  have actual := congrArg (fun tree => RegistrationNativeG3GuardedCoupling.audit setup codec route seeds tree world) erased.symm
  rw [audit_map] at actual
  simpa only [original, traced, RegistrationNativeG2Trace.program, Functor.map_map, Prod.map_def, id_eq] using actual

/-- The known side retains the literal source result and chronology while dropping only the guarded audit observation. -/
theorem known_source :
    known setup codec route seeds wire sign seed scalar candidate provider work frame materials world =
      Prod.fst <$> traced setup codec route seeds wire sign seed scalar candidate provider work frame materials world :=
  RegistrationNativeG3GuardedMarkedKnown.materialized_source setup codec route seeds _ world

/-- The actual marked probability is bounded by the same-run selected-input repeat event; no extra owner union is taken. -/
theorem mark_bound (safe : RegistrationNativePairedTrace.Safe work)
    (unused : ∀ slot role, world.used slot role = false) :
    Pr{let result ← original setup codec route seeds wire sign seed scalar candidate provider work frame materials world}[result.2.2 = true] ≤
      Pr{let result ← known setup codec route seeds wire sign seed scalar candidate provider work frame materials world}[
        RegistrationNativeG2Trace.RepeatedRoleAttempt input selected result.1.2.events] := by
  rw [erase_source, known_source, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result reached marked
  exact trace_repeat setup codec route seeds wire sign seed scalar candidate provider work frame materials world safe unused result reached marked
end BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.trace_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.trace_repeat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.erase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.erase_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.mark_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit.mark_bound
