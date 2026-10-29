-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource
import BeaconcryptCore.Computational.RegistrationNativePairedFrontend

/-! The complete guarded selective execution retains its actual dictionary and ordered native repetition witness through every adaptive callback. Clean paired provenance is discharged by the actual full native frontend, and its cold allocator starts injective independently of material bytes, KEM provider state and public outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeG3AuditTrace (State handler)
open RegistrationNativeG3AuditTraceInvariant (Good)
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

/-- Cold key-service startup retains the whole caller's ordinary KEM/signing frame and the actual completed material cache. -/
def cold (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache) :
    RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState :=
  ({ frame.1 with keys := { RegistrationNativeHiddenService.initial with materials } }, frame.2)

private theorem initial_good (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n) (unused : ∀ slot role, world.used slot role = false) :
    Good input selected RegistrationNativePairedTrace.initial (cold frame materials) (world, false) := by
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

/-- Every actual supported adaptive continuation preserves the chronological same-input audit invariant. -/
theorem program_good (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState)
    (valid : Good input selected before.1.1 before.1.2 before.2) (result : Value × State n KemSK ProviderState)
    (supported : result ∈ support ((simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before))
    (clean : result.2.1.1.bad = false) : Good input selected result.2.1.1 result.2.1.2 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, actual, continued⟩ := supported
      have opened := RegistrationNativeG3AuditTraceSource.open_support setup codec route seeds wire sign seed scalar candidate provider
        (next middle.1) middle.2 result continued
      have currentClean := RegistrationNativePairedEvents.clean_before (next middle.1) middle.2.1.1 (result.1, result.2.1.1) opened clean
      exact ih middle.1 middle.2
        (RegistrationNativeG3AuditTrace.query_good setup codec route seeds wire sign seed scalar candidate provider query before valid middle actual currentClean)
        continued

/-- The actual complete native frontend derives clean paired provenance on this same closed audited result. -/
theorem frontend_clean (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source)
    (before : State n KemSK ProviderState) (clean : before.1.1.bad = false)
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × State n KemSK ProviderState)
    (supported : result ∈ support ((simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider)
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run before)) :
    result.2.1.1.bad = false := by
  exact RegistrationNativePairedFrontend.run setup checks wire sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front
    before.1.1 (result.1, result.2.1.1) clean
    (RegistrationNativeG3AuditTraceSource.open_support setup codec route seeds wire sign seed scalar candidate provider _ before result supported)

/-- A marked audit in the actual complete original native frontend has an ordered same-selected-input installation/later-attempt witness in its same chronological execution. -/
theorem frontend_repeat (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n) (unused : ∀ slot role, world.used slot role = false)
    (value : (Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source)
    (afterPrivate : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (afterWorld : PqxdhRecordLiftWorld.State n)
    (supported : ((value, afterPrivate), (afterWorld, true)) ∈ support
      (RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run
            (cold frame materials)) world)) :
    ∃ trace, (value, ((trace, afterPrivate), (afterWorld, true))) ∈ support
      ((simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider)
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run
          ((RegistrationNativePairedTrace.initial, cold frame materials), (world, false))) ∧
      RegistrationNativeG2Trace.RepeatedRoleAttempt input selected trace.trace.events := by
  let before : State n KemSK ProviderState := ((RegistrationNativePairedTrace.initial, cold frame materials), (world, false))
  rw [← RegistrationNativeG3AuditTraceSource.audit_source setup codec route seeds wire sign seed scalar candidate provider
    _ before rfl, support_map] at supported
  obtain ⟨result, actual, equal⟩ := supported
  have clean := frontend_clean setup codec route seeds wire sign seed scalar candidate provider checks source
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front before rfl result actual
  have valid := program_good setup codec route seeds wire sign seed scalar candidate provider _ before
    (initial_good setup seed scalar candidate frame materials world unused) result actual clean
  rcases result with ⟨found, ⟨⟨trace, privateState⟩, ⟨reachedWorld, flag⟩⟩⟩
  simp only [Prod.mk.injEq] at equal
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := equal
  exact ⟨trace, actual, valid.2.2 rfl⟩

/-- The actual marked native run has its ordered repeat witness in the literal G2 trace under that same selective/World execution, with the original result, ledger, frontend and private state unchanged. -/
theorem frontend_repeat_trace (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePublicFrontend.State source)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n) (unused : ∀ slot role, world.used slot role = false)
    (value : (Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source)
    (afterPrivate : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (afterWorld : PqxdhRecordLiftWorld.State n)
    (supported : ((value, afterPrivate), (afterWorld, true)) ∈ support
      (RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run
            (cold frame materials)) world)) :
    ∃ trace, (((value, trace), afterPrivate), (afterWorld, true)) ∈ support
      (RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          (RegistrationNativeG2Trace.program
            (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
              (cold frame materials)) world) ∧
      RegistrationNativeG2Trace.RepeatedRoleAttempt input selected trace.events := by
  obtain ⟨trace, actual, repeated⟩ := frontend_repeat setup codec route seeds wire sign seed scalar candidate provider checks source
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame materials world unused value afterPrivate afterWorld supported
  refine ⟨trace.trace, ?_, repeated⟩
  have mapped := Set.mem_image_of_mem
    (fun result => (((result.1, result.2.1.1.trace), result.2.1.2), result.2.2)) actual
  rw [← support_map] at mapped
  change (((value, trace.trace), afterPrivate), (afterWorld, true)) ∈ support
    ((fun result => (((result.1, result.2.1.1.trace), result.2.1.2), result.2.2)) <$>
      (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider)
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)).run
          ((RegistrationNativePairedTrace.initial, cold frame materials), (world, false))) at mapped
  rw [RegistrationNativeG3AuditTraceSource.trace_source] at mapped
  simpa only [RegistrationNativeG3GuardedCoupling.audit, RegistrationNativeG3AuditQuiet.world,
    QueryImpl.simulateQ_compose, RegistrationNativeG2Trace.program, RegistrationNativePairedTrace.initial] using mapped

end BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_clean
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_repeat
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_repeat_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceRun.frontend_repeat_trace
