-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity
import BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformStartupAuditBound

/-! Independent genuine KEM-prior draws commute with the actual native startup in distribution, retaining its literal reached World. Thus the averaged record-bound audit is exactly the existing whole-startup recovery audit; no extra KEM or independence allowance is charged. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))

/-- The record target's averaged original audit is exactly the same actual startup-inclusive uniform audit in distribution. -/
theorem audit_source :
    RegistrationNativeSelectiveRecordTraceUniformSecurity.audit (n := budget.cap 4 + budget.cap 5) setup checks wire route source
      ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected =ᵈ
      RegistrationNativeG3NativeUniformStartupAuditBound.audit setup checks wire source route ensureInit identityIndex serverKeyId
        selectedAccept bounds .P adversary budget selected := by
  simp only [RegistrationNativeSelectiveRecordTraceUniformSecurity.audit,
    RegistrationNativeSelectiveRecordTraceUniformSecurity.prior,
    RegistrationNativeSelectiveRecordTraceUniformSecurity.fixedAudit,
    RegistrationNativeG3NativeUniformStartupAuditBound.audit, RegistrationNativeG3NativeStartupAlias.prior,
    RegistrationNativeG3MaterializedStartup.audit, bind_assoc, pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  let family := RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let startup := RegistrationNativeG3MaterializedStartup.startup (n := budget.cap 4 + budget.cap 5)
    setup wire route source ensureInit identityIndex serverKeyId seed
  let next := fun (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : MlKemSharedSecret)
      (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) =>
    RegistrationNativeG3MaterializedStartup.auditAfter setup checks wire route source serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
      none selected.val selectedAccept bounds .P adversary initialized
  change (family >>= fun profile => ($ᵗ MlKemSharedSecret) >>= fun candidate => startup >>= next profile candidate) =ᵈ
    (startup >>= fun initialized => family >>= fun profile => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized)
  calc
    _ =ᵈ (family >>= fun profile => startup >>= fun initialized => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized) := by
      apply _root_.EvalDistEq.bind_right
      intro profile
      exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ MlKemSharedSecret) startup (fun candidate initialized => next profile candidate initialized)
    _ =ᵈ _ := OracleComp.EvalDistEq.bind_bind_swap family startup
      (fun profile initialized => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized)

/-- One whole-prior recovery adversary bounds the record target's same averaged cold audit, with no additional KEM loss. -/
theorem audit_bound (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let marked ← (RegistrationNativeSelectiveRecordTraceUniformSecurity.audit (n := budget.cap 4 + budget.cap 5) setup checks wire route source
      ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected)}[marked = true] ≤
      RegistrationNativeG3NativeUniformStartupAuditBound.loss setup checks wire source route ensureInit identityIndex serverKeyId
        selectedAccept bounds .P adversary budget selected := by
  rw [(audit_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected).prEvent_eq]
  exact RegistrationNativeG3NativeUniformStartupAuditBound.bound setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds .P adversary budget bounded selected

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit.audit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit.audit_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit.audit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit.audit_bound
