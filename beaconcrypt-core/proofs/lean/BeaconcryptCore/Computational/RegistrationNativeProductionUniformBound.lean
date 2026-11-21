-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProductionPrior
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformAudit

/-! The whole uniform native target game has its actual selected installation ordinal, actual physical hidden origin and permitted record view. One whole-startup recovery loss pays the concrete repeat audit, and the actual record reductions reach literal fresh-byte entropy. No further KEM comparison is made on this uniform side. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProductionUniformBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
  (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def loss : ℝ≥0∞ :=
  ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
  RegistrationNativeG3NativeUniformStartupAuditBound.loss setup checks wire source route ensureInit identityIndex serverKeyId
    target.1.val bounds .P adversary budget target.2 +
  RegistrationNativeSelectiveRecordTraceUniformSecurity.recordLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source
    ensureInit identityIndex serverKeyId target.1.val bounds adversary budget target.2 claim allowance constructorCoins mlCoins setup.hmac fallback

/-- The genuine uniform whole-client target probability has its explicit repeat, record cryptographic and byte-accurate entropy bound. -/
theorem bound (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (framed : ∀ context ∈ support (RegistrationNativeSelectiveRecordTraceUniformSecurity.prior setup budget target.2),
      RegistrationNativeSelectiveRecordFrame.Frame (n := budget.cap 4 + budget.cap 5) setup checks wire source
        context.seed context.scalar context.candidate (RegistrationNativeSelectiveRecordTraceUniformSecurity.provider setup target.2.val context)
        target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) :
    Pr{let won ← (RegistrationNativeProductionPrior.uniform setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)}[won = true] ≤
      loss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins fallback := by
  rw [(RegistrationNativeG3NativeTargetUniformSource.uniform_source setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary
    budget target claim bounded).prEvent_eq]
  have selected := RegistrationNativeG3NativeTargetUniform.probability setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
    bounded readback responseReadback
  have record := RegistrationNativeSelectiveRecordTraceUniformSecurity.bound (n := budget.cap 4 + budget.cap 5) setup checks wire route source
    ensureInit identityIndex serverKeyId target.1.val bounds adversary budget target.2 claim allowance constructorCoins mlCoins setup.hmac fallback
    bounded framed constructorBound mlBound correct
  have repeated := RegistrationNativeSelectiveRecordTraceUniformAudit.audit_bound setup checks wire route source ensureInit identityIndex serverKeyId
    target.1.val bounds adversary budget target.2 bounded
  exact selected.trans (record.trans (add_le_add (add_le_add le_rfl repeated) le_rfl))

end BeaconcryptCore.Computational.RegistrationNativeProductionUniformBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProductionUniformBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProductionUniformBound.bound
