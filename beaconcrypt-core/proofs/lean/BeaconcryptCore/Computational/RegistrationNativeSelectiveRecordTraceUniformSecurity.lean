-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity
import BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound

/-! The selected native target bound is averaged over the same independent Server seed, prekey scalar, reserved KEM family/challenge and uniform mathematical candidate. Actual effectful startup remains inside each continuation. The record losses are displayed as their literal prior expectation; no average of primitive advantages is replaced by an unconstructed adversary. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordBills (programBill)
open RegistrationNativeRecordViewCrypto (chainLoss authLoss privacyLoss)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

structure Context (KemSK : Type) where
  seed : PqxdhJointIdentity.IdentitySeed
  scalar : PqxdhJointGapDh.ScalarBytes
  profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK
  candidate : PqxdhKemIndCca.MlKemSharedSecret

noncomputable def prior (setup : Setup base KemSK) (budget : PqxdhDeploymentInterface.Budget)
    (selected : Fin (budget.create + 1)) : ProbComp (Context KemSK) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  pure ⟨seed, scalar, profile, candidate⟩

noncomputable def provider (setup : Setup base KemSK) (selected : Nat) (context : Context KemSK) :=
  RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected context.profile.pairs
    context.profile.publicKey context.profile.challenge context.candidate

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
  (claim : Value → Option (Nat × Pqxdh.Bytes))

noncomputable def fixedFull (context : Context KemSK) : ProbComp Bool :=
  RegistrationNativeSelectiveRecordTraceTarget.event setup context.seed context.scalar context.candidate claim <$>
    RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      context.seed context.scalar context.candidate (provider setup selected.val context) none selected.val selectedAccept bounds .P adversary

noncomputable def fixedAudit (context : Context KemSK) : ProbComp Bool :=
  RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup selected.val context) none selected.val selectedAccept bounds .P adversary

noncomputable def full : ProbComp Bool := prior setup budget selected >>=
  fixedFull (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim

noncomputable def audit : ProbComp Bool := prior setup budget selected >>=
  fixedAudit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def fixedLoss (context : Context KemSK) : ℝ≥0∞ :=
  let work := RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup selected.val context) none selected.val selectedAccept bounds .P adversary
  let observe := RegistrationNativeRecordViewFresh.event claim
  chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe hmac +
    authLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe fallback
      (programBill budget bounds allowance constructorCoins mlCoins .hash) (programBill budget bounds allowance constructorCoins mlCoins .raw) +
    privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route work budget observe

noncomputable def recordLoss : ℝ≥0∞ :=
  ∑' context, Pr{let sampled ← prior setup budget selected}[sampled = context] *
    fixedLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim
      allowance constructorCoins mlCoins hmac fallback context

/-- The same entire uniform challenge prior preserves coefficient one for the fresh-byte term, original cold repeat audit and literal expected record losses. -/
theorem bound
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ context ∈ support (prior setup budget selected), RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source
      context.seed context.scalar context.candidate (provider setup selected.val context) selected.val selectedAccept allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac) :
    Pr{let won ← full (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim}[won = true] ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
      Pr{let marked ← audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected}[marked = true] +
      recordLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim
        allowance constructorCoins mlCoins hmac fallback := by
  classical
  have pointwise (context : Context KemSK) (supported : context ∈ support (prior setup budget selected)) :
      Pr{let won ← fixedFull (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim context}[won = true] ≤
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
        Pr{let marked ← fixedAudit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected context}[marked = true] +
        fixedLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim
          allowance constructorCoins mlCoins hmac fallback context := by
    simpa only [fixedFull, prEvent_map, RegistrationNativeSelectiveRecordTraceTarget.event, decide_eq_true_eq,
      fixedAudit, fixedLoss, add_assoc] using
      RegistrationNativeSelectiveRecordTraceSecurity.bound (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        context.seed context.scalar context.candidate (provider setup selected.val context) none selected.val selectedAccept bounds adversary
        budget bounded allowance (framed context supported) constructorCoins mlCoins constructorBound mlBound claim hmac correct fallback
  unfold full audit recordLoss
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' context, Pr{let sampled ← prior setup budget selected}[sampled = context] *
        (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
          Pr{let marked ← fixedAudit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected context}[marked = true] +
          fixedLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim
            allowance constructorCoins mlCoins hmac fallback context) :=
      ENNReal.tsum_le_tsum fun context => by
        by_cases supported : context ∈ support (prior setup budget selected)
        · exact mul_le_mul' le_rfl (pointwise context supported)
        · simp only [prEvent_eq_zero_of_not_mem_support _ supported, zero_mul, le_refl]
    _ = (∑' context, Pr{let sampled ← prior setup budget selected}[sampled = context]) * (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹) +
        (∑' context, Pr{let sampled ← prior setup budget selected}[sampled = context] *
          Pr{let marked ← fixedAudit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected context}[marked = true]) +
        (∑' context, Pr{let sampled ← prior setup budget selected}[sampled = context] *
          fixedLoss (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept bounds adversary budget selected claim
            allowance constructorCoins mlCoins hmac fallback context) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply add_le_add _ le_rfl
      simpa only [one_mul] using
        mul_le_mul_left (OracleComp.tsum_prEvent_le_one (prior setup budget selected)) (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity.bound
