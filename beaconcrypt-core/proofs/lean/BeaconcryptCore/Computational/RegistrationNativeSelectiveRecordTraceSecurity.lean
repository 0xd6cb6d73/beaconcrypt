-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFreshSecurity
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound

/-! A concrete selected native target in the complete known108 execution reaches the same actual selective hidden-handle observation, then the literal all-random entropy endpoint. The loss consists of the original startup-averaged repeat audit and the three original billed record reductions, with one fresh-byte term. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordStartup (program)
open RegistrationNativeSelectiveRecordBills (programBill)
open RegistrationNativeRecordViewCrypto (chainLoss authLoss privacyLoss)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
  (allowance : Fin 14 → EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
  (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "actualWork" => program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
  selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "observation" => RegistrationNativeRecordViewFresh.event claim

include bounded framed constructorBound mlBound in
/-- The complete original cold known108 target event has the explicit repeat, record cryptographic and fresh-byte bound. -/
theorem bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary)}[
        RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome] ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
      Pr{let bad ← (RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary)}[bad = true] +
      chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation hmac +
      authLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation fallback
        (programBill budget bounds allowance constructorCoins mlCoins .hash) (programBill budget bounds allowance constructorCoins mlCoins .raw) +
      privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation := by
  classical
  let selectedEvent := RegistrationNativeSelectiveRecordTraceTarget.event (source := source) setup seed scalar candidate claim
  let full := RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary
  let actual := RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary
  have repeated := RegistrationNativeG3MaterializedTracedStartupBound.bound (n := n) setup checks wire route source serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds .P adversary ensureInit identityIndex
  rw [RegistrationNativeG3MaterializedTracedStartup.audit_source] at repeated
  have projected := (ENNReal.ofReal_le_ofReal ((boolDistance_le_discreteDistance _ _).trans
    (discreteDistance_map_le selectedEvent full actual))).trans repeated
  have attached := RegistrationNativeSelectiveRecordTraceTarget.actual_probability (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary claim
  rw [prEvent_eq_evalDist_decide, prEvent_eq_evalDist_decide] at attached
  simp only [bind_pure_comp] at attached
  change 𝒟[selectedEvent <$> actual] {true} ≤
    𝒟[observation <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route actualWork] {true} at attached
  have fresh := RegistrationNativeSelectiveRecordFreshSecurity.bound setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
    provider providerState selectedOwner selectedAccept bounds adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound claim
    hmac correct fallback
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (selectedEvent <$> full) (selectedEvent <$> actual)
  rw [prEvent_eq_evalDist_decide, bind_pure_comp]
  change 𝒟[selectedEvent <$> full] {true} ≤ _
  exact compared.trans (by simpa only [add_assoc, add_comm, add_left_comm] using add_le_add (attached.trans fresh) projected)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceSecurity.bound
