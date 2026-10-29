-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient

/-! Candidate-equal literals at actual installation events or failed installation attempts are bounded in the complete original alias client. The bound uses its concrete recovery adversary and the original build-plus-finish allowance; the same-run service proof derives the link to its literal-query log internally. The additional suffix-key primitive assumption remains explicit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativeSecretWordFrontendTrace (Event)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Exposure (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (candidate : Secret) (trace : RegistrationNativeSecretWordFrontendTrace.State) : Prop :=
  ∃ role message key, (Event.install role message ∈ trace.events ∨ Event.installAttempt role message ∈ trace.events) ∧
    input message = some key ∧ inside key.head = true ∧ key.word = .literal candidate

/-- One explicit ordinary suffix-key recovery advantage bounds all concrete valid protected literal exposures in the full chronological original client. -/
theorem bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativeSecretWordMessage.State source) (empty : front.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    let actual := RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem
    Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[Exposure input inside pair.1 pair.2.1.1.2] ≤
      ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  let actual := RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem
  have included : Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[Exposure input inside pair.1 pair.2.1.1.2] ≤
      Pr{let pair ← (do
      let candidate ← $ᵗ Secret
      let result ← RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual
      pure (candidate, result))}[pair.1 ∈ pair.2.2.2] := by
    apply prEvent_mono_of_support
    intro pair supported exposed
    simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨candidate, _draw, result, possible, rfl⟩ := supported
    obtain ⟨role, message, key, member, realized, protectedInput, literal⟩ := exposed
    exact RegistrationNativeSecretWordAliasServiceClient.install_logged setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front empty ordinary kem candidate result possible
      role message key member realized protectedInput literal
  exact included.trans (RegistrationNativeSecretWordAliasClient.literal_hit_bound setup checks wire source route sign input inside provider
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front ordinary kem)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound.bound
