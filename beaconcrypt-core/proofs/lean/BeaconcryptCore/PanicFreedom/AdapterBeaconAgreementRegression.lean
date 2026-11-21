-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterBeaconAgreementSafety
import BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish

/-! A direct RustM regression model with divergent generation and panicking encapsulation. Its genuine, pin-aligned Beacon entry starts at nonterminal rank eight and remains normal under the reached-leaf contracts. Arbitrary generation phases still diverge. This tests source control coverage, without claiming correspondence between this model and native cryptography. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom.AdapterBeaconAgreementRegression
open Refinement AdapterNormal beaconcrypt_public_wrapper
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]

@[instance_reducible] def unusedEntropy : PublicWrapperPlatform.CryptoOperations := {
  crypto with
  kxGenerate := fun _ _ => div
  encapsulate := fun _ _ _ => fail .panic
}

theorem reached_contracts (contracts : AdapterBeaconAgreementSafety.Contracts) :
    letI := unusedEntropy
    AdapterBeaconAgreementSafety.Contracts := by
  rcases contracts with ⟨parse, kxSecretBytes, convertPublic, convertSecret, scalarMult,
    kemCipherFromBytes, kemSharedBytes, decapsulate, extract, expand⟩
  let _ := unusedEntropy (crypto := crypto)
  exact {
    parse := parse
    kxSecretBytes := kxSecretBytes
    convertPublic := convertPublic
    convertSecret := convertSecret
    scalarMult := scalarMult
    kemCipherFromBytes := kemCipherFromBytes
    kemSharedBytes := kemSharedBytes
    decapsulate := decapsulate
    extract := extract
    expand := expand }

theorem generation_diverges {R E : Type} (generator : rand_core.TryCryptoRng R E) (rng : R) :
    unusedEntropy.kxGenerate generator rng = div := rfl

theorem encapsulation_panics {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (key : beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey) (rng : R) :
    unusedEntropy.encapsulate generator key rng = fail .panic := rfl

theorem generation_body_diverges {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : pqxdh.RegistrationKeys) (pending : agreement.EphemeralPending) (rng : R) :
    letI := unusedEntropy
    AdapterPublicAgreementSourceLoop.body generator keys (.GenerateEphemeral pending, rng, none, none) = div := rfl

omit material primitive crypto in
def alignedResponse (authenticated : registration.AuthenticatedResponse) : registration.AuthenticatedResponse :=
  { authenticated with control :=
      { authenticated.control with expected_server_binding :=
          authenticated.binding.server_pin.binding } }

omit material primitive crypto in
theorem aligned_entry_rank_eight (authenticated : registration.AuthenticatedResponse) :
    ∃ initial, agreement.begin_beacon_agreement (alignedResponse authenticated) = ok initial ∧
      RegistrationAgreementExecutor.rank initial = 8 := by
  obtain ⟨initial, started⟩ := KeyAgreement.begin_beacon_agreement_total (alignedResponse authenticated)
  refine ⟨initial, started, ?_⟩
  simp [alignedResponse, agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
    pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
    session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
    PqxdhRefinement.array_eq_abs, agreement.AgreementState.new, ratchet.RatchetChain.from_bytes] at started
  subst initial
  rfl

theorem entry_normal (contracts : AdapterBeaconAgreementSafety.Contracts)
    (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (keys : pqxdh.RegistrationKeys)
    (started : agreement.begin_beacon_agreement authenticated = ok initial) :
    letI := unusedEntropy
    Normal (pqxdh.execute_beacon_agreement initial keys) := by
  have selected := reached_contracts contracts
  let _ := unusedEntropy (crypto := crypto)
  exact AdapterBeaconAgreementSafety.execute_beacon_agreement_entry_total selected authenticated initial keys started

theorem nonterminal_entry_normal (contracts : AdapterBeaconAgreementSafety.Contracts)
    (authenticated : registration.AuthenticatedResponse) (keys : pqxdh.RegistrationKeys) :
    letI := unusedEntropy
    ∃ initial, agreement.begin_beacon_agreement (alignedResponse authenticated) = ok initial ∧
      RegistrationAgreementExecutor.rank initial = 8 ∧ Normal (pqxdh.execute_beacon_agreement initial keys) := by
  obtain ⟨initial, started, rank⟩ := aligned_entry_rank_eight authenticated
  exact ⟨initial, started, rank, entry_normal contracts (alignedResponse authenticated) initial keys started⟩

variable [platform : PublicWrapperPlatform.Platform]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [codec : PublicWrapperPlatform.Codecs]

theorem finish_contracts (contracts : AdapterPublicBeaconFinish.Contracts) :
    letI := unusedEntropy
    AdapterPublicBeaconFinish.Contracts := by
  rcases contracts with ⟨agreement, record, response, decode, initialKdf⟩
  have selected := reached_contracts agreement
  let _ := unusedEntropy (crypto := crypto)
  exact {
    agreement := selected
    record := record
    response := response
    decode := decode
    initialKdf := initialKdf }

theorem finish_preserves (contracts : AdapterPublicBeaconFinish.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : AdapterPublicOrdinary.ValidBeacon self) :
    letI := unusedEntropy
    Ensures (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes)
      (fun result => AdapterPublicOrdinary.ValidBeacon result.2) := by
  have selected := finish_contracts contracts
  let _ := unusedEntropy (crypto := crypto)
  exact AdapterPublicBeaconFinish.finish_registration_preserves selected self bytes valid

theorem finish_total (contracts : AdapterPublicBeaconFinish.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) :
    letI := unusedEntropy
    Normal (beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes) := by
  have selected := finish_contracts contracts
  let _ := unusedEntropy (crypto := crypto)
  exact AdapterPublicBeaconFinish.finish_registration_total selected self bytes

end BeaconcryptCore.PanicFreedom.AdapterBeaconAgreementRegression
