-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordPeerBinding
import BeaconcryptCore.Computational.RegistrationAuthenticationNative

/-!
The record world's public peer binding contains the actual native registration AD281. Native completion preserves this same binding, and a completely accepted Init supplies its source-derived fingerprint receipts. No ratchet initialization, first-send consumption or cryptographic security conclusion is assumed by these public metadata conversions.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationRecordBinding

open CtxRomAuth
open PqxdhRecordLiftInterface (PeerBinding)

attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

def ofRegistration (binding : session.RegistrationBinding) : PeerBinding :=
  ⟨binding.beacon_identity_public_key, some binding.associated_data⟩

theorem registration_associated_bytes (server : RawCtxServerRouting.Identity)
    (binding : session.RegistrationBinding) :
    (ofRegistration binding).associatedBytes server = absBytes binding.associated_data := by
  rfl

/-- The actual native completion operation transfers exactly the same peer identity and populated record AD. -/
theorem finish_native (binding : session.RegistrationBinding) (assigned : Std.U64)
    (established : session.SessionBinding) (finished : binding.finish assigned = .ok established) :
    PeerBinding.ofSession established = ofRegistration binding := by
  obtain ⟨result, ran, _, _, sameIdentity, _, _, sameAD, _⟩ :=
    BeaconcryptCore.Refinement.SessionBinding.finish_refines binding assigned
  have same : result = established := RustM.ok.inj (ran.symm.trans finished)
  cases same
  simp only [PeerBinding.ofSession, ofRegistration, sameIdentity, sameAD]

/-- Every complete accepted native Init supplies the exact populated AD that later record-world routing reads. -/
theorem accepted_associated_data {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before))
    (server : RawCtxServerRouting.Identity) :
    (ofRegistration authenticated.binding).associatedBytes server =
      BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
        (absBytes authenticated.binding.server_pin.binding.identity_public_key)
        (absBytes authenticated.binding.beacon_identity_public_key)
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes authenticated.binding.server_pin.public_key))
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes packet.mldsa_public_key)) := by
  rw [registration_associated_bytes]
  exact RegistrationAuthenticationNative.begin_associated_data crypto verify writer kdf pin packet
    before after events authenticated supported

/-- Installed record AD binds the originally selected server keys and the originally received beacon ML key through the actual shared fingerprints. -/
theorem accepted_selected_associated_data {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (verify : MldsaTranscriptAuth.Verify) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before))
    (server : RawCtxServerRouting.Identity) :
    (ofRegistration authenticated.binding).associatedBytes server =
      BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
        (absBytes pin.binding.identity_public_key) (absBytes authenticated.binding.beacon_identity_public_key)
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes pin.public_key))
        (MldsaSharedAuthentication.cacheHash after.2 (absBytes packet.mldsa_public_key)) := by
  have fields := RegistrationAuthenticationNative.begin_selected_pin crypto verify writer kdf pin packet
    before after events authenticated supported
  simpa only [fields.1, fields.2] using
    accepted_associated_data crypto verify writer kdf pin packet before after events authenticated supported server

end BeaconcryptCore.Computational.RegistrationRecordBinding

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.registration_associated_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.registration_associated_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.finish_native

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.accepted_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.accepted_associated_data

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.accepted_selected_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.accepted_selected_associated_data
