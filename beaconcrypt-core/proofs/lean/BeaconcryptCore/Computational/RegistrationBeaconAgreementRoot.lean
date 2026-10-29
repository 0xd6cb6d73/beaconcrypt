-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementRoot
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation
import BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer

/-! The actual authenticated Beacon response drives the existing ordered Phase2 prefix. Decoding and field extraction are typed projections of the retained authenticated packet; conversion, decapsulation and all four DH requests remain the actual native callbacks. The original pending registration binding remains outside the root coordinate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconAgreementRoot

open RegistrationAgreementExecutor
open RegistrationAgreementRoot (option)
open PqxdhBeaconPhase2Preparation (Word32)

abbrev PrefixSpec := PqxdhBeaconPhase2Preparation.Spec Unit Bool Unit Unit registration.AuthenticatedResponse

def callbacks (authenticated : registration.AuthenticatedResponse) : QueryImpl PrefixSpec (OracleComp Spec)
  | .decode _ => pure (some authenticated)
  | .ciphertext response => pure (some response.packet.public.kem_cipher_text)
  | .ephemeral response => pure (some response.packet.public.ephemeral_key)
  | .serverIdentity response => pure (some response.packet.public.identity_key)
  | .publicConversion key => option <$> Spec.query (.convertPublic key)
  | .privateConversion _ => (fun converted : Bool => if converted then some () else none) <$>
      Spec.query (.convertSecret .LocalIdentity)
  | .decapsulate ciphertext _ => option <$> Spec.query (.decapsulate (.Some ciphertext))
  | .dhPair oneTime key => option <$> Spec.query (.dh ⟨if oneTime then .BeaconOneTime else .BeaconPrekey, key⟩)
  | .dhIdentity _ key => option <$> Spec.query (.dh ⟨.LocalIdentity, key⟩)
  | .assignedId response => pure response.packet.public.key_id
  | .eraseShared _ => pure ()

def state (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) : agreement.AgreementState :=
  ⟨.Beacon authenticated.pending.control authenticated.pending.binding authenticated.packet.public authenticated.packet.application,
    Array.repeat 32#usize 0#u8, input.ephemeral, input.ciphertext,
    ⟨input.finishInputs.shared_secrets.dh1⟩, ⟨input.finishInputs.shared_secrets.dh2⟩,
    ⟨input.finishInputs.shared_secrets.dh3⟩, ⟨input.finishInputs.shared_secrets.dh4⟩,
    ⟨input.finishInputs.shared_secrets.kem_shared_secret⟩⟩

def finish (authenticated : registration.AuthenticatedResponse)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) :
    OracleComp Spec (RustM agreement.AgreementEffect) :=
  continueWith (agreement.finish_dh (state authenticated input)) (drive 2)

def rejected (authenticated : registration.AuthenticatedResponse) : agreement.AgreementEffect :=
  .Rejected (.Some ⟨authenticated.pending.control.expected_server_binding.identity_key_id⟩)

def normalized (authenticated : registration.AuthenticatedResponse) : OracleComp Spec (RustM agreement.AgreementEffect) := do
  let input ← simulateQ (callbacks authenticated) (PqxdhBeaconPhase2Preparation.collect () false true () [])
  match input with
  | none => pure (.ok (rejected authenticated))
  | some input => finish authenticated input

private theorem drive_rejected (fuel : Nat) (aborted : core.option.Option pqxdh.BeaconAborted) :
    drive fuel (.Rejected aborted) = pure (.ok (.Rejected aborted)) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [drive, step, pure_bind, continueWith, ih]

/-- The coherent retained native owner executes the same seven real primitive requests, every optional exit and final root admission. -/
theorem beacon_normalized (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding) :
    beacon authenticated = normalized authenticated := by
  rw [beacon, BeaconcryptCore.Refinement.KeyAgreement.beacon_entry_refines authenticated coherent]
  simp only [normalized, PqxdhBeaconPhase2Preparation.collect,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_pure,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query, callbacks, bind_assoc, pure_bind, Option.elim_some]
  simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok, continueWith]
  repeat' first
    | rfl
    | (simp only [step, continueWith, pure_bind, bind_assoc, bind_map_left,
        Option.elim_some, simulateQ_bind, simulateQ_spec_query, callbacks,
        agreement.PublicConversionPending.public_key, agreement.PublicConversionPending.resume,
        agreement.SecretConversionPending.secret_role, agreement.SecretConversionPending.resume,
        agreement.DecapsulationPending.ciphertext, agreement.DecapsulationPending.resume,
        agreement.DhPending.request, agreement.DhPending.resume,
        agreement.AgreementState.reject, pqxdh.beacon_abort_init,
        ratchet.RatchetChain.from_bytes, bind_tc_ok, option, finish, state, rejected, ↓reduceIte])
    | (dsimp! only)
    | (congr 1; funext reply; cases reply)
    | rw [drive]

end BeaconcryptCore.Computational.RegistrationBeaconAgreementRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconAgreementRoot.beacon_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconAgreementRoot.beacon_normalized
