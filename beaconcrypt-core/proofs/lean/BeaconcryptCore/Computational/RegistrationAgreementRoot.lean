-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRootInput
import BeaconcryptCore.Computational.RegistrationAgreementShared
import BeaconcryptCore.Computational.RegistrationAgreementTermination
import BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer

/-! The native agreement controller factors through the already authenticated root prefix. Its eight actual primitive callbacks retain their order and optional exits. The root-family compiler replaces only the selected static-DH output; the authenticated registration binding is retained outside that private coordinate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationAgreementRoot

open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationAgreementExecutor

def option {Value : Type} : core.option.Option Value → Option Value
  | .None => none
  | .Some value => some value

def nativeOption {Value : Type} : Option Value → core.option.Option Value
  | none => .None
  | some value => .Some value

def pqArray (key : PqxdhKemIndCca.MlKem768PublicKey) : Array Std.U8 1184#usize :=
  ⟨key.toList.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte, by simp⟩

private theorem pq_array (key : Array Std.U8 1184#usize) : pqArray (RegistrationRootInput.pqKey key) = key :=
  RegistrationRootInput.pq_roundtrip key

/-- The unused parsing constructors are pure because the native controller starts with a typed authenticated capability. Every primitive callback is still the actual native request. -/
def callbacks : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Word32)
    (OracleComp Spec)
  | .decode _ => pure none
  | .identity packet => pure (some (absBytes packet.identity_key))
  | .pqField packet => pure (some (absBytes packet.pq_key))
  | .preField packet => pure (some (absBytes packet.pre_key))
  | .oneField packet => pure (some (absBytes packet.one_time_key))
  | .verify _ _ => pure none
  | .identityPoint _ | .reserveRegistration | .parseDh _ | .parseKem _ => pure true
  | .registrationStatus _ => pure .Fresh
  | .generate => (fun reply => (option reply).map fun key => (⟨(), key⟩ : Ephemeral Unit)) <$>
      Spec.query (.generate .ServerEphemeral)
  | .encapsulate key => option <$> Spec.query (.encapsulate (.Some (pqArray key)))
  | .publicConversion key => option <$> Spec.query (.convertPublic (PqxdhRootTableInitialization.rootArray key))
  | .privateConversion => Spec.query (.convertSecret .LocalIdentity)
  | .staticDh key => option <$> Spec.query (.dh ⟨.LocalIdentity, key⟩)
  | .ephemeralDh _ key => option <$> Spec.query (.dh ⟨.ServerEphemeral, key⟩)

def state (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (input : Inputs registration.InitPacket Unit Word32) : agreement.AgreementState :=
  ⟨.Server control .Fresh authenticated.registration authenticated.binding,
    input.convertedIdentity, input.ephemeral.publicKey, input.ciphertext,
    ⟨input.first⟩, ⟨input.second⟩, ⟨input.third⟩, ⟨input.fourth⟩, ⟨input.kem⟩⟩

def finish (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (input : Inputs registration.InitPacket Unit Word32) : OracleComp Spec (RustM agreement.AgreementEffect) :=
  continueWith (agreement.finish_dh (state control authenticated input)) (drive 1)

def normalized (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) : OracleComp Spec (RustM agreement.AgreementEffect) := do
  let input ← simulateQ callbacks
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match input with
  | none => pure (.ok (.Rejected .None))
  | some input => finish control authenticated input

private theorem drive_rejected (fuel : Nat) (aborted : core.option.Option pqxdh.BeaconAborted) :
    drive fuel (.Rejected aborted) = pure (.ok (.Rejected aborted)) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [drive, step, pure_bind, continueWith, ih]

attribute [local irreducible] agreement.finish_dh

/-- All successful and failed native primitive replies pass through the same ordered prefix; the root request is made only after the actual fourth-DH continuation. -/
theorem server_normalized (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    server control .Fresh authenticated = normalized control packet authenticated := by
  rw [server, (BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2]
  simp only [normalized, RegistrationRootInput.verified,
    PqxdhServerRootPreparation.collectVerified, OptionT.run_bind, OptionT.run_monadLift,
    OptionT.run_mk, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, callbacks, bind_pure_comp, bind_assoc, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false,
    Option.elim_some]
  simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok,
    continueWith, ]
  try dsimp only
  repeat' first
    | rfl
    | (simp only [step, continueWith, pure_bind, bind_assoc, bind_map_left,
        OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_map, Option.elimM, Option.elim_some, simulateQ_bind, simulateQ_map, simulateQ_spec_query, callbacks,
        Bool.not_true, Bool.false_eq_true, Functor.map_map, agreement.EphemeralPending.role, agreement.EphemeralPending.resume,
        agreement.EncapsulationPending.public_key, agreement.EncapsulationPending.resume,
        agreement.PublicConversionPending.public_key, agreement.PublicConversionPending.resume,
        agreement.SecretConversionPending.secret_role, agreement.SecretConversionPending.resume,
        agreement.DhPending.request, agreement.DhPending.resume,
        agreement.AgreementState.reject, pqxdh.VerifiedInitKex.impl.beacon_pq_public_key,
        pqxdh.VerifiedInitKex.impl.beacon_identity_public_key,
        pqxdh.VerifiedInitKex.impl.beacon_prekey_public_key,
        pqxdh.VerifiedInitKex.impl.beacon_one_time_public_key,
        ratchet.RatchetChain.from_bytes, bind_tc_ok, option, Option.elim_some, Option.map_some, finish, state,
        RegistrationRootInput.identity, RegistrationRootInput.keys,
        ↓reduceIte])
    | (dsimp! only)
    | (casesm* _ × _)
    | rw [pq_array]
    | rw [PqxdhPhase2InputBytes.word_roundtrip]
    | (congr 1; funext reply; cases reply)
    | rw [drive]

end BeaconcryptCore.Computational.RegistrationAgreementRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementRoot.server_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementRoot.server_normalized
