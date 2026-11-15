-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins

/-! Public Phase1 fields and actual attached-Ed/parser/token receipts, independent of any associated-data identity inverse. The declaration names and terms remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhServerAuthPhase1Origins PqxdhServerAuthPhase1Receipt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The three public unsigned Phase1 fields, with no identity seed argument. -/
def material (prekey oneTime : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) :
    Phase1Material Unit := ⟨prekey, oneTime, pqKey, ()⟩

/-- The literal context's prekey, generated one-time public key and ML-KEM public key. This projection does not read the target Beacon identity seed. -/
def contextMaterial (setup : Setup baseSpec KemSK) (context : PqxdhServerAuthEntryFactor.Context KemSK) :
    Phase1Material Unit :=
  material (context.publicValue setup).prekey (setup.dh.publicKey context.oneTime) context.keys.1

/-- Original attached verification returns the same identity parsed from the original candidate field. No signature adapter is needed for this source equation. -/
theorem accepted_identity (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept verify candidate = some (identity, keys)) :
    parseIdentity candidate.identityKey = some identity := by
  simp only [PqxdhJointPhase1Reports.sourceAccept, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at accepted
  obtain ⟨key, parsed, pq, _, pre, _, one, _, repeated, _, prekey, _, oneTime, _, pqKey, _, same⟩ := accepted
  have identityEq : key = identity := congrArg Prod.fst (Option.some.inj same)
  exact identityEq ▸ parsed

/-- The same actual pending receipt exposes the original reader/getters and parsed identity stored in the native token. -/
theorem token_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token) :
    ∃ verified : PqxdhServerRootPreparation.Verified Reader,
      Decoded codec raw verified ∧
      parseIdentity verified.candidate.identityKey = some verified.identity ∧
      token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray verified.identity ∧
      PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
        verified.candidate = some (verified.identity, verified.keys) := by
  obtain ⟨consumed, after, input, supported, pendingEq, decoded, accepted⟩ := receipt
  exact ⟨input.verified, decoded, accepted_identity _ _ _ _ accepted,
    congrArg beaconcrypt_core.pqxdh.PendingServerRegistration.beacon_identity_public_key pendingEq, accepted⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.accepted_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.accepted_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.token_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.token_identity
