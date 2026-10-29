-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityInterface
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend

/-! Actual native signing and converted-static-DH requests are lowered through the same generated identity handle. Public-key matching and native attached-buffer representability checks remain in the callback. The private source ownership receipt identifies the seed only inside the interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks
open PqxdhJointIdentity
open RegistrationNativeIdentityInterface
variable {Index Auxiliary : Type} {ambient : OracleSpec Index}

def Owns (primitives : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (credential : Credential) (seed : IdentitySeed) : Prop :=
  pool.seeds[credential.handle]? = some seed ∧ credential.publicIdentity = primitives.publicKeys seed

noncomputable def signing (ambient : OracleSpec Index) (credential : Credential)
    (request : registration.Ed25519SigningRequest) :
    OracleComp (Spec ambient) RegistrationSigningShared.SignReply := by
  classical
  exact if request.public_key = PqxdhRootTableInitialization.rootArray credential.publicIdentity.ed25519 then do
      let message := TranscriptAuthParts.absSlice request.message
      let signature ← RegistrationNativeIdentityInterface.sign ambient credential message
      pure (RegistrationAuthenticationShared.openedBytes
        (signature.map fun value => value.toList ++ message))
    else pure .None

noncomputable def signingReply (primitives : Primitives) (seed : IdentitySeed)
    (request : registration.Ed25519SigningRequest) : RegistrationSigningShared.SignReply := by
  classical
  exact if request.public_key = PqxdhRootTableInitialization.rootArray (primitives.publicKeys seed).ed25519 then
    RegistrationAuthenticationShared.openedBytes
      (some ((primitives.sign seed (TranscriptAuthParts.absSlice request.message)).toList ++
        TranscriptAuthParts.absSlice request.message)) else .None

def dh (ambient : OracleSpec Index) (credential : Credential)
    (peer : PqxdhBeaconPhase2Preparation.Word32) :
    OracleComp (Spec ambient) (core.option.Option PqxdhBeaconPhase2Preparation.Word32) := do
  let reply ← RegistrationNativeIdentityInterface.staticDh ambient credential (PqxdhPhase2GapDhSource.peer peer)
  pure (RegistrationAgreementRoot.nativeOption ((reply.join).map PqxdhRootTableInitialization.rootArray))

/-- Public signing callbacks return the source signature under the same generated seed and keep every unrelated state field. The source records the attempted handle service before returning. -/
theorem signing_source (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (credential : Credential) (seed : IdentitySeed)
    (request : registration.Ed25519SigningRequest) (before : State Auxiliary)
    (owned : Owns primitives before.2 credential seed) :
    Prod.map id Prod.fst <$>
      (simulateQ (source ambient ordinary primitives) (signing ambient credential request)).run before =
      pure (signingReply primitives seed request, before.1) := by
  classical
  obtain ⟨found, publicKey⟩ := owned
  by_cases matched : request.public_key = PqxdhRootTableInitialization.rootArray credential.publicIdentity.ed25519
  · simp only [signing, ite_eq_left matched, bind_pure_comp, RegistrationNativeIdentityInterface.sign,
      simulateQ_map, simulateQ_spec_query, StateT.run_map]
    rw [service_source]
    simp only [found, Option.map_some, primitiveReply, map_pure, Prod.map_def, id_eq]
    simp only [signingReply, ← publicKey, ite_eq_left matched]
  · simp only [signing, simulateQ_pure, StateT.run_pure, map_pure,
      Prod.map_def, id_eq, signingReply, ← publicKey, ite_eq_right matched]

/-- Optional static-DH replies use the very same generated seed and preserve native rejection, without returning its converted secret to the client. -/
theorem dh_source (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (credential : Credential) (seed : IdentitySeed)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (before : State Auxiliary)
    (owned : Owns primitives before.2 credential seed) :
    Prod.map id Prod.fst <$>
      (simulateQ (source ambient ordinary primitives) (dh ambient credential peer)).run before =
      pure (RegistrationAgreementRoot.nativeOption
        ((primitives.staticDh seed (PqxdhPhase2GapDhSource.peer peer)).map PqxdhRootTableInitialization.rootArray), before.1) := by
  simp only [dh, bind_pure_comp, RegistrationNativeIdentityInterface.staticDh, simulateQ_map,
    simulateQ_spec_query, StateT.run_map]
  rw [service_source]
  simp only [owned.1, Option.map_some, primitiveReply, map_pure, Prod.map_def, id_eq]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks.signing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks.signing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks.dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks.dh_source
