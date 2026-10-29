-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemGame
import BeaconcryptCore.Computational.RegistrationCredentialBridge

/-! A native authenticated KEM getter is tied to the original signed PQ field. The birth theorem uses the actual indexed source creation support, retaining its private handle rather than identifying owners by public-key equality. These are local receipts for an unchanged published packet; a changed accepted packet still requires the separate authentication-origin argument. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativeKemTarget

open PqxdhKemIndCca
open PqxdhEd25519EufCma (pqMessage parsePqMessage)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
open BeaconcryptCore.Refinement.RegistrationCredentialMetadata (Credential)
variable {κ ι KemSK Auxiliary Result : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationAuthenticationExecutor.begin
  RegistrationCredentialBridge.parsedPacket

/-- The native attached field contains its tag and the exact generated public bytes after the signature. -/
def PacketKey (packet : registration.InitPacket) (key : MlKem768PublicKey) : Prop :=
  (absBytes packet.pq_key).drop 64 = pqMessage key

private theorem parsed_pq (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex)
    (parsed : RegistrationCredentialBridge.parsedPacket packet =
      some (PqxdhHeadlineBridges.typedVerified verified)) :
    parsePqMessage ((absBytes packet.pq_key).drop 64) =
      some (RegistrationRootInput.pqKey verified.beacon_pq_public_key) := by
  simp only [RegistrationCredentialBridge.parsedPacket, PqxdhHeadlineBridges.parsedBytes,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at parsed
  obtain ⟨identity, _, prekey, _, oneTime, _, pq, pqParsed, result⟩ := parsed
  have same := congrArg (fun value => value.2.pqKey) result
  simpa only [PqxdhHeadlineBridges.typedVerified, RegistrationRootInput.pqKey] using
    pqParsed.trans (congrArg some same)

/-- The actual native credential validator recovers precisely the original attached PQ payload. -/
theorem credential_key (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex)
    (key : MlKem768PublicKey) (credential : Credential packet verified)
    (original : PacketKey packet key) :
    RegistrationRootInput.pqKey verified.beacon_pq_public_key = key := by
  have parsed := parsed_pq packet verified (RegistrationCredentialBridge.credential_parsed packet verified credential)
  rw [original, PqxdhEd25519EufCma.parsePqMessage_pqMessage] at parsed
  exact (Option.some.inj parsed).symm

/-- Successful actual authentication preserves a published packet's generated PQ key through every ML, Ed and fingerprint callback. -/
theorem authenticated_key {State : Type}
    (implementation : QueryImpl RegistrationAuthenticationExecutor.Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (before after : State)
    (key : MlKem768PublicKey) (original : PacketKey packet key)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((simulateQ implementation (RegistrationAuthenticationExecutor.begin pin packet)).run before)) :
    RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key = key := by
  have parsed := parsed_pq packet accepted.registration
    (RegistrationCredentialBridge.interpreted_accepted_parsed implementation pin packet events accepted before after supported)
  rw [original, PqxdhEd25519EufCma.parsePqMessage_pqMessage] at parsed
  exact (Option.some.inj parsed).symm

/-- The already authenticated root collector calls the literal native getter, including its original optional shape. -/
theorem root_getter (accepted : registration.AuthenticatedInit) :
    RegistrationAgreementRoot.callbacks
      (.encapsulate (RegistrationRootInput.keys accepted.registration).pqKey) =
      RegistrationAgreementRoot.option <$>
        (RegistrationAgreementExecutor.Spec.query
          (.encapsulate (.Some accepted.registration.beacon_pq_public_key)) :
          OracleComp RegistrationAgreementExecutor.Spec _) := by
  change RegistrationAgreementRoot.option <$>
      (RegistrationAgreementExecutor.Spec.query
        (.encapsulate (.Some (RegistrationAgreementRoot.pqArray
          (RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key)))) :
        OracleComp RegistrationAgreementExecutor.Spec _) = _
  have key : RegistrationAgreementRoot.pqArray
      (RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key) =
      accepted.registration.beacon_pq_public_key :=
    RegistrationRootInput.pq_roundtrip accepted.registration.beacon_pq_public_key
  rw [key]

/-- The actual backend exposes exactly the authenticated key when its real native key check permits encapsulation; refusal has no hidden source call. -/
theorem lowered_getter (checks : PqxdhServerAuthExperiment.Checks)
    (accepted : registration.AuthenticatedInit) (key : MlKem768PublicKey)
    (selected : RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key = key) :
    RegistrationNativeKemInterface.server (KemSK := KemSK) checks
      (.encapsulate (.Some accepted.registration.beacon_pq_public_key)) =
      if checks.kemKey key then RegistrationNativeKemInterface.encapsulate key else pure .None := by
  simp only [RegistrationNativeKemInterface.server, selected]

/-- The selected literal native getter suspends before the KEM ciphertext and shared-secret reply; its exact native conversion remains in the saved continuation. -/
theorem getter_cut {m : Type → Type} [Monad m]
    (implementation : QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) m)
    (checks : PqxdhServerAuthExperiment.Checks) (accepted : registration.AuthenticatedInit)
    (key : MlKem768PublicKey)
    (selected : RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key = key)
    (valid : checks.kemKey key = true)
    (next : core.option.Option (Std.Array U8 1088#usize × Std.Array U8 32#usize) →
      OracleComp (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) Result) :
    RegistrationNativeKemCut.scan implementation
      (RegistrationNativeKemInterface.server checks
        (.encapsulate (.Some accepted.registration.beacon_pq_public_key)) >>= next) 0 =
      pure (.pending key (fun answer => next (.Some
        (PqxdhAcceptedRegistration.ciphertextArray answer.1,
          PqxdhRootTableInitialization.rootArray answer.2)))) := by
  rw [lowered_getter checks accepted key selected, valid]
  simp only [ite_true]
  have moved : (RegistrationNativeKemInterface.encapsulate (KemSK := KemSK) key >>= next) =
      (((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).query
        (.inr (.inr key)) : OracleComp
          (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) _) >>= fun answer => next (.Some
          (PqxdhAcceptedRegistration.ciphertextArray answer.1,
            PqxdhRootTableInitialization.rootArray answer.2))) := by
    unfold RegistrationNativeKemInterface.encapsulate
    exact _root_.bind_map_left
      (m := OracleComp (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK))
      (fun (answer : MlKem768Ciphertext × MlKemSharedSecret) => .Some (PqxdhAcceptedRegistration.ciphertextArray answer.1,
        PqxdhRootTableInitialization.rootArray answer.2))
      ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).query
        (.inr (.inr key))) next
  rw [moved]
  exact RegistrationNativeKemCut.scan_target implementation key _

/-- An actual successful source birth and authentication of its unchanged attached field yield a genuine generated target and the exact retained private creation index. -/
theorem born_authenticated (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (ambient : OracleSpec κ)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (born : (Nat × MlKem768PublicKey) × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK))
    (birth : born ∈ support ((RegistrationNativeKemInterface.source baseImpl kem ambient other
      (.inr (.inl .create))).run before))
    {State : Type}
    (authentication : QueryImpl RegistrationAuthenticationExecutor.Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (pre post : State)
    (original : PacketKey packet born.1.2)
    (authenticated : (.ok (events, .Accepted accepted), post) ∈ support
      ((simulateQ authentication (RegistrationAuthenticationExecutor.begin pin packet)).run pre)) :
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen),
      born.1.1 = before.2.keys.length ∧ born.1.2 = pair.1 ∧
      born.2.2.keys = before.2.keys ++ [pair] ∧
      RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key = pair.1 := by
  obtain ⟨pair, generated, returned, retained⟩ :=
    RegistrationNativeKemInterface.create_generated baseImpl kem ambient other before born birth
  have getter := authenticated_key authentication pin packet events accepted pre post born.1.2 original authenticated
  exact ⟨pair, generated, congrArg Prod.fst returned, congrArg Prod.snd returned,
    retained, getter.trans (congrArg Prod.snd returned)⟩

end BeaconcryptCore.Computational.RegistrationNativeKemTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.getter_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.getter_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.credential_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.credential_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.authenticated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.authenticated_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.root_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.root_getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.lowered_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.lowered_getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTarget.born_authenticated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTarget.born_authenticated
