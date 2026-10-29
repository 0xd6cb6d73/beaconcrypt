-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerRootPreparation
import BeaconcryptCore.Computational.PqxdhPhase2InputBytes
import BeaconcryptCore.Computational.PqxdhServerStaticDhSource
import BeaconcryptCore.Computational.RegistrationEd25519Receipts
import BeaconcryptCore.Refinement.KeyAgreement

/-! Native verified KEX fields have an exact fixed-width presentation in the existing related-root interface. The post-authentication collector keeps the native registration binding outside the root-family request and starts at the already verified capability. Its correspondence with the native agreement executor is a separate operational theorem. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte)

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationRootInput

open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple Ed25519PublicKey)
open PqxdhServerRootPreparation (Verified Inputs)
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhServerStaticDhSource (PublicDomain nativeImpl prefixImpl concreteInputs References)

def pqKey (value : Std.Array Std.U8 1184#usize) : PqxdhKemIndCca.MlKem768PublicKey :=
  ⟨absBytes value, by simp⟩

def identity (registration : pqxdh.VerifiedInitKex) : Ed25519PublicKey :=
  PqxdhPhase2InputBytes.word registration.beacon_identity_public_key

def keys (registration : pqxdh.VerifiedInitKex) : Phase1KeyTuple :=
  ⟨PqxdhPhase2InputBytes.word registration.beacon_prekey_public_key,
    PqxdhPhase2InputBytes.word registration.beacon_one_time_public_key,
    pqKey registration.beacon_pq_public_key⟩

theorem pq_roundtrip (value : Std.Array Std.U8 1184#usize) :
    (⟨(pqKey value).toList.map concreteByte, by simp⟩ : Std.Array Std.U8 1184#usize) = value := by
  apply Subtype.ext
  apply (absBytes_inj_iff _ _).mp
  simp [pqKey, absBytes, List.map_map, Function.comp_def]

/-- Every projected classical coordinate is the actual native verified coordinate. -/
theorem verified_roundtrip (registration : pqxdh.VerifiedInitKex) :
    PqxdhProtocolAcceptance.verified (identity registration) (keys registration) = registration := by
  cases registration with
  | mk identityKey prekey oneTime pq =>
      simp only [identity, keys, PqxdhProtocolAcceptance.verified,
        PqxdhPhase2InputBytes.word_roundtrip, pq_roundtrip]

def candidate (packet : registration.InitPacket) :
    Phase1Candidate :=
  ⟨absBytes packet.identity_key, absBytes packet.pre_key,
    absBytes packet.one_time_key, absBytes packet.pq_key⟩

def verified (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Verified registration.InitPacket :=
  ⟨packet, candidate packet,
    identity authenticated.registration, keys authenticated.registration⟩

theorem verified_native (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    PqxdhProtocolAcceptance.verified (verified packet authenticated).identity
      (verified packet authenticated).keys = authenticated.registration := by
  exact verified_roundtrip authenticated.registration

/-- The binding is retained as public auxiliary metadata, outside the hidden root coordinate. -/
def collectAuthenticated {Ephemeral Shared : Type} (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    OracleComp (PqxdhServerRootPreparation.Spec registration.InitPacket Ephemeral Shared)
      (Option (session.RegistrationBinding × Inputs registration.InitPacket Ephemeral Shared)) :=
  (fun result => result.map fun input => (authenticated.binding, input)) <$>
    PqxdhServerRootPreparation.collectVerified (verified packet authenticated)

theorem collected_verified {Reader Ephemeral Shared : Type} (original : Verified Reader)
    (input : Inputs Reader Ephemeral Shared)
    (supported : some input ∈ support (PqxdhServerRootPreparation.collectVerified original)) :
    input.verified = original := by
  simp only [PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left, mem_support_bind_iff] at supported
  repeat' first
    | (simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
        OptionT.run_failure, Option.elimM, bind_map_left, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, Option.elim_none, Option.elim_some,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
        Option.some.injEq, Option.some_ne_none] at supported)
    | (obtain ⟨reply, _, supported⟩ := supported; cases reply)
  all_goals simp_all

/-- Hiding the selected static DH retains the native binding and every post-authentication effect. -/
theorem collect_realization (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    {Ephemeral : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Ephemeral Unit) m)
    (visit : PqxdhBeaconPhase2Preparation.Word32 → m Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    simulateQ (nativeImpl joint seed aux visit)
        (collectAuthenticated (Shared := PqxdhBeaconPhase2Preparation.Word32) packet authenticated) =
      Option.map (fun value => (value.1, concreteInputs joint seed value.2)) <$>
        simulateQ (prefixImpl domain aux visit)
          (collectAuthenticated (Shared := PeerEncoding) packet authenticated) := by
  simp only [collectAuthenticated, simulateQ_map,
    PqxdhServerStaticDhSource.collectVerified_realization joint domain seed aux visit,
    Functor.map_map]
  congr 1
  funext value
  cases value <;> rfl

/-- The root address and native credential are derived from the actual post-authentication collector. -/
theorem collect_provenance {joint : Primitives} (domain : PublicDomain joint)
    {Ephemeral Auxiliary : Type}
    (aux : QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Ephemeral Unit)
      (StateT Auxiliary ProbComp))
    (visit : PqxdhBeaconPhase2Preparation.Word32 → StateT Auxiliary ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : Auxiliary) (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Ephemeral PeerEncoding)
    (supported : (some (binding, input), after) ∈ support
      ((simulateQ (prefixImpl domain aux visit) (collectAuthenticated packet authenticated)).run before)) :
    binding = authenticated.binding ∧ input.verified = verified packet authenticated ∧
      References domain input := by
  rw [collectAuthenticated, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨result, state⟩, reached, equal⟩ := supported
  cases result with
  | none => simp at equal
  | some found =>
      have pairEq : (authenticated.binding, found) = (binding, input) :=
        Option.some.inj (congrArg Prod.fst equal)
      have bindingEq : binding = authenticated.binding := (congrArg Prod.fst pairEq).symm
      have inputEq : found = input := congrArg Prod.snd pairEq
      have openMember : some found ∈ support
          (PqxdhServerRootPreparation.collectVerified (verified packet authenticated)) := by
        apply OracleComp.support_simulateQ_run'_subset (prefixImpl domain aux visit) _ before
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst reached
      have credential := collected_verified (verified packet authenticated) found openMember
      have reference := PqxdhServerStaticDhSource.collectVerified_references domain aux visit
        (verified packet authenticated) before state found reached
      exact ⟨bindingEq, inputEq ▸ credential, inputEq ▸ reference⟩

attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

/-- The original signed packet, rather than a reconstructed credential, justifies the related-root acceptance premise. -/
theorem accepted_source {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationAuthenticationShared.begin crypto verify writer kdf pin packet).run before)) :
    PqxdhJointPhase1Reports.sourceAccept (fun publicKey bytes => crypto.verify publicKey.toList bytes)
      (candidate packet) = some ((verified packet authenticated).identity, (verified packet authenticated).keys) := by
  exact RegistrationEd25519Receipts.accepted_source crypto verify writer kdf pin packet before after
    events authenticated supported

end BeaconcryptCore.Computational.RegistrationRootInput

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.pq_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.pq_roundtrip

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.verified_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.verified_roundtrip

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.verified_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.verified_native

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.collected_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.collected_verified

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.collect_realization

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.collect_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.collect_provenance

/-- info: 'BeaconcryptCore.Computational.RegistrationRootInput.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootInput.accepted_source
