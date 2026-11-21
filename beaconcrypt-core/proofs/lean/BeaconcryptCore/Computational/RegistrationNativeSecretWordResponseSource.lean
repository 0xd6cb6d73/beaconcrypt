-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource

/-! Actual Word frontend build support carries the same stored-session response metadata through the mutable environment and arbitrary combined outer interpreter. The source receipt keeps the original frontend table and current pin rather than substituting a real-SDK run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The actual public Word build exposes the original stored registration and pin. -/
theorem frontend (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativeSecretWordMessage.State source) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
        selectedOwner selectedAccept publicPrekey (.inr (.build handle application))).run before)) :
    ∃ ready, before.server.sessions[handle]? = some (some ready) ∧
      RegistrationNativeSecretWordResponse.EncodedFrom wire ready before.server.pin bytes := by
  simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
    StateT.run, support_map] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have original := RegistrationNativeResponsePaired.simulation_support
    (RegistrationNativeSecretWordInterface.liftLocal false) _ _ reached
  have material : result.1 ∈ support
      ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire checks.reservePeer handle application).run before.server) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeSecretWordServerCompiler.service setup.source wire sign)
      _ before.environment
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst original
  have success : result.1.1 = .ok (some (keyId, bytes)) := congrArg Prod.fst returned
  rcases result with ⟨⟨reply, server⟩, env⟩
  dsimp only at success
  subst reply
  exact RegistrationNativeSecretWordResponse.build wire checks.reservePeer handle application before.server server keyId bytes material

/-- Arbitrary combined protected-key replies preserve the same successful response provenance. -/
theorem typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativeSecretWordTargetSource.State n KemSK source) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        selectedOwner selectedAccept publicPrekey (.inr (.build handle application))).run before)) :
    ∃ ready, before.1.server.sessions[handle]? = some (some ready) ∧
      RegistrationNativeSecretWordResponse.EncodedFrom wire ready before.1.server.pin bytes := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have original : result.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
        selectedOwner selectedAccept publicPrekey (.inr (.build handle application))).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have success : result.1.1 = .ok (some (keyId, bytes)) := congrArg Prod.fst returned
  rcases result with ⟨⟨reply, front⟩, current⟩
  dsimp only at success
  subst reply
  exact frontend setup checks wire sign selectedOwner selectedAccept publicPrekey handle application before.1 front keyId bytes original

end BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource.frontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource.typed
