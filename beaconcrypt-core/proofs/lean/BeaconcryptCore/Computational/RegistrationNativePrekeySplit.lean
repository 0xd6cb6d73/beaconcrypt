-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrekeyTargetTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginLedger

/-! The original real native APP event splits before any KDF, KEM or suffix-key game change. A changed peer prekey is charged to the existing real-source ordinary joint Ed-origin endpoint. The complementary public prekey equality remains a literal event conjunct; no Ed-origin statement is invoked in a modified game. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePrekeySplit
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget Handle)
open PqxdhEd25519EufCma (Ed25519PublicKey)
open RegistrationNativePrekeyEvents (Pinned GoodApp)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every original real peer designation either has the required public prekey equality or belongs to the original changed-prekey origin event. -/
theorem pinned_or_changed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (handle : Handle) :
    Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) created.server.server.metadata.sender result.2.1.ledger.transcript handle ∨
      RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons := by
  classical
  cases handle with
  | owner index => exact Or.inl trivial
  | peer keyId =>
      by_cases pinned : Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) created.server.server.metadata.sender result.2.1.ledger.transcript (.peer keyId)
      · exact Or.inl pinned
      · unfold Pinned at pinned
        push Not at pinned
        obtain ⟨session, index, designated, different⟩ := pinned
        obtain ⟨_response, raw, candidate, keys, _linked, accepted, candidateFound, keysFound, _valid, published⟩ :=
          PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
            created.server.server.metadata.sender keyId result.2.1.ledger.transcript session index designated
        obtain ⟨publishedPacket, publishedFound, _identity, _pq⟩ := published
        obtain ⟨publishedRaw, bundled, _parsed⟩ := Option.bind_eq_some_iff.mp publishedFound
        obtain ⟨owner, ownerAt, publicKey⟩ := RegistrationNativePrekeyTargetTrace.published_at setup checks wire route representation created credential
          readback bounds mode work before result supported index publishedRaw bundled
        have changed : keys.2.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic := by
          intro equal
          apply different
          simp only [RegistrationNativePrekeyEvents.acceptedAt, accepted, Option.bind_some, candidateFound, keysFound, Option.map_some, publicKey, equal]
        exact Or.inr (RegistrationNativeIdentityOriginLedger.peer_changed setup checks wire route representation created credential readback shortRejects
          bounds mode work before result supported keyId session index designated raw candidate keys.1 keys.2 accepted candidateFound keysFound owner ownerAt changed)

/-- Broad CEAPP success is charged once to the real origin event or retained with the public pin equality. -/
theorem ceapp_split (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (budget : Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto wire created.server.server.metadata.sender budget claim result) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons ∨
      GoodApp setup.source.crypto wire created.server.server.metadata.sender budget claim result := by
  obtain ⟨index, guess, entry, claimed, fresh, designated, guessed⟩ := winning
  rcases pinned_or_changed setup checks wire route representation created credential readback shortRejects bounds mode work before result supported entry.handle with pinned | changed
  · exact Or.inr ⟨index, guess, entry, claimed, fresh, designated, guessed, pinned⟩
  · exact Or.inl changed

end BeaconcryptCore.Computational.RegistrationNativePrekeySplit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeySplit.pinned_or_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeySplit.pinned_or_changed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeySplit.ceapp_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeySplit.ceapp_split
