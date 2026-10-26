import BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! Recover the ordered identity fields from the literal extracted associated-data layout and actual candidate/record receipts. No cryptographic output or arbitrary codec injectivity is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
variable {Reader Response : Type}

/-- The actual extracted array output has the already verified ordered tagged-identity layout. -/
theorem source_bytes (server beacon : Std.Array Std.U8 32#usize)
    (ad : Std.Array Std.U8 281#usize)
    (built : pqxdh.build_associated_data server beacon = ok ad) :
    absBytes ad = Pqxdh.assocData (absBytes server) (absBytes beacon) := by
  obtain ⟨actual, generated, bytes⟩ := build_associated_data_abs server beacon
  exact RustM.ok.inj (generated.symm.trans built) ▸ bytes

/-- Equality of two literal associated-data outputs recovers both ordered raw identity arrays. This is a concrete fixed-layout fact, not a cryptographic or codec contract. -/
theorem source_identities (server beacon otherServer otherBeacon : Std.Array Std.U8 32#usize)
    (ad otherAd : Std.Array Std.U8 281#usize)
    (built : pqxdh.build_associated_data server beacon = ok ad)
    (otherBuilt : pqxdh.build_associated_data otherServer otherBeacon = ok otherAd)
    (same : absBytes ad = absBytes otherAd) : server = otherServer ∧ beacon = otherBeacon := by
  have identities := Pqxdh.assocData_inj (by simp : (absBytes server).length = 32)
    (by simp : (absBytes beacon).length = 32) (by simp : (absBytes otherServer).length = 32)
    (by simp : (absBytes otherBeacon).length = 32)
    ((source_bytes server beacon ad built).symm.trans (same.trans (source_bytes otherServer otherBeacon otherAd otherBuilt)))
  exact ⟨Subtype.ext ((absBytes_inj_iff _ _).mp identities.1), Subtype.ext ((absBytes_inj_iff _ _).mp identities.2)⟩

/-- Actual successful Server preparation builds associated data from the current Server identity and the supplied pending registration's Beacon identity. -/
theorem prepared_bytes (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending binding availability = ok (.Ok candidate)) :
    absBytes candidate.associated_data =
      Pqxdh.assocData (absBytes binding.identity_public_key) (absBytes pending.beacon_identity_public_key) :=
  source_bytes binding.identity_public_key pending.beacon_identity_public_key candidate.associated_data
    (PqxdhServerAuthNegativeControl.prepare_commit_fields state pending binding availability candidate prepared).2.2.2.2.2

/-- The actual Beacon control uses the same ordered source layout. -/
theorem beacon_bytes (control : pqxdh.BeaconInitSent) :
    absBytes (PqxdhBeaconPhase2Shared.associatedData control) =
      Pqxdh.assocData (absBytes control.expected_server_binding.identity_public_key)
        (absBytes control.beacon_identity_public_key) :=
  source_bytes control.expected_server_binding.identity_public_key control.beacon_identity_public_key
    (PqxdhBeaconPhase2Shared.associatedData control)
    (BeaconcryptCore.PanicFreedom.build_associated_data_ok _ _).choose_spec

/-- Matching the actual Server candidate's associated data to an actual Beacon control recovers both raw identities, without a root or KEM output inference. -/
theorem prepared_identities (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending binding availability = ok (.Ok candidate))
    (control : pqxdh.BeaconInitSent)
    (same : absBytes candidate.associated_data = absBytes (PqxdhBeaconPhase2Shared.associatedData control)) :
    binding.identity_public_key = control.expected_server_binding.identity_public_key ∧
      pending.beacon_identity_public_key = control.beacon_identity_public_key :=
  source_identities binding.identity_public_key pending.beacon_identity_public_key
    control.expected_server_binding.identity_public_key control.beacon_identity_public_key
    candidate.associated_data (PqxdhBeaconPhase2Shared.associatedData control)
    (PqxdhServerAuthNegativeControl.prepare_commit_fields state pending binding availability candidate prepared).2.2.2.2.2
    (BeaconcryptCore.PanicFreedom.build_associated_data_ok _ _).choose_spec same

/-- The actual successful builder receipt's selected AD binds its supplied pending Beacon identity and pre-build Server identity to the Beacon control's ordered pair. The AD match remains explicit for the later accepted-frame consumer. -/
theorem receipt_identities (codec : Codec Reader Response) (pending : pqxdh.PendingServerRegistration)
    (payload : Option Pqxdh.Bytes) (state : ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (receipt : PqxdhServerAuthPublicationBuiltRecord.At codec pending payload state response entry)
    (control : pqxdh.BeaconInitSent)
    (same : entry.input.context.ad.bytes = absBytes (PqxdhBeaconPhase2Shared.associatedData control)) :
    state.server.identity = control.expected_server_binding.identity_public_key ∧
      pending.beacon_identity_public_key = control.beacon_identity_public_key := by
  obtain ⟨key, candidate, binding, sealed, encrypted, nonce, width, _, prepared, _, contextSame,
    _, _, _, input, _⟩ := receipt
  exact prepared_identities state.control pending ⟨state.server.identity, state.identityKeyId⟩ _ candidate prepared control
    ((congrArg (fun context : RawCtxSourceSend.SealContext => context.associatedData) contextSame).symm.trans
      ((congrArg (fun input : CtxRomAuth.CtxSealInput => input.context.ad.bytes) input).symm.trans same))

/-- An actual admitted Beacon metadata value and its reached matching raw target discharge the receipt's AD equality. This recovers only the ordered identities; signed bundle and full-session attribution remain separate. -/
theorem matched_identities (codec : Codec Reader Response) (pending : pqxdh.PendingServerRegistration)
    (payload : Option Pqxdh.Bytes) (state : ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (receipt : PqxdhServerAuthPublicationBuiltRecord.At codec pending payload state response entry)
    (control : pqxdh.BeaconInitSent) (prepared : PqxdhPhase2DhMetadata.Prepared Response)
    (admitted : PqxdhPhase2DhMetadata.admitted control prepared.collected = some prepared.metadata)
    (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget codec.frameRead raw
      (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhPhase2DhRootConsumer.cleared prepared).candidate) opened target)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    state.server.identity = control.expected_server_binding.identity_public_key ∧
      pending.beacon_identity_public_key = control.beacon_identity_public_key := by
  have contextEq := (PqxdhPhase2LocalMatching.localTarget_context codec.frameRead raw _ opened target delivery).1
  have inputAD : entry.input.context.ad.bytes = absBytes prepared.metadata.associatedData :=
    congrArg Pqxdh.RecordAD.bytes (same.2.1.symm.trans contextEq)
  exact receipt_identities codec pending payload state response entry receipt control
    (inputAD.trans (congrArg (fun metadata : PqxdhBeaconPhase2Shared.Metadata => absBytes metadata.associatedData)
      (PqxdhPhase2DhMetadata.admitted_fields control prepared.collected prepared.metadata admitted).2.2))

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.source_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.source_bytes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.source_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.source_identities
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.prepared_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.prepared_bytes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.beacon_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.beacon_bytes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.prepared_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.prepared_identities
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.receipt_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.receipt_identities
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.matched_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity.matched_identities
