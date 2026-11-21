-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend

/-! The actual symbolic dispatcher consumes exactly one parsed-attempt ordinal before each typed accept. All Server continuations, owner controllers, records and failures retain the other counter coordinate. These are open AST support facts, so subsequent random material and concrete KEM interpretations cannot replace the routing ordinal with a session or private-key index. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual symbolic Server subprogram retains the separately stored parsed counter. -/
theorem server_counter (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

/-- Every actual symbolic owner subprogram retains the separately stored parsed counter. -/
theorem beacon_counter
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

/-- Actual send/raw records preserve the counter on present and absent public owner branches. -/
theorem record_counter (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  rcases query with server | ⟨owner, query⟩
  · simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl
  · cases query <;> cases found : before.beacons[owner]? with
    | none =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        rfl
    | some selected =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        rfl

def isAccept : RegistrationNativeRawAdapter.TypedSpec.Domain → Bool
  | .inr (.accept _) => true
  | _ => false

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept
  RegistrationNativeSecretWordServerCompiler.build
  RegistrationNativeSecretWordFrontend.serverOpen RegistrationNativeSecretWordFrontend.beacon
  RegistrationNativeSecretWordFrontend.record RegistrationNativeSecretWordFrontend.effect
  RegistrationNativeSecretWordOwners.create RegistrationNativeSecretWordOwners.bundle RegistrationNativeSecretWordOwners.finish

private theorem create_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.create edPin mlPin keyId) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.create edPin mlPin keyId))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.create edPin mlPin keyId))).toNat := by
  exact beacon_counter _ before result supported

private theorem bundle_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owner : Nat) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.bundle owner) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.bundle owner))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.bundle owner))).toNat := by
  exact beacon_counter _ before result supported

private theorem finish_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owner : Nat) (packet : Option registration.ResponsePacket) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.finish owner packet) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.finish owner packet))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.finish owner packet))).toNat := by
  exact beacon_counter _ before result supported

private theorem accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : State source) :
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.accept packet))).run before =
      (RegistrationNativeSecretWordFrontend.serverOpen (decide (before.parsedAccepts = selectedAccept))
        (RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet)).run
          { before with parsedAccepts := before.parsedAccepts + 1 } := by
  simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind,
    StateT.run_get, StateT.run_modify, pure_bind]

private theorem accept_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.accept packet) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.accept packet))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.accept packet))).toNat := by
  rw [accept_run] at supported
  exact server_counter _ _ _ result supported

private theorem build_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.build handle application) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.build handle application))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.build handle application))).toNat := by
  exact server_counter _ _ before result supported

private theorem hmac_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (key : PqxdhSecretInputKdf.HmacBlock) (bytes : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.hmac key bytes) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.hmac key bytes))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.hmac key bytes))).toNat := by
    simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl

private theorem hash_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (bytes : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.hash bytes) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.hash bytes))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.hash bytes))).toNat := by
    simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
      support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl

private theorem serverSend_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (keyId : U64) (plaintext : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.serverSend keyId plaintext) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.serverSend keyId plaintext))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.serverSend keyId plaintext))).toNat := by
  exact record_counter (.inl (.inl (plaintext, keyId))) before result supported

private theorem serverRaw_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (raw : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.serverRaw raw) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.serverRaw raw))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.serverRaw raw))).toNat := by
  exact record_counter (.inl (.inr raw)) before result supported

private theorem beaconSend_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owner : Nat) (plaintext : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.beaconSend owner plaintext) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.beaconSend owner plaintext))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.beaconSend owner plaintext))).toNat := by
  exact record_counter (.inr (owner, .inl plaintext)) before result supported

private theorem beaconRaw_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owner : Nat) (raw : Pqxdh.Bytes) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range (.beaconRaw owner raw) × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.beaconRaw owner raw))).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr (.beaconRaw owner raw))).toNat := by
  exact record_counter (.inr (owner, .inr raw)) before result supported

private theorem command_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.Command) (before : State source)
    (result : RegistrationNativeRawAdapter.CommandSpec.Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr query)).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept (.inr query)).toNat := by
  cases query with
  | create edPin mlPin keyId => exact create_counter setup checks wire sign selectedOwner selectedAccept publicPrekey edPin mlPin keyId before result supported
  | bundle owner => exact bundle_counter setup checks wire sign selectedOwner selectedAccept publicPrekey owner before result supported
  | finish owner packet => exact finish_counter setup checks wire sign selectedOwner selectedAccept publicPrekey owner packet before result supported
  | accept packet => exact accept_counter setup checks wire sign selectedOwner selectedAccept publicPrekey packet before result supported
  | build handle application => exact build_counter setup checks wire sign selectedOwner selectedAccept publicPrekey handle application before result supported
  | hmac key bytes => exact hmac_counter setup checks wire sign selectedOwner selectedAccept publicPrekey key bytes before result supported
  | hash bytes => exact hash_counter setup checks wire sign selectedOwner selectedAccept publicPrekey bytes before result supported
  | serverSend keyId plaintext => exact serverSend_counter setup checks wire sign selectedOwner selectedAccept publicPrekey keyId plaintext before result supported
  | serverRaw raw => exact serverRaw_counter setup checks wire sign selectedOwner selectedAccept publicPrekey raw before result supported
  | beaconSend owner plaintext => exact beaconSend_counter setup checks wire sign selectedOwner selectedAccept publicPrekey owner plaintext before result supported
  | beaconRaw owner raw => exact beaconRaw_counter setup checks wire sign selectedOwner selectedAccept publicPrekey owner raw before result supported

/-- Authentication rejection, replay and all failed accepted-call continuations consume that same actual preincrement ordinal. -/
theorem typed_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (isAccept query).toNat := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
        support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      rfl
  | inr command => exact command_counter setup checks wire sign selectedOwner selectedAccept publicPrekey command before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.server_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.server_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.beacon_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.beacon_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.record_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.record_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.typed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter.typed_counter
