-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentInterface
import BeaconcryptCore.Computational.RawCtxMixedShared

/-! Native semantics of the common deployment experiment (CE-2, the subset used by the CE-3 trial). Registration commands, the public HMAC and BLAKE2b oracles are the source14 handler on the one live native Server and its dynamically created owners; `create` first applies the public 32-byte pin parse and does not re-run runtime initialization (deviation D1). Record commands run `RawCtxServerMixed.serverImpl` and `RawCtxBeaconLifecycle.beaconImpl` on the live Server peer map and the live owners, with real HKDF and AEAD, the codec frame reader and writer, and the shared BLAKE2b cache; their raw-attempt ghost counters are kept beside the native state. The game constructs the Server from a generated seed only. No reveal, public getter, snapshot or secrecy command exists. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentNative
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Spec Command parsePin)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The live native registration state with every owner and the shared Server, plus the Server and per-owner raw-attempt ghost counters. -/
structure State (KemSK : Type) where
  native : PqxdhRegistrationSchedule.State KemSK
  serverRaw : Nat
  ownerRaw : Nat → Nat

/-- A registration scheduler step leaves both raw-attempt counters untouched. -/
def onNative {Result : Type} (work : PqxdhRegistrationSchedule.Game KemSK Result) :
    StateT (State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, { state with native := result.2 })) <$> work state.native

/-- Record primitives: real ratchet HKDF and AEAD, the codec frame writer, and the shared BLAKE2b cache. -/
noncomputable def primitives (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp) :=
  RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)

/-- A record program runs on the shared BLAKE2b cache of the native state and touches nothing else. -/
noncomputable def record {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) : PqxdhRegistrationSchedule.Game KemSK Result :=
  PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeCtx (simulateQ (primitives setup codec) work))

/-- The live Server peer map with its raw-attempt counter. -/
def serverView (state : State KemSK) : RawCtxServerRouting.State Unit Unit :=
  ⟨state.native.shared.2.server.server, state.serverRaw⟩

/-- Reinstall a Server peer map and its counter; control, consumed IDs, tokens and all other fields are kept. -/
def withServer (state : State KemSK) (server : RawCtxServerRouting.State Unit Unit) : State KemSK :=
  { state with
    native := { state.native with shared := (state.native.shared.1, { state.native.shared.2 with
      server := { state.native.shared.2.server with server := server.server } }) }
    serverRaw := server.rawAttempts }

/-- `Server::encrypt_message` sends under the Server's own identity key ID. -/
def senderId (state : State KemSK) : Unit → Std.U64 := fun _ => state.native.shared.2.server.identityKeyId

/-- Server record commands: `encrypt_message` and `decrypt_message` on the live peer map, routed by the header router `route` and decoded by the codec frame reader. -/
noncomputable def serverStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    StateT (State KemSK) ProbComp (RawCtxServerMixed.SourceSpec.Range query) := fun state => do
  let result ← (record setup codec ((RawCtxServerMixed.serverImpl (senderId state) route codec.frameRead query).run
    (serverView state))).run state.native
  pure (result.1.1, withServer { state with native := result.2 } result.1.2)

/-- An owner handle that was never created has no Beacon object; the command is rejected without any effect. -/
def absent (query : RawCtxMixedOwner.SourceSpec.Domain) : RawCtxMixedOwner.SourceSpec.Range query :=
  match query with
  | .inl _ => none
  | .inr _ => .None

/-- Beacon record commands: `encrypt_message` and `decrypt_message` on the live owner; only its returned Beacon is reinstalled and its counter kept in the ghost map. -/
noncomputable def beaconStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT (State KemSK) ProbComp (RawCtxMixedOwner.SourceSpec.Range query) := fun state =>
  match state.native.owners[index]? with
  | none => pure (absent query, state)
  | some owner => do
      let result ← (record setup codec ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
        ⟨owner.beacon, state.ownerRaw index⟩)).run state.native
      pure (result.1.1, { state with
        native := { result.2 with owners := result.2.owners.set index { owner with beacon := result.1.2.beacon } }
        ownerRaw := Function.update state.ownerRaw index result.1.2.rawAttempts })

/-- The native handler. Registration, HMAC and BLAKE2b are the source14 handler; `create` parses the pin first; records act on the live Server and owners. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT (State KemSK) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.create pin keyId) =>
      match parsePin pin with
      | none => pure none
      | some word => some <$> onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.create word keyId)))
  | .inr (.bundle owner) => onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle owner)))
  | .inr (.accept raw) => onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.accept raw)))
  | .inr (.build session payload) =>
      onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.build session payload)))
  | .inr (.finish owner raw) => onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.finish owner raw)))
  | .inr (.hmac key message) => onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.hmac key message)))
  | .inr (.hash bytes) => onNative (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => serverStep setup codec route (.inl (plaintext, keyId))
  | .inr (.serverRaw raw) => serverStep setup codec route (.inr raw)
  | .inr (.beaconSend owner plaintext) => beaconStep setup codec owner (.inl plaintext)
  | .inr (.beaconRaw owner raw) => beaconStep setup codec owner (.inr raw)

/-- The experiment starts from the constructed Server with no owners and zero counters. -/
def initial (created : PqxdhLiveServerConstruction.Created Unit) : State KemSK :=
  ⟨PqxdhRegistrationSchedule.initial created, 0, fun _ => 0⟩

/-- The common experiment: the actual Server constructor with a generated seed (never a supplied one), then the adversary against the native handler. A constructor failure ends the run with no outcome. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (adversary : OracleComp Spec X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × State KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (handler setup codec checks route created.seed) adversary).run (initial created)

/-- A record program changes only the BLAKE2b cache of the native state. -/
theorem record_run {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRegistrationSchedule.State KemSK) :
    (record setup codec work).run state =
      (fun result => (result.1, { state with shared := (state.shared.1, { state.shared.2 with ctx := result.2.2 }) })) <$>
        (simulateQ (primitives setup codec) work).run ((), state.shared.2.ctx) := by
  simp only [record, PqxdhRegistrationSchedule.onShared_run, PqxdhServerAuthNative.nativeCtx, Functor.map_map]

/-- Every supported record result keeps the whole native state except the BLAKE2b cache. -/
theorem record_support {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRegistrationSchedule.State KemSK)
    (result : Result × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((record setup codec work).run state)) :
    ∃ cache, result.2 = { state with shared := (state.shared.1, { state.shared.2 with ctx := cache }) } := by
  rw [record_run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact ⟨inner.2.2, rfl⟩

/-- A wrong-width pin is rejected with no draw and no state change. -/
theorem create_width (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (width : pin.length ≠ 32) (state : State KemSK) :
    (handler setup codec checks route serverSeed (.inr (.create pin keyId))).run state = pure (none, state) := by
  have parsed : parsePin pin = none := by
    simp only [parsePin, toWord32, width, _root_.dite_false]
  simp only [handler, parsed, StateT.run_pure]

/-- A Server record command changes only the Server peer map, its counter and the BLAKE2b cache: the Extract family, owners, pending tokens, session counter, control, consumed IDs, the Server key ID and the owners' counters are untouched. -/
theorem serverStep_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) (state : State KemSK)
    (result : RawCtxServerMixed.SourceSpec.Range query × State KemSK)
    (supported : result ∈ support ((serverStep setup codec route query).run state)) :
    result.2.native.owners = state.native.owners ∧ result.2.ownerRaw = state.ownerRaw ∧
      result.2.native.shared.1 = state.native.shared.1 ∧
      result.2.native.shared.2.pending = state.native.shared.2.pending ∧
      result.2.native.shared.2.sessions = state.native.shared.2.sessions ∧
      result.2.native.shared.2.ghost = state.native.shared.2.ghost ∧
      result.2.native.shared.2.server.control = state.native.shared.2.server.control ∧
      result.2.native.shared.2.server.consumed = state.native.shared.2.server.consumed ∧
      result.2.native.shared.2.server.identityKeyId = state.native.shared.2.server.identityKeyId := by
  simp only [serverStep, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  obtain ⟨cache, same⟩ := record_support setup codec _ state.native inner member
  simp only [withServer, same, and_self]

/-- A Beacon record command changes only the addressed owner's Beacon, its counter and the BLAKE2b cache; the Server, the Extract family, pending tokens and every other owner are untouched. -/
theorem beaconStep_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State KemSK)
    (supported : result ∈ support ((beaconStep setup codec index query).run state)) :
    result.2.serverRaw = state.serverRaw ∧ result.2.native.shared.1 = state.native.shared.1 ∧
      result.2.native.shared.2.server = state.native.shared.2.server ∧
      result.2.native.shared.2.pending = state.native.shared.2.pending ∧
      result.2.native.shared.2.sessions = state.native.shared.2.sessions ∧
      result.2.native.shared.2.ghost = state.native.shared.2.ghost ∧
      result.2.native.owners.length = state.native.owners.length ∧
      (∀ other, other ≠ index → result.2.native.owners[other]? = state.native.owners[other]? ∧
        result.2.ownerRaw other = state.ownerRaw other) := by
  unfold beaconStep at supported
  cases found : state.native.owners[index]? with
  | none =>
      simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | some owner =>
      simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      obtain ⟨cache, same⟩ := record_support setup codec _ state.native inner member
      refine ⟨rfl, by simp only [same], by simp only [same], by simp only [same], by simp only [same],
        by simp only [same], by simp only [same, List.length_set], fun other different => ⟨?_, ?_⟩⟩
      · simp only [same, List.getElem?_set_ne (Ne.symm different)]
      · exact Function.update_of_ne different _ _

end BeaconcryptCore.Computational.PqxdhDeploymentNative

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentNative.record_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentNative.record_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentNative.record_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentNative.record_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentNative.create_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentNative.create_width

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentNative.serverStep_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentNative.serverStep_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentNative.beaconStep_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentNative.beaconStep_fields
