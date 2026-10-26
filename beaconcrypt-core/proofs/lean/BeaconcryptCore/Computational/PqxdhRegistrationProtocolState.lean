import BeaconcryptCore.Computational.PqxdhAcceptedRegistration
import BeaconcryptCore.Computational.RawCtxProtocolReveals

/-!
Ten operational statements retain the actual finite role families, registration allocation controls, consumed-ID histories and one shared primitive state. Source record/public/reveal execution changes only its actual fields. Successful response construction installs only the selected reached Server; other owners and all primitive effects remain present. Native binding and identity-key-ID accessors select stored fields. Consumed-list versus native HashSet representation, allocator effects, codecs and deployment ownership remain explicit contracts. These statements add no freshness or cryptographic-security assumption.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationProtocolState

abbrev Roles (M P I D K : Type) (S B : Nat) :=
  RawCtxProtocolReveals.State M P I D K S B

/-- Private source state: existing role objects, registration controls and consumed IDs share one primitive state. -/
structure State (M P I D K A : Type) (S B : Nat) where
  roles : Roles M P I D K S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes
  primitive : RawCtxSharedPrimitive.SharedState A

variable {M P I D K A : Type} {S B : Nat}

abbrev Projection := Roles M P I D K S B × RawCtxSharedPrimitive.SharedState A

def project (state : State M P I D K A S B) : Projection (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) :=
  (state.roles, state.primitive)

def restore (state : State M P I D K A S B) (result : Projection (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) : State M P I D K A S B :=
  { state with roles := result.1, primitive := result.2 }

theorem restore_project (state : State M P I D K A S B) : restore state (project state) = state := rfl

/-- Existing record, public and reveal requests execute the unchanged source handler. -/
noncomputable def sourceImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (State M P I D K A S B) ProbComp) :=
  fun query state => do
    let result ← (RawCtxProtocolReveals.sourceImpl source writer S B senderId route decode query).run (project state)
    pure (result.1, restore state result.2)

/-- The complete native role/cache run is retained, with controls and consumed IDs unchanged by these capabilities. -/
theorem source_schedule {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : State M P I D K A S B) :
    (simulateQ (sourceImpl source writer senderId route decode) client).run state =
      (fun result => (result.1, restore state result.2)) <$>
        (simulateQ (RawCtxProtocolReveals.sourceImpl source writer S B senderId route decode) client).run (project state) := by
  have complete := map_run_simulateQ_eq_of_query_map_eq
    (RawCtxProtocolReveals.sourceImpl source writer S B senderId route decode)
    (sourceImpl source writer senderId route decode) (restore state)
    (fun query before => by
      simp only [sourceImpl, StateT.run, map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      rfl) client (project state)
  exact complete.symm

/-- This is the actual selected Server state; binding comes from its current public identity and sender accessor. -/
def input (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (state : State M P I D K A S B) :
    PqxdhAcceptedRegistration.Input M P (List Pqxdh.Bytes) (RawCtxSharedPrimitive.SharedState A) :=
  let selected := (state.roles.1.1 index).server
  ⟨⟨selected.identity, senderId selected.metadata⟩,
    ⟨selected, senderId selected.metadata, state.controls index, state.consumed index⟩,
    metadata, state.primitive⟩

/-- Reinstall only the selected source Server and its control/consumed fields, preserving all other owners and the actual primitive poststate. -/
def install (index : Fin S) (state : State M P I D K A S B)
    (updated : PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState A) : State M P I D K A S B :=
  { roles := ((Function.update state.roles.1.1 index
        { state.roles.1.1 index with server := updated.server }, state.roles.1.2), state.roles.2)
    controls := Function.update state.controls index updated.control
    consumed := Function.update state.consumed index updated.consumed
    primitive := primitive }

/-- Extraction followed by installation is exact, including the selected raw-attempt counter. -/
theorem install_input (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (state : State M P I D K A S B) :
    install index state (input senderId index metadata state).state state.primitive = state := by
  simp [install, input, Function.update_eq_self]

/-- All unselected native objects and analysis history survive publication; the selected raw counter is retained. -/
theorem install_fields (index : Fin S) (state : State M P I D K A S B)
    (updated : PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState A) :
    (install index state updated primitive).roles.1.1 index =
      { state.roles.1.1 index with server := updated.server } ∧
    (install index state updated primitive).controls index = updated.control ∧
    (install index state updated primitive).consumed index = updated.consumed ∧
    (install index state updated primitive).roles.1.2 = state.roles.1.2 ∧
    (install index state updated primitive).roles.2 = state.roles.2 ∧
    (install index state updated primitive).primitive = primitive ∧
    ∀ other, other ≠ index →
      (install index state updated primitive).roles.1.1 other = state.roles.1.1 other ∧
      (install index state updated primitive).controls other = state.controls other ∧
      (install index state updated primitive).consumed other = state.consumed other := by
  simp only [install, Function.update_self, true_and]
  intro other different
  simp only [Function.update_of_ne different, and_self]

/-- Ready is interpreter-private. Only its already-performed consumption update is installed here. -/
def consume (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State M P I D K A S B) :
    State M P I D K A S B :=
  { state with consumed := Function.update state.consumed index ready.consumed.consumed }

theorem input_consume (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State M P I D K A S B) :
    input senderId index metadata (consume index ready state) =
      (input senderId index metadata state).afterReady ready := by
  simp [input, consume, PqxdhAcceptedRegistration.Input.afterReady]

/-- The first registration send uses exactly the same fixed KDF, AEAD, writer and CTX cache as subsequent record operations. -/
noncomputable def registrationImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl PqxdhServerRegistrationPublication.NativeSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  fun query => match query with
  | .inl request => (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
      ∘ₛ RawCtxMixedOwner.sendLift) request
  | .inr request => aux request

/-- Even diagnostic branches retain their primitive poststate; actual typed builders will rule these branches out. -/
def reinstall (index : Fin S) (state : State M P I D K A S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState A) :
    RustM (Option PqxdhServerRegistrationPublication.Response) × State M P I D K A S B :=
  match result.1 with
  | .ok value => (.ok value.1, install index state value.2 result.2)
  | .fail error => (.fail error, { state with primitive := result.2 })
  | .div => (.div, { state with primitive := result.2 })

/-- A private accepted-root invocation uses the reached role/map/control/cache and resumes from its actual complete poststate. -/
noncomputable def build
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (State M P I D K A S B) ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response)) :=
  fun state =>
    let current := consume index ready state
    let selected := input senderId index metadata current
    reinstall index current <$> (simulateQ (registrationImpl source writer aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhAcceptedRegistration.buildReady source selected.binding ready metadata selected.state))).run current.primitive

/-- This is the original consumed pending token and supplied root, executed on the selected current native Server. -/
noncomputable def nativeBuild
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (application : Option Pqxdh.Bytes) :
    StateT (State M P I D K A S B) ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response)) :=
  fun state =>
    let selected := input senderId index metadata state
    reinstall index state <$> (simulateQ (registrationImpl source writer aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhServerRegistrationPublication.build source pending root application metadata selected.state))).run state.primitive

/-- Actual field correspondence replaces no state: the same complete builder result is installed back into the reached role family. -/
theorem build_native
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State M P I D K A S B)
    (pending : pqxdh.PendingServerRegistration)
    (fields : PqxdhRegistrationInputs.used pending =
      PqxdhAcceptedRegistration.usedReady source.crypto (input senderId index metadata state).binding ready) :
    (build source writer aux senderId index metadata ready).run state =
      (nativeBuild source writer aux senderId index metadata pending ready.root ready.application).run
        (consume index ready state) := by
  simp only [build, nativeBuild, StateT.run, PqxdhAcceptedRegistration.buildReady]
  rw [show (input senderId index metadata (consume index ready state)).binding =
    (input senderId index metadata state).binding from rfl, ← fields, PqxdhRegistrationInputs.build_exact]

/-- The wrapper never discards a diagnostic poststate: every supported actual builder result is an ordinary optional reply. -/
theorem build_normal
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : State M P I D K A S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response) × State M P I D K A S B)
    (present : result ∈ support ((build source writer aux senderId index metadata ready).run state)) :
    ∃ reply, result.1 = ok reply := by
  dsimp only [build, StateT.run] at present
  rw [support_map] at present
  obtain ⟨original, present, rfl⟩ := present
  obtain ⟨value, equal⟩ := PqxdhAcceptedRegistration.buildReady_run_normal
    (registrationImpl source writer aux) source (input senderId index metadata (consume index ready state)).binding
    ready metadata (input senderId index metadata (consume index ready state)).state
    (consume index ready state).primitive original present
  rw [equal]
  exact ⟨value.1, rfl⟩

/-- The original extracted acceptance/RID establishes the exact consumed-list update on the reached Server. -/
theorem accepted_consumption (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (state : State M P I D K A S B) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (oneTime : List.Vector UInt8 32)
    (ephemeral : List.Vector UInt8 32) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext)
    (root : PqxdhSecretInputKdf.RootOutput) (registration : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (acceptedState : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (accepted : pqxdh.server_accept (state.controls index) registration status
      (input senderId index metadata state).binding coins secrets = ok (.Ok (acceptedState, pending)))
    (hidentity : PqxdhRefinement.absBytes registration.beacon_identity_public_key = identity.toList)
    (honeTime : PqxdhRefinement.absBytes registration.beacon_one_time_public_key = oneTime.toList)
    (history : server.consumed = state.consumed index) :
    consume index (PqxdhPrivateAcceptedRoot.ready server application identity oneTime ephemeral ciphertext root) state =
      { state with consumed := Function.update state.consumed index (PqxdhRefinement.absBytes pending.registration_id.bytes :: state.consumed index) } := by
  rw [PqxdhRegistrationInputs.accepted_rid (state.controls index) acceptedState registration status
    (input senderId index metadata state).binding coins secrets pending accepted, hidentity, honeTime]
  simp only [consume, PqxdhPrivateAcceptedRoot.ready, history]

/-- Native private identity fields and the fixed identity_key_kid are distinct from allocation state and remote peer handles. -/
structure ServerMetadata (IdentityFields Metadata : Type) where
  identity : IdentityFields
  identity_key_kid : Std.U64
  metadata : Metadata

/-- This accessor is specifically the stored Server.identity_key_kid used at both native callsites. -/
def serverIdentityKeyId {IdentityFields Metadata : Type} (fields : ServerMetadata IdentityFields Metadata) : Std.U64 :=
  fields.identity_key_kid

/-- The native metadata specialization derives both binding and stored sender from that same fixed field. -/
theorem native_input_fields {IdentityFields Metadata : Type} (index : Fin S) (metadata : P)
    (state : State (ServerMetadata IdentityFields Metadata) P I D K A S B) :
    (input serverIdentityKeyId index metadata state).binding.identity_key_id =
      (state.roles.1.1 index).server.metadata.identity_key_kid ∧
    (input serverIdentityKeyId index metadata state).state.identityKeyId =
      (state.roles.1.1 index).server.metadata.identity_key_kid ∧
    (input serverIdentityKeyId index metadata state).state.control = state.controls index ∧
    (input serverIdentityKeyId index metadata state).state.server.peers = (state.roles.1.1 index).server.peers := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Actual record/public/reveal scheduling preserves registration controls and consumed IDs through every supported adaptive result. -/
theorem source_controls {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : State M P I D K A S B)
    (result : Result × State M P I D K A S B)
    (present : result ∈ support ((simulateQ (sourceImpl source writer senderId route decode) client).run state)) :
    result.2.controls = state.controls ∧ result.2.consumed = state.consumed := by
  rw [source_schedule, support_map] at present
  obtain ⟨original, _, rfl⟩ := present
  exact ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhRegistrationProtocolState

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.restore_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.restore_project

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.source_schedule

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.install_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.install_input

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.install_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.install_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.input_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.input_consume

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.build_native

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.build_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.build_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.accepted_consumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.accepted_consumption

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.native_input_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.native_input_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.source_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationProtocolState.source_controls
