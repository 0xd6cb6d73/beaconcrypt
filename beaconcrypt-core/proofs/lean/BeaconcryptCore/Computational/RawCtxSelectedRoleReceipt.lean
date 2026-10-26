import BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt

/-!
Actual role acceptance is attributed to the original mixed-owner raw receive after Beacon phase dispatch or Server routing and repeated peer lookup. The observer preserves actual optional replies and source publication. Selected full-tuple freshness remains an explicit source event, never a consequence of acceptance, role admission or byte freshness alone.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedAuthenticationObserver RawCtxSelectedAcceptedRecord RawCtxSelectedReceiveReceipt
open RawCtxGenericRoleStorage
variable {I D K M P Metadata : Type}

/-- A mixed-owner raw acceptance is exactly the original raw result; its outer option is not a nonce refusal or an invented plaintext. -/
theorem owner_accepts (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (bytes : Pqxdh.Bytes)
    (owner finalOwner : RawCtxChainOwner.State Kernel Metadata) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read sender (.inr bytes) owner) before)) :
    ((.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before) := by
  rw [RawCtxSelectedOwnerCompiler.raw_cases, monitor_map] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have value : result.1 = (.Some decrypted, finalOwner) := Option.some.inj (congrArg Prod.fst equal)
  have history : result.2 = after := congrArg Prod.snd equal
  have same : result = ((.Some decrypted, finalOwner), after) := Prod.ext value history
  rwa [same] at reached

/-- Accepted established-Beacon delivery is the actual selected owner call and exact role reinstallation; inactive phases cannot produce an accepted plaintext. -/
theorem beacon_accepts (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (beacon finalBeacon : BeaconState Kernel I D K) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalBeacon), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inr bytes) beacon) before)) :
    ∃ control ad kernel finalOwner,
      beacon.beacon.phase = .established control ad kernel ∧
      ((.Some decrypted, finalOwner), after) ∈ support (monitor
        (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes
          (RawCtxGenericBeacon.selected beacon control ad kernel)) before) ∧
      finalBeacon = RawCtxGenericBeacon.reinstall beacon control ad finalOwner := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases] at supported
  cases phase : beacon.beacon.phase
  case established control ad kernel =>
    simp only [phase, monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨result, reached, equal⟩ := supported
    cases value : result.1 with
    | none =>
      have impossible := congrArg Prod.fst equal
      simp only [value, Option.map_none, reduceCtorEq] at impossible
    | some owned =>
      have accepted := congrArg Prod.fst equal
      simp only [value, Option.map_some, Option.some.injEq] at accepted
      have reply : owned.1 = .Some decrypted := congrArg Prod.fst accepted
      have published : finalBeacon = RawCtxGenericBeacon.reinstall beacon control ad owned.2 :=
        (congrArg Prod.snd accepted).symm
      have history : result.2 = after := congrArg Prod.snd equal
      have same : result = (some (.Some decrypted, owned.2), after) := by
        apply Prod.ext
        · rw [value]
          exact congrArg some (Prod.ext reply rfl)
        · exact history
      rw [same] at reached
      exact ⟨control, ad, kernel, owned.2, rfl,
        owner_accepts source writer prior parent target nonce next read beacon.beacon.identityKeyId bytes
          (RawCtxGenericBeacon.selected beacon control ad kernel) owned.2 before after decrypted reached, published⟩
  all_goals simp only [phase, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    RawCtxGenericBeacon.rejected, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported

/-- Accepted Server delivery follows the actual header route, associated-data lookup and repeated peer lookup. Its actual optional plaintext and complete selected owner are retained through publication in the original peer slot. -/
theorem server_accepts (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (bytes : Pqxdh.Bytes) (server finalServer : ServerState Kernel M P) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalServer), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr bytes) server) before)) :
    ∃ kid ad peer finalOwner,
      route bytes = some kid ∧ RawCtxGenericServer.peerAssociatedData server.server kid = some ad ∧
      server.server.peers kid = some peer ∧
      ((.Some decrypted, finalOwner), after) ∈ support (monitor
        (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes
          (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts)) before) ∧
      finalServer = ⟨RawCtxGenericServer.putPeer server.server kid peer finalOwner.kernel, finalOwner.rawAttempts⟩ := by
  rw [RawCtxSelectedRoleCompiler.server_raw_cases] at supported
  cases routed : route bytes with
  | none =>
    simp only [routed, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
      Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported
  | some kid =>
    simp only [routed] at supported
    cases adFound : RawCtxGenericServer.peerAssociatedData server.server kid with
    | none =>
      simp only [adFound, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
        Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported
    | some ad =>
      simp only [adFound] at supported
      cases peerFound : server.server.peers kid with
      | none =>
        simp only [peerFound, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
          Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported
      | some peer =>
        simp only [peerFound, monitor_map, support_map, Set.mem_image] at supported
        obtain ⟨result, reached, equal⟩ := supported
        cases value : result.1 with
        | none =>
          have impossible := congrArg Prod.fst equal
          simp only [value, Option.map_none, reduceCtorEq] at impossible
        | some owned =>
          have accepted := congrArg Prod.fst equal
          simp only [value, Option.map_some, Option.some.injEq] at accepted
          have reply : owned.1 = .Some decrypted := congrArg Prod.fst accepted
          have published : finalServer =
              ⟨RawCtxGenericServer.putPeer server.server kid peer owned.2.kernel, owned.2.rawAttempts⟩ :=
            (congrArg Prod.snd accepted).symm
          have history : result.2 = after := congrArg Prod.snd equal
          have same : result = (some (.Some decrypted, owned.2), after) := by
            apply Prod.ext
            · rw [value]
              exact congrArg some (Prod.ext reply rfl)
            · exact history
          rw [same] at reached
          exact ⟨kid, ad, peer, owned.2, rfl, adFound, peerFound,
            owner_accepts source writer prior parent target nonce next read (sender server.server.metadata) bytes
              (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) owned.2 before after decrypted reached, published⟩

/-- The Beacon source event inspects exactly the phase-selected owner; it supplies neither selected-key independence nor a claim about inactive phases. -/
def BeaconSelectedFresh (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (beacon : BeaconState Kernel I D K) (before : State) : Prop :=
  match beacon.beacon.phase with
  | .established control ad kernel => SelectedFresh prior parent target nonce next read bytes
      (RawCtxGenericBeacon.selected beacon control ad kernel) before
  | _ => False

/-- The Server source event follows both original lookups and uses the exact chosen peer owner, without identifying the claimed outer ID with a registration assignment. -/
def ServerSelectedFresh (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (server : ServerState Kernel M P) (before : State) : Prop :=
  match route bytes with
  | none => False
  | some kid => match RawCtxGenericServer.peerAssociatedData server.server kid with
    | none => False
    | some ad => match server.server.peers kid with
      | none => False
      | some peer => SelectedFresh prior parent target nonce next read bytes
          (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) before

/-- Complete Beacon acceptance on its explicitly selected fresh source target supplies the actual ordinary record receipt after exact role publication. -/
theorem beacon_selected_record (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (beacon finalBeacon : BeaconState Kernel I D K) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalBeacon), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inr bytes) beacon) before))
    (selected : BeaconSelectedFresh prior parent target nonce next read bytes beacon before) : RecordEvent read after := by
  obtain ⟨control, ad, kernel, finalOwner, phase, accepted, _⟩ :=
    beacon_accepts source writer prior parent target nonce next read bytes beacon finalBeacon before after decrypted supported
  have actual : SelectedFresh prior parent target nonce next read bytes
      (RawCtxGenericBeacon.selected beacon control ad kernel) before := by
    simpa only [BeaconSelectedFresh, phase] using selected
  exact raw_selected_record prior parent target nonce next read bytes
    (RawCtxGenericBeacon.selected beacon control ad kernel) finalOwner before after decrypted accepted actual

/-- Complete Server acceptance on its explicitly selected fresh source target supplies the actual ordinary record receipt after the original route and peer publication. -/
theorem server_selected_record (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (bytes : Pqxdh.Bytes) (server finalServer : ServerState Kernel M P) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalServer), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr bytes) server) before))
    (selected : ServerSelectedFresh prior parent target nonce next route read bytes server before) : RecordEvent read after := by
  obtain ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, accepted, _⟩ :=
    server_accepts source writer prior parent target nonce next sender route read bytes server finalServer before after decrypted supported
  have actual : SelectedFresh prior parent target nonce next read bytes
      (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) before := by
    simpa only [ServerSelectedFresh, routed, adFound, peerFound] using selected
  exact raw_selected_record prior parent target nonce next read bytes
    (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) finalOwner before after decrypted accepted actual

/-- Deterministic optional publication retains the exact callback result and observer state; it cannot manufacture an accepted plaintext. -/
theorem mapped_accepts {X Y : Type} (f : X → Y) (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option X))
    (before after : State) (value : Y)
    (supported : (some value, after) ∈ support (monitor (Option.map f <$> work) before)) :
    ∃ original, value = f original ∧ (some original, after) ∈ support (monitor work before) := by
  rw [monitor_map] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases actual : result.1 with
  | none =>
    have impossible := congrArg Prod.fst equal
    simp only [actual, Option.map_none, reduceCtorEq] at impossible
  | some original =>
    have published := congrArg Prod.fst equal
    simp only [actual, Option.map_some, Option.some.injEq] at published
    have history : result.2 = after := congrArg Prod.snd equal
    have same : result = (some original, after) := Prod.ext actual history
    exact ⟨original, published.symm, by rwa [same] at reached⟩

/-- Accepted indexed Beacon delivery is the exact selected role operation, retaining every other role and the actual updated Beacon slot. -/
theorem family_beacon_accepts {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inr (.inl ⟨index, .inr bytes⟩)) roles) before)) :
    ∃ finalBeacon, (some (.Some decrypted, finalBeacon), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inr bytes) (roles.2 index)) before) ∧
      finalRoles = (roles.1, Function.update roles.2 index finalBeacon) := by
  rw [RawCtxSelectedFamilyCompiler.family_cases] at supported
  obtain ⟨result, published, accepted⟩ := mapped_accepts _ _ before after _ supported
  have reply : result.1 = .Some decrypted := (congrArg Prod.fst published).symm
  have updated : finalRoles = (roles.1, Function.update roles.2 index result.2) := congrArg Prod.snd published
  have same : result = (.Some decrypted, result.2) := Prod.ext reply rfl
  refine ⟨result.2, ?_, updated⟩
  rw [same] at accepted
  exact accepted

/-- Accepted indexed Server delivery is the exact selected role operation, retaining every other role and the actual updated Server slot. -/
theorem family_server_accepts {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inl ⟨index, .inr bytes⟩) roles) before)) :
    ∃ finalServer, (some (.Some decrypted, finalServer), after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr bytes) (roles.1 index)) before) ∧
      finalRoles = (Function.update roles.1 index finalServer, roles.2) := by
  rw [RawCtxSelectedFamilyCompiler.family_cases] at supported
  obtain ⟨result, published, accepted⟩ := mapped_accepts _ _ before after _ supported
  have reply : result.1 = .Some decrypted := (congrArg Prod.fst published).symm
  have updated : finalRoles = (Function.update roles.1 index result.2, roles.2) := congrArg Prod.snd published
  have same : result = (.Some decrypted, result.2) := Prod.ext reply rfl
  refine ⟨result.2, ?_, updated⟩
  rw [same] at accepted
  exact accepted

/-- The actual indexed Beacon source target maps directly to the ordinary accepted-record event; selection is over the original family slot and original raw request. -/
theorem family_beacon_record {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inr (.inl ⟨index, .inr bytes⟩)) roles) before))
    (selected : BeaconSelectedFresh prior parent target nonce next read bytes (roles.2 index) before) : RecordEvent read after := by
  obtain ⟨finalBeacon, accepted, _⟩ := family_beacon_accepts source writer prior parent target nonce next sender route read
    index bytes roles finalRoles before after decrypted supported
  exact beacon_selected_record source writer prior parent target nonce next read bytes
    (roles.2 index) finalBeacon before after decrypted accepted selected

/-- The actual indexed Server source target maps directly to the ordinary accepted-record event, retaining its chosen route and original family slot. -/
theorem family_server_record {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inl ⟨index, .inr bytes⟩) roles) before))
    (selected : ServerSelectedFresh prior parent target nonce next route read bytes (roles.1 index) before) : RecordEvent read after := by
  obtain ⟨finalServer, accepted, _⟩ := family_server_accepts source writer prior parent target nonce next sender route read
    index bytes roles finalRoles before after decrypted supported
  exact server_selected_record source writer prior parent target nonce next sender route read bytes
    (roles.1 index) finalServer before after decrypted accepted selected

end BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.owner_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.owner_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.beacon_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.beacon_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.server_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.server_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.beacon_selected_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.beacon_selected_record
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.server_selected_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.server_selected_record
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.mapped_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.mapped_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_beacon_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_beacon_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_server_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_server_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_beacon_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_beacon_record
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_server_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt.family_server_record
