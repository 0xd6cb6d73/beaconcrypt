import BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler

/-!
The key-free CTX compiler retains the actual finite-family role dispatch: Beacon phases and pinned owner fields, Server peer routing and associated-data lookup, and complete publication after optional source replies. Nonce stopping is taken only on an original admitted send's selected pending seal. These are operational source equations, not assumptions that arbitrary native clients can be simulated.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
open RawCtxSelectedOwnerCompiler (Kernel Base calls originalCalls)
open RawCtxGenericRoleStorage
variable {A I D K M P : Type}

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem mapped_source {X Y : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (f : X → Y) (work : Base (Option X))
    (original : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp X) (state : State A) (stop : Prop)
    (same : Prod.map id project <$> (evaluated source key read work).run state =
      if stop then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$> original.run (project state)) :
    Prod.map id project <$> (evaluated source key read (Option.map f <$> work)).run state =
      if stop then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$> (f <$> original).run (project state) := by
  rw [RawCtxSelectedReceiveCompiler.evaluated_map]
  have mapped := congrArg (fun computation => (fun result => (Option.map f result.1, result.2)) <$> computation) same
  simp only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq, apply_ite, map_pure, Option.map_none, Option.map_some] at mapped ⊢
  convert mapped using 1

noncomputable def beacon (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : BeaconState Kernel I D K) : Base (Option (RawCtxMixedOwner.SourceSpec.Range query × BeaconState Kernel I D K)) :=
  ((RawCtxGenericBeacon.impl (calls source writer prior parent target nonce next read) read query).run before).run

noncomputable def BeaconStops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (before : BeaconState Kernel I D K)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match before.beacon.phase with
  | .established control ad kernel => RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next before.beacon.identityKeyId query
      (RawCtxGenericBeacon.selected before control ad kernel) state
  | _ => False

/-- The exact Beacon phase dispatch wraps the whole original mixed owner; an explicit nonce stop preserves the entry role instead of publishing a failed send. -/
theorem beacon_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : BeaconState Kernel I D K) :
    beacon source writer prior parent target nonce next read query before =
      match before.beacon.phase with
      | .established control ad kernel =>
          Option.map (fun result => (result.1, RawCtxGenericBeacon.reinstall before control ad result.2)) <$>
            RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read before.beacon.identityKeyId query
              (RawCtxGenericBeacon.selected before control ad kernel)
      | _ => pure (some (RawCtxGenericBeacon.rejected query before)) := by
  cases phase : before.beacon.phase
  case established control ad kernel =>
    simp only [beacon, RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxSelectedOwnerCompiler.owner,
      OptionT.run_bind, OptionT.run_pure, map_eq_bind_pure_comp]
    apply bind_congr
    intro reply
    cases reply <;> rfl
  all_goals simp only [beacon, RawCtxGenericBeacon.impl, StateT.run, phase]
  all_goals rfl

/-- The complete established or inactive Beacon record operation has the exact optional source reply and role state, with only the explicitly charged selected nonce stop added. -/
theorem beacon_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : BeaconState Kernel I D K) (state : State A) :
    Prod.map id project <$> (evaluated source key read (beacon source writer prior parent target nonce next read query before)).run state =
      if BeaconStops prior parent target nonce next query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((RawCtxGenericBeacon.impl (originalCalls source writer prior parent key target nonce next) read query).run before).run (project state) := by
  rw [beacon_cases]
  cases phase : before.beacon.phase
  case established control ad kernel =>
    have test : BeaconStops prior parent target nonce next query before state.2 ↔
      RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel) state.2 := by simp only [BeaconStops, phase]
    have same := mapped_source source key read
      (fun result => (result.1, RawCtxGenericBeacon.reinstall before control ad result.2))
      (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel))
      ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) before.beacon.identityKeyId read query).run
        (RawCtxGenericBeacon.selected before control ad kernel)) state
      (RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel) state.2)
      (RawCtxSelectedOwnerCompiler.owner_source source writer prior parent key target nonce next read before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel) state)
    rw [RawCtxGenericBeacon.established _ _ _ _ _ _ _ phase]
    simp only [bind_pure_comp]
    simpa only [test] using same
  all_goals
    have clear : ¬ BeaconStops prior parent target nonce next query before state.2 := by simp only [BeaconStops, phase, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase]
    rfl


noncomputable def server (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : ServerState Kernel M P) :
    Base (Option (RawCtxServerMixed.SourceSpec.Range query × ServerState Kernel M P)) :=
  ((RawCtxGenericServer.serverImpl (calls source writer prior parent target nonce next read) sender route read query).run before).run

/-- The source raw Server dispatch keeps header routing, identity-derived AD lookup, repeated peer lookup and exact selected owner before any CTX operation. -/
theorem server_raw_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : ServerState Kernel M P) :
    server source writer prior parent target nonce next sender route read (.inr raw) before =
      match route raw with
      | none => pure (some (.None, { before with rawAttempts := before.rawAttempts + 1 }))
      | some kid => match RawCtxGenericServer.peerAssociatedData before.server kid with
        | none => pure (some (.None, { before with rawAttempts := before.rawAttempts + 1 }))
        | some ad => match before.server.peers kid with
          | none => pure (some (.None, { before with rawAttempts := before.rawAttempts + 1 }))
          | some peer => Option.map (fun result =>
              (result.1, (⟨RawCtxGenericServer.putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩ : ServerState Kernel M P))) <$>
              RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read (sender before.server.metadata) (.inr raw)
                (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) := by
  simp only [server, RawCtxGenericServer.serverImpl, StateT.run, RawCtxGenericServer.rawServer]
  cases routed : route raw with
  | none => simp only; rfl
  | some kid =>
    simp only
    cases adFound : RawCtxGenericServer.peerAssociatedData before.server kid with
    | none => simp only; rfl
    | some ad =>
      simp only
      cases found : before.server.peers kid with
      | none => simp only; rfl
      | some peer =>
        simp only [RawCtxSelectedOwnerCompiler.owner, RawCtxChainOwner.ownerImpl, OptionT.run_bind, OptionT.run_pure,
          map_eq_bind_pure_comp]
        apply bind_congr
        intro reply
        cases reply <;> rfl

/-- Every arbitrary Server raw delivery preserves exact route rejection, selected-peer publication, optional challenger plaintext and the full source state. -/
theorem server_raw_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : ServerState Kernel M P) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (server source writer prior parent target nonce next sender route read (.inr raw) before)).run state =
      (fun result => (some result.1, result.2)) <$>
        ((RawCtxGenericServer.serverImpl (originalCalls source writer prior parent key target nonce next) sender route read (.inr raw)).run before).run
          (project state) := by
  rw [server_raw_cases]
  simp only [RawCtxGenericServer.serverImpl, StateT.run]
  unfold RawCtxGenericServer.rawServer
  cases routed : route raw with
  | none => rfl
  | some kid =>
    simp only
    cases adFound : RawCtxGenericServer.peerAssociatedData before.server kid with
    | none => rfl
    | some ad =>
      simp only
      cases found : before.server.peers kid with
      | none => rfl
      | some peer =>
        simp only
        let selected := RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts
        let publish := fun result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel P =>
          (result.1, (⟨RawCtxGenericServer.putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩ : ServerState Kernel M P))
        have rawSame := RawCtxSelectedOwnerCompiler.raw_source source writer prior parent key target nonce next read
          (sender before.server.metadata) raw selected state
        have same := mapped_source source key read publish
          (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read (sender before.server.metadata) (.inr raw) selected)
          ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) (sender before.server.metadata) read (.inr raw)).run selected)
          state False (by simp only [ite_false]; convert rawSame using 1)
        simp only [ite_false, RawCtxChainOwner.ownerImpl] at same
        simp only [publish, selected, bind_pure_comp, StateT.run] at same ⊢
        convert same using 1


noncomputable def ServerStops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : RawCtxServerMixed.SourceSpec.Domain) (before : ServerState Kernel M P)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match query with
  | .inr _ => False
  | .inl (plaintext, kid) => match RawCtxGenericServer.peerAssociatedData before.server kid with
    | none => False
    | some ad => match before.server.peers kid with
      | none => False
      | some peer => RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next (sender before.server.metadata) (.inl plaintext)
          (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) state

/-- The actual Server send preserves AD lookup, sender selection, peer lookup and original owner publication in source order. -/
theorem server_send_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (before : ServerState Kernel M P) :
    server source writer prior parent target nonce next sender route read (.inl (plaintext, kid)) before =
      match RawCtxGenericServer.peerAssociatedData before.server kid with
      | none => pure (some (none, before))
      | some ad => match before.server.peers kid with
        | none => pure (some (none, before))
        | some peer => Option.map (fun result =>
            (result.1, (⟨RawCtxGenericServer.putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩ : ServerState Kernel M P))) <$>
            RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read (sender before.server.metadata) (.inl plaintext)
              (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) := by
  simp only [server, RawCtxGenericServer.serverImpl, StateT.run, RawCtxGenericServer.sendServer]
  cases adFound : RawCtxGenericServer.peerAssociatedData before.server kid with
  | none => rfl
  | some ad =>
    simp only
    cases found : before.server.peers kid with
    | none => rfl
    | some peer =>
      simp only [RawCtxSelectedOwnerCompiler.owner, RawCtxChainOwner.ownerImpl, OptionT.run_bind, OptionT.run_pure,
        map_eq_bind_pure_comp]
      apply bind_congr
      intro reply
      cases reply <;> rfl

/-- The complete Server send has the exact source optional ciphertext, whole peer map and cache. Its extra stop occurs only at the original selected peer's actual repeated selected nonce. -/
theorem server_send_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (before : ServerState Kernel M P) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (server source writer prior parent target nonce next sender route read (.inl (plaintext, kid)) before)).run state =
      if ServerStops prior parent target nonce next sender (.inl (plaintext, kid)) before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((RawCtxGenericServer.serverImpl (originalCalls source writer prior parent key target nonce next) sender route read (.inl (plaintext, kid))).run before).run
          (project state) := by
  rw [server_send_cases]
  simp only [RawCtxGenericServer.serverImpl, StateT.run]
  unfold RawCtxGenericServer.sendServer
  cases adFound : RawCtxGenericServer.peerAssociatedData before.server kid with
  | none =>
    have clear : ¬ ServerStops prior parent target nonce next sender (.inl (plaintext, kid)) before state.2 := by
      simp only [ServerStops, adFound, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    rfl
  | some ad =>
    simp only
    cases found : before.server.peers kid with
    | none =>
      have clear : ¬ ServerStops prior parent target nonce next sender (.inl (plaintext, kid)) before state.2 := by
        simp only [ServerStops, adFound, found, not_false_eq_true]
      rw [ite_eq_right (fun h => (clear h).elim)]
      rfl
    | some peer =>
      simp only
      let selected := RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts
      let publish := fun result : Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State Kernel P =>
        (result.1, (⟨RawCtxGenericServer.putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩ : ServerState Kernel M P))
      have test : ServerStops prior parent target nonce next sender (.inl (plaintext, kid)) before state.2 ↔
          RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next (sender before.server.metadata) (.inl plaintext) selected state.2 := by
        simp only [ServerStops, adFound, found, selected]
      have same := mapped_source source key read publish
        (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read (sender before.server.metadata) (.inl plaintext) selected)
        ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) (sender before.server.metadata) read (.inl plaintext)).run selected)
        state (RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next (sender before.server.metadata) (.inl plaintext) selected state.2)
        (RawCtxSelectedOwnerCompiler.send_source source writer prior parent key target nonce next read (sender before.server.metadata) plaintext selected state)
      simp only [test, publish, selected, RawCtxChainOwner.ownerImpl, bind_pure_comp, StateT.run] at same ⊢
      convert same using 1

/-- One complete original Server record query, including all routing and lookup failures, compiles without a selected-key or fresh-nonce premise. -/
theorem server_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : ServerState Kernel M P) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (server source writer prior parent target nonce next sender route read query before)).run state =
      if ServerStops prior parent target nonce next sender query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((RawCtxGenericServer.serverImpl (originalCalls source writer prior parent key target nonce next) sender route read query).run before).run (project state) := by
  cases query with
  | inl input => exact server_send_source source writer prior parent key target nonce next sender route read input.1 input.2 before state
  | inr raw =>
    have clear : ¬ ServerStops prior parent target nonce next sender (.inr raw) before state.2 := by simp only [ServerStops, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    exact server_raw_source source writer prior parent key target nonce next sender route read raw before state


/-- Complete Beacon record dispatch makes at most one dynamic component request, including inactive phases and every rejected attempt. -/
theorem beacon_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : BeaconState Kernel I D K) :
    (beacon source writer prior parent target nonce next read query before).IsTotalQueryBound 1 := by
  rw [beacon_cases]
  cases before.beacon.phase
  case established control ad kernel =>
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedOwnerCompiler.owner_queries source writer prior parent target nonce next read before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel)
  all_goals trivial

/-- Complete Server record dispatch has one dynamic-call allowance, while actual routing and peer lookups remain explicit local work. -/
theorem server_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : ServerState Kernel M P) :
    (server source writer prior parent target nonce next sender route read query before).IsTotalQueryBound 1 := by
  cases query with
  | inl input =>
    rw [server_send_cases]
    split
    · trivial
    · split
      · trivial
      · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
          RawCtxSelectedOwnerCompiler.owner_queries source writer prior parent target nonce next read (sender before.server.metadata) (.inl input.1) _
  | inr raw =>
    rw [server_raw_cases]
    split
    · trivial
    · split
      · trivial
      · split
        · trivial
        · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
            RawCtxSelectedOwnerCompiler.owner_queries source writer prior parent target nonce next read (sender before.server.metadata) (.inr raw) _

end BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.mapped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.mapped_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_raw_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_raw_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_raw_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_send_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.beacon_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler.server_queries
