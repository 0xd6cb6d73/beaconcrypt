import BeaconcryptCore.Computational.RawCtxMixedShared
import BeaconcryptCore.Computational.RawCtxServerSend

/-!
The same assigned-peer map handles arbitrary interleaved source sends and raw receives. One common primitive interpreter retains every effect across calls. Nine checked statements identify the complete existing native/source games and derive five source caps without a peer-selection factor. Equal identities at different assigned handles and correlated record keys are allowed.

This is an operational composition, not a cryptographic multi-key reduction. Native map/codec/slot and immutable-metadata correspondence, synchronous ownership, primitive/runtime work, registration/reveal/persistence transitions and global security remain explicit boundaries. Raw API plaintext is an actual privileged result; network secrecy requires its own observation and declassification policy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxServerMixed
open RawCtxServerRouting RawCtxMixedOwner

noncomputable def rawServer {Metadata PeerMetadata : Type}
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) :
    OracleComp NativeSpec (core.option.Option RawCtxWholeOwner.Decrypted × State Metadata PeerMetadata) :=
  match route raw with
  | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
  | some kid =>
      match peerAssociatedData state.server kid with
      | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
      | some ad =>
          match state.server.peers kid with
          | none => pure (.None, { state with rawAttempts := state.rawAttempts + 1 })
          | some peer => do
              let result ← simulateQ receiveAdapter ((RawCtxWholeOwner.rawReceive decode raw).run
                ⟨selectedOwner kid ad peer, state.rawAttempts⟩)
              pure (result.1, ⟨putPeer state.server kid peer result.2.owner.kernel, result.2.rawAttempts⟩)

noncomputable def sendServer {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata) :
    OracleComp NativeSpec (Option RawCtxSourceSend.Encrypted × State Metadata PeerMetadata) :=
  simulateQ sendLift (RawCtxServerSend.sendServer senderId plaintext kid state)

abbrev SourceSpec := RawCtxServerSend.ApplicationSpec + RawCtxWholeOwner.RawSpec

noncomputable def serverImpl {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (State Metadata PeerMetadata) (OracleComp NativeSpec)) :=
  fun query state => match query with
  | .inl (plaintext, kid) => sendServer senderId plaintext kid state
  | .inr raw => rawServer route decode raw state

/-- The native routing, selected source owner and complete primitive state have exactly the same execution. -/
theorem raw_interpretation {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) :
    (simulateQ impl (rawServer route decode raw state)).run primitive =
      RawCtxServerRouting.rawGame (impl ∘ₛ receiveAdapter) route decode raw state primitive := by
  cases hr : route raw <;> simp only [rawServer, RawCtxServerRouting.rawGame, hr]
  case some kid =>
    cases hp : state.server.peers kid <;> simp [peerAssociatedData, hp, RawCtxWholeOwner.rawGame, ← QueryImpl.simulateQ_compose]
  case none => simp

/-- Native sends retain the source routing and complete primitive poststate under the common interface. -/
theorem send_interpretation {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : State Metadata PeerMetadata) (primitive : PrimitiveState) :
    (simulateQ impl (sendServer senderId plaintext kid state)).run primitive =
      RawCtxServerSend.sendGame (impl ∘ₛ sendLift) senderId plaintext kid state primitive := by
  simp only [sendServer, RawCtxServerSend.sendGame, QueryImpl.simulateQ_compose]

noncomputable def sourceImpl {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (State Metadata PeerMetadata × PrimitiveState) (OracleComp base)) :=
  fun query state => match query with
  | .inl (plaintext, kid) => do
      let result ← RawCtxServerSend.sendGame (impl ∘ₛ sendLift)
        senderId plaintext kid state.1 state.2
      pure (result.1.1, (result.1.2, result.2))
  | .inr raw => do
      let result ← RawCtxServerRouting.rawGame (impl ∘ₛ receiveAdapter)
        route decode raw state.1 state.2
      pure (result.1.1, (result.1.2, result.2))

/-- Flattening retains one complete server map and the actual primitive state for either request. -/
theorem server_interpretation {Metadata PeerMetadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    (impl.mapStateTBase (serverImpl (PeerMetadata := PeerMetadata) senderId route decode)).flattenStateT =
      sourceImpl impl senderId route decode := by
  funext query state
  rcases query with ⟨plaintext, kid⟩ | raw <;> simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, serverImpl, sourceImpl]
  all_goals simp only [bind_pure_comp]
  all_goals congr 1
  all_goals first | exact send_interpretation _ _ _ _ _ _ | exact raw_interpretation _ _ _ _ _ _

/-- Arbitrary interleaving retains the original result, full assigned-peer map and complete primitive poststate. -/
theorem schedule_interpretation {Metadata PeerMetadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Metadata PeerMetadata)
    (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (serverImpl senderId route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl impl senderId route decode) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, server_interpretation]

/-- Header and peer lookup add no cryptographic call; every raw attempt retains the actual source-window cap. -/
theorem raw_bound {Metadata PeerMetadata : Type}
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata PeerMetadata) (kind : CallKind) :
    (rawServer route decode raw state).IsQueryBoundP
      (fun query => callKind query = kind) (receiveCost kind) := by
  cases hr : route raw <;> simp only [rawServer, hr]
  case some kid =>
    cases hp : state.server.peers kid <;> simp [peerAssociatedData, hp]
    exact RawCtxMixedOwner.receive_bounds (0#u64) decode raw _ kind
  case none => exact isQueryBoundP_pure _ _ _

/-- Adaptive target selection does not add primitive work to one source send. -/
theorem send_bound {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Metadata PeerMetadata)
    (kind : CallKind) :
    (sendServer senderId plaintext kid state).IsQueryBoundP
      (fun query => callKind query = kind) (sendCost kind) := by
  cases hp : state.server.peers kid with
  | none => simp [sendServer, RawCtxServerSend.sendServer_missing senderId plaintext kid state hp]
  | some peer =>
      rw [sendServer, RawCtxServerSend.sendServer_selected senderId plaintext kid state peer hp]
      simp only [bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff, ← QueryImpl.simulateQ_compose]
      exact RawCtxMixedOwner.send_bounds (senderId state.server.metadata) (fun _ => none) plaintext _ kind

/-- All-continuation send/raw caps retain the full adaptive peer map with no peer-selection factor. -/
theorem schedule_bound {Metadata PeerMetadata Result : Type} (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Metadata PeerMetadata) (kind : CallKind) :
    ((simulateQ (serverImpl senderId route decode) client).run state).IsQueryBoundP
      (fun query => callKind query = kind) (sendCost kind * qSend + receiveCost kind * qRaw) := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hSend hRaw
      rw [simulateQ_query_bind, StateT.run_bind]
      rcases query with ⟨plaintext, kid⟩ | raw <;> simp only [Sum.isLeft, Sum.isRight, Bool.false_eq_true, not_true_eq_false, false_or, ↓reduceIte] at hSend hRaw
      case inl =>
        apply (isQueryBoundP_bind (send_bound senderId plaintext kid state kind)
          (fun result _ => ih result.1 (qSend - 1) qRaw (hSend.2 result.1)
            (hRaw.2 result.1) result.2)).mono
        cases kind <;> simp only [sendCost, receiveCost] <;> omega
      case inr =>
        apply (isQueryBoundP_bind (raw_bound route decode raw state kind)
          (fun result _ => ih result.1 qSend (qRaw - 1) (hSend.2 result.1)
            (hRaw.2 result.1) result.2)).mono
        cases kind <;> simp only [sendCost, receiveCost] <;> omega

/-- The common ledger counts all source operations across the selected peer map. -/
theorem schedule_bounds {Metadata PeerMetadata Result : Type} (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Metadata PeerMetadata) :
    let program := (simulateQ (serverImpl senderId route decode) client).run state
    program.IsQueryBoundP (fun query => callKind query = .kdf) (qSend + 51 * qRaw) ∧
      program.IsQueryBoundP (fun query => callKind query = .sealing) qSend ∧
      program.IsQueryBoundP (fun query => callKind query = .opening) qRaw ∧
      program.IsQueryBoundP (fun query => callKind query = .hash) (qSend + qRaw) ∧
      program.IsQueryBoundP (fun query => callKind query = .writer) qSend := by
  simpa only [sendCost, receiveCost, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using
    And.intro (schedule_bound senderId route decode client qSend qRaw hSend hRaw state .kdf)
      (And.intro (schedule_bound senderId route decode client qSend qRaw hSend hRaw state .sealing)
        (And.intro (schedule_bound senderId route decode client qSend qRaw hSend hRaw state .opening)
          (And.intro (schedule_bound senderId route decode client qSend qRaw hSend hRaw state .hash)
            (schedule_bound senderId route decode client qSend qRaw hSend hRaw state .writer))))

noncomputable def sharedSchedule {Metadata PeerMetadata Auxiliary Result : Type}
    (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Metadata PeerMetadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ProbComp ((Result × State Metadata PeerMetadata) × RawCtxSharedPrimitive.SharedState Auxiliary) :=
  (simulateQ (RawCtxMixedShared.sharedImpl c writer kdf)
    ((simulateQ (serverImpl senderId route decode) client).run state)).run primitive

/-- One shared cache accounts for every peer and every failed commitment attempt. -/
theorem shared_uniform {Metadata PeerMetadata Auxiliary Result : Type}
    (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Metadata PeerMetadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw) :
    (sharedSchedule c writer kdf senderId route decode client state primitive).IsTotalQueryBound
      (kdfCoins * (qSend + 51 * qRaw) + 64 * (qSend + qRaw)) := by
  exact RawCtxMixedShared.shared_uniform c writer kdf kdfCoins bounded _ _ _
    (schedule_bounds senderId route decode client qSend qRaw hSend hRaw state).1
    (schedule_bounds senderId route decode client qSend qRaw hSend hRaw state).2.2.2.1 primitive

end BeaconcryptCore.Computational.RawCtxServerMixed

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.raw_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.raw_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.send_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.send_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.server_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.server_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.raw_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.raw_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.send_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.send_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.schedule_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.schedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.schedule_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxServerMixed.shared_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerMixed.shared_uniform
