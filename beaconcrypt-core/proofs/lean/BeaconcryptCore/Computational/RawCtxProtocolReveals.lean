import BeaconcryptCore.Computational.RawCtxProtocolUniform
import BeaconcryptCore.PanicFreedom.Lookup

/-!
Ten statements extend the replicated actual record interface with explicit compromise reads of the installed send chain, receive chain and a selected skipped material. A Server handle reads its actual peer entry; a Beacon handle reads only its established kernel. Missing peers and inactive phases reject. The skipped accessor normalizes only the unique result of the previously proved total extracted lookup, retaining actual sequence/tag rejection without a well-formed-state or successful-lookup premise.

Both source and backend experiments retain the full role families and shared primitive state through every adaptive record/public/reveal continuation. Reads do not consume keys or modify native state. A private analysis history records each original reveal request, actual optional reply and global API position; every operation, including rejection, increments that position. Complete one-step and schedule equations preserve all replies and effects. Supported schedules extend the prior reveal history and obey their explicit total source-query cap.

Compromise reads are an explicit experiment capability, not a new native public network API or a claim that ordinary record replies disclose keys. Initial states may be correlated. History may contain revealed secret copies and remains private analysis state; the adversary receives only the requested reply and never the whole interpreter state. Live identity and prekey/KEM compromise, root knowledge at its actual point of availability, allocation/registration, public API declassification, target freshness and cryptographic hybrid simulations still require their consuming interfaces. Disposed secrets are not reintroduced as live reads. Snapshots, persistence, restoration and their consequences are outside the active protocol proof; native memory and physical erasure remain external. Current-chain exposure must include descendants under the real public KDF; no post-compromise recovery, primitive hardness or secrecy conclusion is asserted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxProtocolReveals

inductive Owner (serverCount beaconCount : Nat) where
  | server (index : Fin serverCount) (peer : Std.U64)
  | beacon (index : Fin beaconCount)
  deriving DecidableEq

inductive Request (serverCount beaconCount : Nat) where
  | sendChain (owner : Owner serverCount beaconCount)
  | receiveChain (owner : Owner serverCount beaconCount)
  | skippedKey (owner : Owner serverCount beaconCount) (sequence : Std.U64)
  deriving DecidableEq

def RevealSpec (serverCount beaconCount : Nat) : OracleSpec (Request serverCount beaconCount)
  | .sendChain _ | .receiveChain _ => core.option.Option RatchetChain
  | .skippedKey _ _ => core.option.Option RatchetMaterial

abbrev Roles (Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount

def selectedKernel {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (owner : Owner serverCount beaconCount)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) : Option ConcreteRatchetKernel :=
  match owner with
  | .server index peer => (roles.1 index).server.peers peer |>.map RawCtxServerRouting.Peer.kernel
  | .beacon index => match (roles.2 index).beacon.phase with
      | .established _ _ kernel => some kernel
      | _ => none

noncomputable def skippedKey (kernel : ConcreteRatchetKernel) (sequence : Std.U64) :
    core.option.Option RatchetMaterial :=
  (refined.refined_receive_key_total kernel.refined sequence).choose

/-- The normalizer returns exactly the actual total extracted material lookup result. -/
theorem skipped_exact (kernel : ConcreteRatchetKernel) (sequence : Std.U64) :
    refined.refined_receive_key kernel.refined sequence = ok (skippedKey kernel sequence) := by
  exact (refined.refined_receive_key_total kernel.refined sequence).choose_spec

noncomputable def reveal {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (request : (RevealSpec serverCount beaconCount).Domain)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (RevealSpec serverCount beaconCount).Range request :=
  match request with
  | .sendChain owner => match selectedKernel owner roles with
      | none => .None
      | some kernel => .Some kernel.refined.send_chain
  | .receiveChain owner => match selectedKernel owner roles with
      | none => .None
      | some kernel => .Some kernel.refined.receive_chain
  | .skippedKey owner sequence => match selectedKernel owner roles with
      | none => .None
      | some kernel => skippedKey kernel sequence

abbrev Observation (serverCount beaconCount : Nat) :=
  (request : (RevealSpec serverCount beaconCount).Domain) × (RevealSpec serverCount beaconCount).Range request

structure History (serverCount beaconCount : Nat) where
  position : Nat
  observations : List (Nat × Observation serverCount beaconCount)

def tick {serverCount beaconCount : Nat} (history : History serverCount beaconCount) : History serverCount beaconCount :=
  { history with position := history.position + 1 }

def note {serverCount beaconCount : Nat} (observation : Observation serverCount beaconCount)
    (history : History serverCount beaconCount) : History serverCount beaconCount :=
  ⟨history.position + 1, history.observations ++ [(history.position, observation)]⟩

abbrev SourceSpec (serverCount beaconCount : Nat) :=
  RawCtxProtocolRoles.SourceSpec serverCount beaconCount + RevealSpec serverCount beaconCount

abbrev State (Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount × History serverCount beaconCount

noncomputable def protocolImpl {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
        (OracleComp RawCtxServerServices.BackendSpec)) :=
  fun query state => match query with
  | .inl request => do
      let result ← (RawCtxProtocolRoles.protocolImpl serverCount beaconCount senderId route decode request).run state.1
      pure (result.1, (result.2, tick state.2))
  | .inr request =>
      let reply := reveal request state.1
      pure (reply, (state.1, note ⟨request, reply⟩ state.2))

noncomputable def sourceImpl {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
        RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => do
      let result ← (RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount senderId route decode request).run
        (state.1.1, state.2)
      pure (result.1, ((result.2.1, tick state.1.2), result.2.2))
  | .inr request =>
      let reply := reveal request state.1.1
      pure (reply, ((state.1.1, note ⟨request, reply⟩ state.1.2), state.2))

/-- Interpretation retains the complete role, timestamped reveal and primitive states. -/
theorem protocol_interpretation {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    ((RawCtxProtocolBackend.backend source writer).mapStateTBase
      (protocolImpl (PeerMetadata := PeerMetadata) (Identity := Identity) (DhPair := DhPair) (KemPair := KemPair)
        serverCount beaconCount senderId route decode)).flattenStateT =
      (sourceImpl (Auxiliary := Auxiliary) source writer serverCount beaconCount senderId route decode) := by
  funext query state
  cases query with
  | inl request =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, protocolImpl, sourceImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map]
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        (((fun a => (a.1, a.2, tick state.1.2)) <$>
          simulateQ (RawCtxProtocolBackend.backend source writer)
            ((RawCtxProtocolRoles.protocolImpl serverCount beaconCount senderId route decode request).run state.1.1)).run state.2) = _
      rw [StateT.run_map]
      have exactStep := congrFun (congrFun
        (RawCtxProtocolRoles.protocol_interpretation (PeerMetadata := PeerMetadata)
          (Identity := Identity) (DhPair := DhPair) (KemPair := KemPair) (Auxiliary := Auxiliary)
          source writer serverCount beaconCount senderId route decode) request) (state.1.1, state.2)
      simpa only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
        Functor.map_map, Function.comp_def, SourceSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim] using
        congrArg (fun computation => (fun a => (a.1, (a.2.1, tick state.1.2), a.2.2)) <$> computation) exactStep
  | inr request =>
      simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, protocolImpl, sourceImpl,
        StateT.run, StateT.mk]
      rfl

/-- Every adaptive record/public/reveal continuation receives its actual optional replies. -/
theorem schedule_interpretation {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxProtocolBackend.backend source writer)
      ((simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl source writer serverCount beaconCount senderId route decode) client).run
          (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, protocol_interpretation]

/-- A read retains all native roles and records the original request/reply at the current API position. -/
theorem reveal_step {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RevealSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (protocolImpl serverCount beaconCount senderId route decode (.inr request)).run state =
      pure (reveal request state.1, (state.1, note ⟨request, reveal request state.1⟩ state.2)) := by
  rfl

/-- Both disclosed chains are the actual extracted current-chain fields of the selected owner. -/
theorem chain_reveal_exact {Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (kernel : ConcreteRatchetKernel) (selected : selectedKernel owner roles = some kernel) :
    reveal (.sendChain owner) roles = .Some kernel.refined.send_chain ∧
      kernel.send_chain = ok kernel.refined.send_chain ∧
      reveal (.receiveChain owner) roles = .Some kernel.refined.receive_chain ∧
      kernel.receive_chain = ok kernel.refined.receive_chain := by
  simp [reveal, selected, ConcreteRatchetKernel.send_chain, ConcreteRatchetKernel.receive_chain,
    refined.RefinedRatchet.impl.send_chain, refined.RefinedRatchet.impl.receive_chain]
  exact ⟨rfl, rfl⟩

/-- A disclosed skipped result is the actual guarded lookup, including absent or mismatched material. -/
theorem skipped_reveal_exact {Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (kernel : ConcreteRatchetKernel) (sequence : Std.U64)
    (selected : selectedKernel owner roles = some kernel) :
    refined.refined_receive_key kernel.refined sequence =
      ok (reveal (.skippedKey owner sequence) roles) := by
  simpa only [reveal, selected, RevealSpec, OracleSpec.Range, OracleSpec.ofFn] using skipped_exact kernel sequence

/-- No selected native kernel means rejection for every record-material reveal kind. -/
theorem missing_reveals {Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} (owner : Owner serverCount beaconCount)
    (roles : Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (missing : selectedKernel owner roles = none) (sequence : Std.U64) :
    reveal (.sendChain owner) roles = .None ∧ reveal (.receiveChain owner) roles = .None ∧
      reveal (.skippedKey owner sequence) roles = .None := by
  simp only [reveal, missing]
  exact ⟨rfl, rfl, rfl⟩

/-- Actual source compromise reads also preserve the complete shared auxiliary/cache state. -/
theorem source_reveal_step {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RevealSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    (sourceImpl source writer serverCount beaconCount senderId route decode (.inr request)).run state =
      pure (reveal request state.1.1,
        ((state.1.1, note ⟨request, reveal request state.1.1⟩ state.1.2), state.2)) := by
  rfl

/-- Every supported operation advances exactly one API position and appends exactly one entry iff it is a reveal. -/
theorem step_history {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (result : (SourceSpec serverCount beaconCount).Range query ×
      State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (present : result ∈ support ((protocolImpl serverCount beaconCount senderId route decode query).run state)) :
    result.2.2.position = state.2.position + 1 ∧
      ∃ suffix, result.2.2.observations = state.2.observations ++ suffix ∧
        suffix.length = if query.isRight then 1 else 0 := by
  cases query with
  | inl request =>
      simp only [protocolImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at present
      obtain ⟨_, _, rfl⟩ := present
      exact ⟨rfl, [], by simp [tick]⟩
  | inr request =>
      simp only [protocolImpl, StateT.run, mem_support_pure_iff] at present
      subst result
      exact ⟨rfl, [(state.2.position, ⟨request, reveal request state.1⟩)], rfl, rfl⟩

/-- Every supported adaptive schedule preserves the prior reveal prefix and bounds total position/history growth. -/
theorem schedule_history {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (result : Result × State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (present : result ∈ support ((simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state)) :
    result.2.2.position ≤ state.2.position + budget ∧
      ∃ suffix, result.2.2.observations = state.2.observations ++ suffix ∧ suffix.length ≤ budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at present
      subst result
      exact ⟨Nat.le_add_right _ _, [], by simp⟩
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
      obtain ⟨reply, supported, continued⟩ := present
      obtain ⟨positionStep, firstLog, prefixEq, prefixLength⟩ :=
        step_history serverCount beaconCount senderId route decode query state reply supported
      obtain ⟨positionTail, tailLog, tailEq, tailLength⟩ :=
        ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result continued
      refine ⟨by omega, firstLog ++ tailLog, ?_, ?_⟩
      · rw [tailEq, prefixEq, List.append_assoc]
      · simp only [List.length_append]
        split at prefixLength <;> omega

end BeaconcryptCore.Computational.RawCtxProtocolReveals

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.skipped_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.skipped_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.protocol_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.protocol_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.reveal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.reveal_step

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.chain_reveal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.chain_reveal_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.skipped_reveal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.skipped_reveal_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.missing_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.missing_reveals

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.source_reveal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.source_reveal_step

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.step_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.step_history

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolReveals.schedule_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolReveals.schedule_history
