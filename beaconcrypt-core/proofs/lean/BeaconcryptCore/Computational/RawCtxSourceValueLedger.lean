import BeaconcryptCore.Computational.RawCtxLiveSourceFreshness
import BeaconcryptCore.Computational.RawCtxFreshChainCut

/-!
A private finite value ledger observes actual source replies without changing the native role state, original reveal history, public randomness or shared primitive effects. It records both real public HKDF 32-byte projections and the existing optional live chain/material replies. The nonce projection is 12 bytes and does not directly disclose a 32-byte chain. Arbitrary computations on public bytes remain adversarial candidate work, not an unbounded knowledge closure. Prior actual root disclosures can enter the initial ledger without inventing a later root-read service. Freshness still uses the actual values of the consuming hybrid's finite lineage.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceValueLedger
open RawCtxProtocolReveals RawCtxLiveLineage RawCtxLiveSourceFreshness
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf

def publicValues (query : JointKdfViewQuery) (reply : JointKdfViewSpec.Range query) : List RatchetChain :=
  match query with
  | ⟨_, _, .first32⟩ | ⟨_, _, .second32⟩ => [RawCtxFreshChainCut.concreteChain reply]
  | ⟨_, _, .final12⟩ => []

def returned {serverCount beaconCount : Nat}
    (query : (SourceSpec serverCount beaconCount).Domain)
    (reply : (SourceSpec serverCount beaconCount).Range query) : List RatchetChain :=
  match query with
  | .inl (.inr (.inr (.inr (.inr view)))) => publicValues view reply
  | .inr request => disclosed ⟨request, reply⟩
  | _ => []

/-- Both source 32-byte projections record their actual reply, including the shared first 64-byte prefix. -/
theorem public_chains (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (reply : RootOutput) :
    publicValues ⟨input, domain, .first32⟩ reply = [RawCtxFreshChainCut.concreteChain reply] ∧
    publicValues ⟨input, domain, .second32⟩ reply = [RawCtxFreshChainCut.concreteChain reply] := by
  exact ⟨rfl, rfl⟩

/-- One original source callback returns at most one directly exposed 32-byte key/chain coordinate. -/
theorem returned_length {serverCount beaconCount : Nat}
    (query : (SourceSpec serverCount beaconCount).Domain)
    (reply : (SourceSpec serverCount beaconCount).Range query) : (returned query reply).length ≤ 1 := by
  rcases query with (server | (beacon | (coin | (hash | view)))) | read
  all_goals try exact Nat.zero_le _
  case inl.inr.inr.inr.inr => rcases view with ⟨input, domain, projection⟩; cases projection <;> simp [returned, publicValues]
  case inr => exact disclosed_length ⟨read, reply⟩

/-- Instrumentation interprets the original complete source step and appends only its actual returned values. -/
noncomputable def observed {σ : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp)) :
    QueryImpl (SourceSpec serverCount beaconCount) (StateT (σ × List RatchetChain) ProbComp) :=
  fun query state => do
    let result ← (impl query).run state.1
    pure (result.1, (result.2, state.2 ++ returned query result.1))

/-- The observed source step preserves every original reply and state, retaining the complete prior ledger. -/
theorem step_values {σ : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp))
    (query : (SourceSpec serverCount beaconCount).Domain) (state : σ × List RatchetChain)
    (result : (SourceSpec serverCount beaconCount).Range query × σ × List RatchetChain)
    (supported : result ∈ support ((observed impl query).run state)) :
    (result.1, result.2.1) ∈ support ((impl query).run state.1) ∧
      result.2.2 = state.2 ++ returned query result.1 := by
  simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, original, rfl⟩
  exact ⟨original, rfl⟩

/-- Erasing only the private value ledger recovers the complete original adaptive execution syntactically. -/
theorem schedule_projection {σ α : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp))
    (client : OracleComp (SourceSpec serverCount beaconCount) α) (state : σ × List RatchetChain) :
    (fun result => (result.1, result.2.1)) <$> (simulateQ (observed impl) client).run state =
      (simulateQ impl client).run state.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [observed, StateT.run, bind_assoc, pure_bind, map_bind]
    exact congrArg (fun continuation => (impl query state.1) >>= continuation)
      (funext fun result => ih result.1 (result.2, state.2 ++ returned query result.1))

/-- Every adaptive source schedule retains its prior value ledger and adds at most its explicit total callback budget. -/
theorem schedule_values {σ α : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp))
    (client : OracleComp (SourceSpec serverCount beaconCount) α) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget) (state : σ × List RatchetChain)
    (result : α × σ × List RatchetChain)
    (supported : result ∈ support ((simulateQ (observed impl) client).run state)) :
    ∃ suffix, result.2.2 = state.2 ++ suffix ∧ suffix.length ≤ budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp⟩
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    obtain ⟨_, headValues⟩ := step_values impl query state reply head
    obtain ⟨suffix, tailValues, tailLength⟩ := ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result tail
    refine ⟨returned query reply.1 ++ suffix, ?_, ?_⟩
    · rw [tailValues, headValues, List.append_assoc]
    · have headLength := returned_length query reply.1
      simp only [List.length_append]
      omega

/-- Disjointness of the complete value ledger implies disjointness of its prior prefix. This auxiliary predicate includes public outputs and is not the protocol freshness rule; public-output aliases must be charged as candidate events. -/
theorem schedule_fresh {σ α : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp))
    (client : OracleComp (SourceSpec serverCount beaconCount) α) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget) (state : σ × List RatchetChain)
    (result : α × σ × List RatchetChain) (blocked : List RatchetChain)
    (supported : result ∈ support ((simulateQ (observed impl) client).run state))
    (fresh : FreshValues blocked result.2.2) : FreshValues blocked state.2 := by
  obtain ⟨suffix, values, _⟩ := schedule_values impl client budget bounded state result supported
  rw [values, freshValues_append] at fresh
  exact fresh.1

noncomputable abbrev sourceObserved {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount ×
        List RatchetChain) ProbComp) :=
  observed (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode)

/-- The actual public projection reply, native roles, original history and shared state are all retained in the ledger step. -/
theorem source_public {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : JointKdfViewQuery)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount × List RatchetChain) :
    (sourceObserved source writer serverCount beaconCount senderId route decode
      (.inl (.inr (.inr (.inr (.inr query)))))).run state =
    pure (query.project (productionStream source.crypto query.address),
      (((state.1.1.1, tick state.1.1.2), state.1.2),
        state.2 ++ publicValues query (query.project (productionStream source.crypto query.address)))) := by
  simp only [sourceObserved, observed, StateT.run, RawCtxProtocolReveals.sourceImpl,
    RawCtxProtocolRoles.sourceImpl]
  rw [show (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift)
      (.inr (.inr query)) state.1.2 = _ from RawCtxProtocolBackend.public_hkdf source writer query state.1.2]
  rfl

/-- Every underlying uniform-oracle bill is unchanged by the adaptive source value ledger; only finite local bookkeeping is added. -/
theorem uniform_bound {σ α : Type} {serverCount beaconCount : Nat}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT σ ProbComp))
    (client : OracleComp (SourceSpec serverCount beaconCount) α) (state : σ × List RatchetChain) (budget : Nat) :
    ((simulateQ (observed impl) client).run state).IsTotalQueryBound budget ↔
      ((simulateQ impl client).run state.1).IsTotalQueryBound budget := by
  rw [← schedule_projection impl client state]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

end BeaconcryptCore.Computational.RawCtxSourceValueLedger

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.public_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.public_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.returned_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.returned_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.step_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.step_values

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_values

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.schedule_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.source_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.source_public

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceValueLedger.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceValueLedger.uniform_bound
