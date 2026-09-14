import BeaconcryptCore.Computational.RawCtxGenericFamilyLive
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The actual generic Server/Beacon frontends retain the query caps of their exact receive, send, public and read callbacks. Every empty-input, decode, sender/AD/peer, phase and publication branch is included. The original aggregate source budget then accumulates weighted costs across both role families and every adaptive typed reply, with no operational session multiplier.

These are compositional syntax bounds. Their callback caps are explicit operational obligations, discharged by the concrete slot or native callback ledger in the consuming module. They are not cryptographic or source freshness assumptions and do not declare local routing, parsing, lookup, copying or public evaluation free. No distribution-based cost transport or persistence interface is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxServerServiceBounds

/-- Original raw admission can invoke only its one actual receive program; all rejection paths spend no primitive query. -/
theorem owner_raw {ι Kernel Metadata : Type} {spec : OracleSpec ι}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate budget)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : RawCtxChainOwner.State Kernel Metadata) :
    ((RawCtxChainOwner.rawReceive calls decode raw).run state).IsQueryBoundP predicate budget := by
  simp only [RawCtxChainOwner.rawReceive, StateT.run]
  split
  · trivial
  · split
    · trivial
    · split
      · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using bounded _ _ _
      · trivial

/-- Empty sends reject before callbacks, and every active send executes only its original full send program. -/
theorem owner_send {ι Kernel Metadata : Type} {spec : OracleSpec ι}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate budget)
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes) (state : RawCtxChainOwner.State Kernel Metadata) :
    ((RawCtxChainOwner.sendOwner calls senderId plaintext).run state).IsQueryBoundP predicate budget := by
  simp only [RawCtxChainOwner.sendOwner, StateT.run]
  split
  · trivial
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using bounded _ _

/-- Server routing and all peer/AD admission gates retain the complete original receive-program cap. -/
theorem server_raw {ι Kernel Metadata PeerMetadata : Type} {spec : OracleSpec ι}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate budget)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : ServerState Kernel Metadata PeerMetadata) :
    (RawCtxGenericServer.rawServer calls route decode raw state).IsQueryBoundP predicate budget := by
  simp only [RawCtxGenericServer.rawServer]
  split
  · trivial
  · split
    · trivial
    · split
      · trivial
      · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using owner_raw calls predicate budget bounded decode raw _

/-- Server AD lookup, sender selection and original peer publication add no primitive request to the actual send program. -/
theorem server_send {ι Kernel Metadata PeerMetadata : Type} {spec : OracleSpec ι}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate budget)
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : ServerState Kernel Metadata PeerMetadata) :
    (RawCtxGenericServer.sendServer calls senderId plaintext kid state).IsQueryBoundP predicate budget := by
  simp only [RawCtxGenericServer.sendServer]
  split
  · trivial
  · split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using owner_send calls predicate budget bounded _ plaintext _

/-- Every Beacon phase either rejects or invokes exactly the original established owner, retaining its send/raw resource class. -/
theorem beacon_step {ι Kernel Identity DhPair KemPair : Type} {spec : OracleSpec ι}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (sendBudget rawBudget : Nat)
    (receiveBound : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate rawBudget)
    (sendBound : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate sendBudget)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    ((RawCtxGenericBeacon.impl calls decode query).run state).IsQueryBoundP predicate
      (if query.isLeft then sendBudget else rawBudget) := by
  cases phase : state.beacon.phase
  case established control associatedData kernel =>
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, bind_pure_comp, isQueryBoundP_map_iff]
    cases query with
    | inl plaintext => exact owner_send calls predicate sendBudget sendBound _ plaintext _
    | inr raw => exact owner_raw calls predicate rawBudget receiveBound decode raw _
  all_goals simp only [RawCtxGenericBeacon.impl, StateT.run, phase]
  all_goals trivial

/-- The full finite family charges the selected actual role program and original public service under every possible reply. -/
theorem family_step {ι Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat)
    (receiveBound : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate (weight .raw))
    (sendBound : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate (weight .send))
    (publicBound : ∀ query, (publicCalls query).IsQueryBoundP predicate (weight (sourceKind (.inr query))))
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((RawCtxGenericFamilyFrontend.impl calls publicCalls senderId route decode query).run state).IsQueryBoundP predicate
      (weight (RawCtxProtocolBudgets.sourceKind query)) := by
  rcases query with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (hash | hkdf)))
  all_goals simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp,
    isQueryBoundP_map_iff, RawCtxProtocolBudgets.sourceKind]
  case inl.inl => exact server_send calls predicate _ sendBound senderId send.1 send.2 (state.1 index)
  case inl.inr => exact server_raw calls predicate _ receiveBound route decode raw (state.1 index)
  case inr.inl.inl => exact beacon_step calls predicate _ _ receiveBound sendBound decode (.inl send) (state.2 index)
  case inr.inl.inr => exact beacon_step calls predicate _ _ receiveBound sendBound decode (.inr raw) (state.2 index)
  case inr.inr.inl => exact publicBound (.inl coin)
  case inr.inr.inr.inl => exact publicBound (.inr (.inl hash))
  case inr.inr.inr.inr => exact publicBound (.inr (.inr hkdf))

/-- Original aggregate source budgets accumulate the concrete family step costs with no session-count multiplier. -/
theorem family_schedule {ι Kernel Metadata PeerMetadata Identity DhPair KemPair Result : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat)
    (receiveBound : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate (weight .raw))
    (sendBound : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate (weight .send))
    (publicBound : ∀ query, (publicCalls query).IsQueryBoundP predicate (weight (sourceKind (.inr query))))
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec serverCount beaconCount) Result)
    (budget : Budget) (bounded : RawCtxProtocolBudgets.Bounded client budget)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((simulateQ (RawCtxGenericFamilyFrontend.impl calls publicCalls senderId route decode) client).run state).IsQueryBoundP predicate
      (bill weight budget) :=
  RawCtxProtocolBudgets.weighted_bound _ predicate weight client budget bounded
    (family_step calls publicCalls predicate weight receiveBound sendBound publicBound senderId route decode) state

/-- Actual family reads add their own callback cost while retaining original optional replies, roles and history. -/
theorem live_step {ι Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel serverCount beaconCount) (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat) (readCost : Nat)
    (receiveBound : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate (weight .raw))
    (sendBound : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate (weight .send))
    (publicBound : ∀ query, (publicCalls query).IsQueryBoundP predicate (weight (sourceKind (.inr query))))
    (readBound : ∀ input, (reader input).IsQueryBoundP predicate readCost)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((RawCtxGenericFamilyLive.impl calls publicCalls reader senderId route decode query).run state).IsQueryBoundP predicate
      (RawCtxRevealBudgets.weight weight readCost query) := by
  cases query with
  | inl request =>
      simpa only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight] using
        family_step calls publicCalls predicate weight receiveBound sendBound publicBound senderId route decode request state.1
  | inr request =>
      simpa only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight] using readBound _

/-- The full original family/public/read schedule consumes its own source budget through every possible callback continuation. -/
theorem live_schedule {ι Kernel Metadata PeerMetadata Identity DhPair KemPair Result : Type} {spec : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp spec))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel serverCount beaconCount) (OracleComp spec))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat) (readCost : Nat)
    (receiveBound : ∀ entry target context, (calls.receive entry target context).IsQueryBoundP predicate (weight .raw))
    (sendBound : ∀ entry context, (calls.send entry context).IsQueryBoundP predicate (weight .send))
    (publicBound : ∀ query, (publicCalls query).IsQueryBoundP predicate (weight (sourceKind (.inr query))))
    (readBound : ∀ input, (reader input).IsQueryBoundP predicate readCost)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader senderId route decode) client).run state).IsQueryBoundP predicate
      (RawCtxRevealBudgets.bill weight readCost budget) :=
  RawCtxRevealBudgets.weighted_bound _ predicate weight readCost client budget bounded
    (live_step calls publicCalls reader predicate weight readCost receiveBound sendBound publicBound readBound senderId route decode) state

end BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.owner_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.owner_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.owner_send' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.owner_send

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.server_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.server_send

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.beacon_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.family_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.family_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.family_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.family_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.live_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.live_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.live_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets.live_schedule
