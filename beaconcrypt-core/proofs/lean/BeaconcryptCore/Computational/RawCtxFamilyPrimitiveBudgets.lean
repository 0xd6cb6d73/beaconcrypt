import BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets
import BeaconcryptCore.Computational.RawCtxFamilyReadCompiler
import BeaconcryptCore.Computational.RawCtxFamilySourceFreshness

/-!
The actual slot receive/send programs and literal original finite-family/read compiler supply seven separate primitive-interface caps: private KDF S+51R, sealing S, opening R, caller coins U, public commitment H, real public HKDF K and reads E. Every possible typed reply, rejection and selected role is retained. Public HKDF calls and reads never become private KDF calls, and no callback budget is assumed at the final source theorem.

Opening and sealing interface calls contain their actual inner commitment/AEAD/writer work; their shared hash uniform costs are accounted by the consuming interpreter ledger. This module counts source primitive interfaces and does not declare inner or deterministic local work free. It does not bound an arbitrary stopped context merely from its type: reached original outside-client budget provenance and pending completion costs remain separate consuming statements. No cryptographic or freshness premise is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets
open RawCtxSelectedChain RawCtxSelectedAliasPrimitives RawCtxServerServiceBounds

inductive Class where
  | kdf | seal | open | coin | hash | hkdf | read
  deriving DecidableEq

def primitiveClass : Spec.Domain → Class
  | .inl (.inl _) | .inr (.inl (.inl _)) => .kdf
  | .inl (.inr _) => .open
  | .inr (.inl (.inr _)) => .seal
  | .inr (.inr (.inl _)) => .coin
  | .inr (.inr (.inr (.inl _))) => .hash
  | .inr (.inr (.inr (.inr _))) => .hkdf

def liveClass : RawCtxSelectedLiveCompiler.Spec.Domain → Class
  | .inl query => primitiveClass query
  | .inr _ => .read

def receiveCost : Class → Nat
  | .kdf => 51
  | .open => 1
  | _ => 0

def sendCost : Class → Nat
  | .kdf | .seal => 1
  | _ => 0

def weight (selected : Class) : Kind → Nat
  | .send => sendCost selected
  | .raw => receiveCost selected
  | .coin => if selected = .coin then 1 else 0
  | .hash => if selected = .hash then 1 else 0
  | .hkdf => if selected = .hkdf then 1 else 0

/-- The original generic receive syntax retains its KDF and opening reservations through the actual alias primitive compiler. -/
theorem receive_calls (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (selected : Class) :
    (RawCtxSelectedAliasCompiler.calls.receive entry target context).IsQueryBoundP
      (fun query => primitiveClass query = selected) (receiveCost selected) := by
  cases selected
  case kdf =>
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.receiveForward
      (fun query => query.isLeft = true) _ _ 51 (RawCtxChainReceiveBounds.receive_bound entry target context)
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  case «open» =>
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.receiveForward
      (fun query => query.isRight = true) _ _ 1 (RawCtxChainReceiveBounds.program_open_bound _)
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  all_goals
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.receiveForward
      (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  all_goals intro query
  all_goals cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])

/-- The original send syntax retains one KDF and one sealing callback, including optional sealing failure. -/
theorem send_calls (entry : Kernel) (context : RawCtxSourceSend.SealContext) (selected : Class) :
    (RawCtxSelectedAliasCompiler.calls.send entry context).IsQueryBoundP
      (fun query => primitiveClass query = selected) (sendCost selected) := by
  cases selected
  case kdf =>
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.sendForward
      (fun query => query.isLeft = true) _ _ 1 (RawCtxChainSend.program_kdf_bound _)
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  case «seal» =>
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.sendForward
      (fun query => query.isRight = true) _ _ 1 (RawCtxChainSend.program_seal_bound _)
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  all_goals
    apply RawCtxSourceOpen.simulate_bound RawCtxSelectedAliasCompiler.sendForward
      (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  all_goals intro query
  all_goals cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])

/-- Every original public service makes exactly its own primitive-class request, including real HKDF evaluation. -/
theorem public_calls (query : RawCtxServerServices.PublicSpec.Domain) (selected : Class) :
    (RawCtxSelectedAliasCompiler.publicForward query).IsQueryBoundP
      (fun query => primitiveClass query = selected) (weight selected (sourceKind (.inr query))) := by
  apply (isQueryBoundP_query_iff _ _ _).mpr
  rcases query with coin | (hash | hkdf)
  all_goals cases selected <;> simp [primitiveClass, weight, sourceKind]

/-- Forwarding a complete primitive program into the live interface preserves every original primitive-class query. -/
theorem primitive_forward {Result : Type} (client : OracleComp Spec Result) (selected : Class) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => primitiveClass query = selected) budget) :
    (simulateQ RawCtxSelectedLiveCompiler.primitiveForward client).IsQueryBoundP
      (fun query => liveClass query = selected) budget := by
  refine RawCtxSourceOpen.simulate_bound RawCtxSelectedLiveCompiler.primitiveForward
    (fun query => primitiveClass query = selected) (fun query => liveClass query = selected)
    client budget bounded ?_
  intro query
  apply (isQueryBoundP_query_iff _ _ _).mpr
  intro chosen
  change primitiveClass query = selected at chosen
  simp [chosen]

/-- The exact family read compiler charges only a read attempt and never a record/public primitive class. -/
theorem read_calls {serverCount beaconCount : Nat}
    (input : RawCtxFamilyReadCompiler.Input serverCount beaconCount) (selected : Class) :
    (RawCtxFamilyReadCompiler.compiler input).IsQueryBoundP
      (fun query => liveClass query = selected) (if selected = .read then 1 else 0) := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel
  all_goals first | trivial | skip
  all_goals apply (isQueryBoundP_query_iff _ _ _).mpr
  all_goals cases selected <;> simp [liveClass]

/-- The literal original family/read compiler supplies every concrete primitive-class step bound. -/
theorem source_step {Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : Class) :
    ((RawCtxFamilySourceFreshness.compiler RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward
      senderId route decode query).run state).IsQueryBoundP (fun query => liveClass query = selected)
      (RawCtxRevealBudgets.weight (weight selected) (if selected = .read then 1 else 0) query) := by
  cases query with
  | inl request =>
      simp only [RawCtxFamilySourceFreshness.compiler, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight]
      exact primitive_forward _ selected _
        (RawCtxGenericFamilyBudgets.family_step RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward
          (fun query => primitiveClass query = selected) (weight selected)
          (fun entry target context => receive_calls entry target context selected)
          (fun entry context => send_calls entry context selected)
          (fun query => public_calls query selected) senderId route decode request state.1)
  | inr request =>
      simpa only [RawCtxFamilySourceFreshness.compiler, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight] using read_calls
          (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1) selected

def sourceCost (selected : Class) (budget : RawCtxRevealBudgets.Budget) : Nat :=
  match selected with
  | .kdf => budget.1 .send + 51 * budget.1 .raw
  | .seal => budget.1 .send
  | .open => budget.1 .raw
  | .coin => budget.1 .coin
  | .hash => budget.1 .hash
  | .hkdf => budget.1 .hkdf
  | .read => budget.2

/-- The original adaptive family source supplies KDF S+51R, seal S, open R, caller coins U, public hashes H, real public HKDF K and reads E. -/
theorem source_class {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : Class) :
    ((simulateQ (RawCtxFamilySourceFreshness.compiler RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward
      senderId route decode) client).run state).IsQueryBoundP (fun query => liveClass query = selected)
      (sourceCost selected budget) := by
  have cap := RawCtxRevealBudgets.weighted_bound
    (RawCtxFamilySourceFreshness.compiler RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward senderId route decode)
    (fun query => liveClass query = selected) (weight selected) (if selected = .read then 1 else 0)
    client budget bounded (fun query state => source_step senderId route decode query state selected) state
  have enumeration : (Finset.univ : Finset Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  cases selected <;> simpa [sourceCost, RawCtxRevealBudgets.bill, RawCtxServerServiceBounds.bill,
    enumeration, weight, sendCost, receiveCost] using cap

end BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.receive_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.receive_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.send_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.send_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.public_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.public_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.primitive_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.primitive_forward

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.read_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.read_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.source_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets.source_class
