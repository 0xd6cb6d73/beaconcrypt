import BeaconcryptCore.Computational.RawCtxPendingReceiveQueries
import BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler

/-!
Private full pending receive/send requests factor the existing mixed owner compiler. Public queries, raw admission, optional replies, failed-send advancement and the complete owner state retain their original interfaces. Erasure removes only the added private pending context; it neither changes KDF inputs nor samples new values. The generic chain payload specializes to actual native chains or selected private labels.

These are operational equalities, not input secrecy or freshness assumptions. They support selecting the original adaptive KDF callback before its reply, with all pending state available to the private reduction. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingOwnerQueries

abbrev Kernel (Chain : Type) := RefinedRatchet Chain Chain RatchetMaterial
abbrev ReceiveSpec (Chain : Type) := RawCtxPendingReceiveQueries.Spec Chain Chain RatchetMaterial
  RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted
abbrev SendSpec (Chain : Type) :=
  (RawCtxChainSend.Kdf Chain Chain RatchetMaterial RawCtxSourceSend.SealContext →ₒ (Chain × RatchetMaterial)) +
  (RawCtxChainSend.Seal Chain Chain RatchetMaterial RawCtxSourceSend.SealContext →ₒ Option RawCtxSourceSend.Encrypted)
abbrev Spec (Chain : Type) := ReceiveSpec Chain + (SendSpec Chain + RawCtxServerServices.PublicSpec)
abbrev OriginalSpec (Chain : Type) :=
  RawCtxChainReceive.ReceiveSpec Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted +
  (RawCtxChainSend.SendSpec Chain Chain RatchetMaterial RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted +
    RawCtxServerServices.PublicSpec)

def receiveForward {Chain : Type} : QueryImpl (ReceiveSpec Chain) (OracleComp (Spec Chain)) :=
  fun query => (Spec Chain).query (.inl query)
def sendForward {Chain : Type} : QueryImpl (SendSpec Chain) (OracleComp (Spec Chain)) :=
  fun query => (Spec Chain).query (.inr (.inl query))
def publicForward {Chain : Type} : QueryImpl RawCtxServerServices.PublicSpec (OracleComp (Spec Chain)) :=
  fun query => (Spec Chain).query (.inr (.inr query))

noncomputable def sendProgram {Chain : Type}
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    OracleComp (SendSpec Chain) (Kernel Chain × Option RawCtxSourceSend.Encrypted) :=
  match start with
  | .exhausted entry _ => pure (entry, none)
  | .requested pending => do
      let reply ← (SendSpec Chain).query (.inl pending)
      let ready := RawCtxChainSend.ready pending reply
      let sealed ← (SendSpec Chain).query (.inr ready)
      pure (ready.advanced, sealed)

noncomputable def calls {Chain : Type} : RawCtxChainOwner.Calls (Kernel Chain) (OracleComp (Spec Chain)) :=
  { receive := fun entry target context => simulateQ receiveForward
      (RawCtxPendingReceiveQueries.program (RawCtxChainReceive.normalBegin entry target context))
    send := fun entry context => simulateQ sendForward
      (sendProgram (RawCtxChainSend.normalBegin entry context)) }

noncomputable def compiler {Chain Metadata : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxSelectedPublicTrace.SourceSpec (StateT (RawCtxChainOwner.State (Kernel Chain) Metadata) (OracleComp (Spec Chain)))
  | .inl request => RawCtxChainOwner.ownerImpl calls sender decode request
  | .inr request => fun state => do
      let reply ← publicForward request
      pure (reply, state)

def erase {Chain : Type} : QueryImpl (Spec Chain) (OracleComp (OriginalSpec Chain))
  | .inl (.inl pending) => (OriginalSpec Chain).query (.inl (.inl pending.request))
  | .inl (.inr pending) => (OriginalSpec Chain).query (.inl (.inr pending))
  | .inr (.inl (.inl pending)) => (OriginalSpec Chain).query (.inr (.inl (.inl pending.request)))
  | .inr (.inl (.inr pending)) => (OriginalSpec Chain).query (.inr (.inl (.inr pending)))
  | .inr (.inr request) => (OriginalSpec Chain).query (.inr (.inr request))

def originalReceive {Chain : Type} : QueryImpl
    (RawCtxChainReceive.ReceiveSpec Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
    (OracleComp (OriginalSpec Chain)) := fun query => (OriginalSpec Chain).query (.inl query)
def originalSend {Chain : Type} : QueryImpl
    (RawCtxChainSend.SendSpec Chain Chain RatchetMaterial RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
    (OracleComp (OriginalSpec Chain)) := fun query => (OriginalSpec Chain).query (.inr (.inl query))
def originalPublic {Chain : Type} : QueryImpl RawCtxServerServices.PublicSpec (OracleComp (OriginalSpec Chain)) :=
  fun query => (OriginalSpec Chain).query (.inr (.inr query))

noncomputable def originalCalls {Chain : Type} : RawCtxChainOwner.Calls (Kernel Chain) (OracleComp (OriginalSpec Chain)) :=
  { receive := fun entry target context => simulateQ originalReceive (RawCtxChainReceive.execute entry target context)
    send := fun entry context => simulateQ originalSend (RawCtxChainSend.execute entry context) }

noncomputable def originalCompiler {Chain Metadata : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxSelectedPublicTrace.SourceSpec (StateT (RawCtxChainOwner.State (Kernel Chain) Metadata) (OracleComp (OriginalSpec Chain)))
  | .inl request => RawCtxChainOwner.ownerImpl originalCalls sender decode request
  | .inr request => fun state => do
      let reply ← originalPublic request
      pure (reply, state)

/-- Erasure retains the exact original receive request and its full possible reply interface. -/
theorem receive_erase {Chain : Type} :
    (erase (Chain := Chain)) ∘ₛ receiveForward = originalReceive ∘ₛ RawCtxPendingReceiveQueries.forward := by
  funext query
  cases query <;> simp [QueryImpl.compose, receiveForward, erase,
    RawCtxPendingReceiveQueries.forward, originalReceive, OracleSpec.query]

/-- The pending send query preserves the exact original input and advanced sealing tail. -/
theorem send_erase {Chain : Type}
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    simulateQ (erase ∘ₛ sendForward) (sendProgram start) =
      simulateQ originalSend (RawCtxChainSend.program start) := by
  cases start <;> simp [sendProgram, RawCtxChainSend.program, QueryImpl.compose,
    sendForward, erase, originalSend, OracleSpec.query]

/-- Full receive admission and every skip/open continuation survive pending erasure. -/
theorem receive_call {Chain : Type} (entry : Kernel Chain) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    simulateQ erase (calls.receive entry target context) = originalCalls.receive entry target context := by
  change simulateQ erase (simulateQ receiveForward _) = simulateQ originalReceive _
  rw [← QueryImpl.simulateQ_compose, receive_erase, QueryImpl.simulateQ_compose,
    RawCtxPendingReceiveQueries.program_forward]
  rfl

/-- Full send admission retains the original exhaustion, advancement and optional sealing reply. -/
theorem send_call {Chain : Type} (entry : Kernel Chain) (context : RawCtxSourceSend.SealContext) :
    simulateQ erase (calls.send entry context) = originalCalls.send entry context := by
  exact (QueryImpl.simulateQ_compose erase sendForward _).symm.trans (send_erase _)

/-- Every original public or owner operation erases to the unchanged complete stateful source step. -/
theorem step_erase {Chain Metadata : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain) (state : RawCtxChainOwner.State (Kernel Chain) Metadata) :
    simulateQ erase ((compiler sender decode query).run state) =
      (originalCompiler sender decode query).run state := by
  rcases query with (send | raw) | request
  · simp only [compiler, originalCompiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run]
    by_cases empty : send.isEmpty = true
    · simp only [empty, if_true]
      exact simulateQ_pure _ _
    · simp only [empty, Bool.false_eq_true, if_false, bind_pure_comp]
      refine (simulateQ_map _ _ _).trans ?_
      rw [send_call]
  · simp only [compiler, originalCompiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run]
    by_cases empty : raw.isEmpty = true
    · simp only [empty, if_true]
      exact simulateQ_pure _ _
    · simp only [empty, Bool.false_eq_true, if_false]
      cases decoded : decode raw with
      | none => exact simulateQ_pure _ _
      | some frame =>
          by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
          · simp only [valid, if_true, bind_pure_comp]
            refine (simulateQ_map _ _ _).trans ?_
            rw [receive_call]
          · simp only [valid, if_false]
            exact simulateQ_pure _ _
  · simp [compiler, originalCompiler, StateT.run, publicForward, originalPublic, erase, OracleSpec.query]

/-- Erasure commutes with every finite adaptive mixed schedule before any owner or reply projection. -/
theorem schedule_erase {Chain Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxChainOwner.State (Kernel Chain) Metadata) :
    simulateQ erase ((simulateQ (compiler sender decode) client).run state) =
      (simulateQ (originalCompiler sender decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact congrArg (fun impl : QueryImpl RawCtxSelectedPublicTrace.SourceSpec
    (StateT (RawCtxChainOwner.State (Kernel Chain) Metadata) (OracleComp (OriginalSpec Chain))) =>
      (simulateQ impl client).run state)
    (funext fun query => funext fun owner => step_erase sender decode query owner)

/-- The selected-label specialization is precisely the existing common source compiler. -/
theorem selected_schedule {Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (state : RawCtxChainOwner.State RawCtxSelectedChain.Kernel Metadata) :
    simulateQ erase ((simulateQ (compiler sender decode) client).run state) =
      (simulateQ (RawCtxSelectedAliasCompiler.compiler sender decode) client).run state :=
  schedule_erase sender decode client state

def originalQuery {Chain : Type} : (Spec Chain).Domain → (OriginalSpec Chain).Domain
  | .inl (.inl pending) => .inl (.inl pending.request)
  | .inl (.inr pending) => .inl (.inr pending)
  | .inr (.inl (.inl pending)) => .inr (.inl (.inl pending.request))
  | .inr (.inl (.inr pending)) => .inr (.inl (.inr pending))
  | .inr (.inr request) => .inr (.inr request)

set_option backward.isDefEq.respectTransparency false in
/-- Every all-reply query-class bound is preserved on literal programs, including repeated private and public calls. -/
theorem query_bound_iff {Chain Result : Type} (client : OracleComp (Spec Chain) Result)
    (predicate : (OriginalSpec Chain).Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (simulateQ erase client).IsQueryBoundP predicate budget ↔
      client.IsQueryBoundP (fun query => predicate (originalQuery query)) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      rcases query with (pending | opening) | ((pending | sealing) | externalRequest)
      all_goals simp only [simulateQ_bind, simulateQ_spec_query, erase,
        isQueryBoundP_query_bind_iff, originalQuery, ih]
      all_goals rfl

end BeaconcryptCore.Computational.RawCtxPendingOwnerQueries

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.receive_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.receive_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.send_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.send_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.receive_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.receive_call

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.send_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.send_call

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.step_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.step_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.schedule_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.schedule_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.selected_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.selected_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.query_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerQueries.query_bound_iff
