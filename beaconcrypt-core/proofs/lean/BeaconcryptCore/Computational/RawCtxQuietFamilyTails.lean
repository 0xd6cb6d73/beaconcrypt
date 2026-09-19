import BeaconcryptCore.Computational.RawCtxQuietServerTails

/-!
The actual singleton family operation derives zero-query captured source continuations at every inner owner, Server and family layer. Every indexed role, Beacon phase, public request and exact publication installer is retained. These source-derived resource witnesses add no cryptographic or freshness premise; the pending material-only completion and the original outside LIVE client still require their separate explicit budgets.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxQuietFamilyTails
open RawCtxPendingFamilyTails RawCtxPendingOwnerQueries RawCtxQueryOccurrence RawCtxSelectedFamilyContext

variable {M P I D K Result : Type} {S B : Nat}

def Quiet : FamilyContext M P I D K Result S B → Prop
  | .server _ _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound 0) ∧ RawCtxQuietServerTails.Quiet inner
  | .beacon _ _ _ _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound 0) ∧ RawCtxQuietOwnerTails.Quiet inner

def QuietTail (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B)) : Prop :=
  ∃ context : FamilyContext M P I D K Result S B,
    (⟨query, next⟩ : FamilyFrame M P I D K Result S B) = familyFrame sender route decode context ∧ Quiet context

private theorem no_occurrence
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) Result) (bounded : client.IsTotalQueryBound 0)
    (state : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B))
    (occurs : Occurs query next (program sender route decode client state)) : False := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  exact pure_impossible query next (value, state) occurs

/-- The actual singleton Server call retains quiet captured owner, Server and family continuations through its exact indexed installer. -/
theorem server_tail
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxServerMixed.SourceSpec.Domain)
    (before : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B) (index : Fin S)
    (outside : RawCtxServerMixed.SourceSpec.Range request → OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B))
    (occurs : Occurs query next (liftServer sender route decode before index outside
      (RawCtxPendingServerTails.program sender route decode (RawCtxServerMixed.SourceSpec.query request) (before.1 index))))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    obtain ⟨context, frame, quietContext⟩ := RawCtxQuietServerTails.single_tail sender route decode request
      (before.1 index) query inner innerOccurs selected
    refine ⟨.server request before index outside context, ?_, quiet, quietContext⟩
    exact congrArg (fun saved : ServerFrame M P (RawCtxServerMixed.SourceSpec.Range request) =>
      (⟨saved.1, fun reply => liftServer sender route decode before index outside (saved.2 reply)⟩ :
        FamilyFrame M P I D K Result S B)) frame
  · rcases continued with ⟨result, later⟩
    exact (no_occurrence sender route decode _ (quiet result.1) _ query next later).elim

/-- The actual singleton Beacon call retains quiet owner and family continuations through its original phase installer. -/
theorem beacon_tail
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B) (index : Fin B)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize) (kernel : Kernel RatchetChain)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B))
    (occurs : Occurs query next (liftBeacon sender route decode before index control associatedData outside
      (RawCtxPendingOwnerTails.program (before.2 index).beacon.identityKeyId decode
        (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
        (RawCtxGenericBeacon.selected (before.2 index) control associatedData kernel))))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    obtain ⟨context, frame, quietContext⟩ := RawCtxQuietOwnerTails.single_tail (before.2 index).beacon.identityKeyId decode
      (.inl request) (RawCtxGenericBeacon.selected (before.2 index) control associatedData kernel) query inner innerOccurs selected
    refine ⟨.beacon request before index control associatedData outside context, ?_, quiet, quietContext⟩
    exact congrArg (fun saved : OwnerFrame Unit (RawCtxMixedOwner.SourceSpec.Range request) =>
      (⟨saved.1, fun reply => liftBeacon sender route decode before index control associatedData outside (saved.2 reply)⟩ :
        FamilyFrame M P I D K Result S B)) frame
  · rcases continued with ⟨result, later⟩
    exact (no_occurrence sender route decode _ (quiet result.1) _ query next later).elim

/-- Every selected query in one original family operation inherits zero-query evidence for all inner captured source continuations. -/
theorem step_tail
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxPendingFamilyTails.SourceSpec S B).Domain)
    (outside : (RawCtxPendingFamilyTails.SourceSpec S B).Range request → OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (state : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B))
    (occurs : Occurs query next (program sender route decode
      (((RawCtxPendingFamilyTails.SourceSpec S B).query request : OracleComp (RawCtxPendingFamilyTails.SourceSpec S B) _) >>= outside) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
  · rw [server_selected sender route decode request index outside state] at occurs
    exact server_tail sender route decode request state index outside quiet query next occurs selected
  · cases active : (state.2 index).beacon.phase
    case established control associatedData kernel =>
      rw [beacon_selected sender route decode request index control associatedData kernel outside state active] at occurs
      exact beacon_tail sender route decode request state index control associatedData kernel outside quiet query next occurs selected
    all_goals
      rw [program_query sender route decode (.inr (.inl ⟨index, request⟩)) outside state] at occurs
      simp only [StateT.run, RawCtxGenericFamilyFrontend.impl, RawCtxGenericBeacon.impl, active, pure_bind] at occurs
      exact (no_occurrence sender route decode _ (quiet _) _ query next occurs).elim
  · rw [program_query sender route decode (.inr (.inr publicQuery)) outside state] at occurs
    simp only [StateT.run, RawCtxGenericFamilyFrontend.impl, publicForward, bind_assoc, pure_bind] at occurs
    rcases query_cases query (.inr (.inr publicQuery)) next _ occurs with current | following
    · have same : query = .inr (.inr publicQuery) := congrArg Sigma.fst current
      subst query
      simp only [RawCtxPendingMixedPrefix.ownerSelected, Bool.false_eq_true] at selected
    · rcases following with ⟨reply, continued⟩
      exact (no_occurrence sender route decode _ (quiet reply) _ query next continued).elim

/-- The actual single family query supplies all inner zero-call continuations without an external callback budget. -/
theorem single_tail
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxPendingFamilyTails.SourceSpec S B).Domain)
    (state : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      ((RawCtxPendingFamilyTails.SourceSpec S B).Range request × RawCtxPendingFamilyTails.State RatchetChain M P I D K S B))
    (occurs : Occurs query next (program sender route decode ((RawCtxPendingFamilyTails.SourceSpec S B).query request) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  exact step_tail sender route decode request pure (fun _ => trivial) state query next occurs selected

end BeaconcryptCore.Computational.RawCtxQuietFamilyTails

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietFamilyTails.server_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietFamilyTails.server_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietFamilyTails.beacon_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietFamilyTails.beacon_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietFamilyTails.step_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietFamilyTails.step_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietFamilyTails.single_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietFamilyTails.single_tail
