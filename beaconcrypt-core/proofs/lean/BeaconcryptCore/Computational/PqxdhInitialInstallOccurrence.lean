import BeaconcryptCore.Computational.PqxdhInitialFinishReceipt
import BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt

/-!
Successful local installations receive separate owner/attempt tokens. The attempt counter advances before every attempted finish, including inactive and failed attempts. Source receipts keep the literal initial kernels privately; erasure retains the existing coordinate-origin trace and all protocol operations. Preexisting roles are not labelled merely because the new annotation starts empty.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence
open PqxdhInitialPendingPost RawCtxProtocolReveals
variable {ι Chain M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

structure Token (S B : Nat) where
  owner : Owner S B
  attempt : Nat
  deriving DecidableEq

inductive Evidence (Chain Response Shared : Type) where
  | beacon (raw : Pqxdh.Bytes) (receipt : PqxdhInitialFinishReceipt.Receipt (KernelOf Chain) Response Shared)
  | server (ready : PqxdhPrivateAcceptedRoot.Ready) (receipt : PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))

def initialKernel : Evidence Chain Response Shared → KernelOf Chain
  | .beacon _ receipt => receipt.initial
  | .server _ receipt => receipt.initial

structure Occurrence (Chain Response Shared : Type) (S B : Nat) where
  token : Token S B
  evidence : Evidence Chain Response Shared

structure Trace (Chain Response Shared : Type) (S B : Nat) where
  nextAttempt : Nat
  installed : Owner S B → Option (Occurrence Chain Response Shared S B)
  receipts : List (Occurrence Chain Response Shared S B)

def empty : Trace Chain Response Shared S B := ⟨0, fun _ => none, []⟩

def begin (before : Trace Chain Response Shared S B) : Trace Chain Response Shared S B :=
  { before with nextAttempt := before.nextAttempt + 1 }

def note (before : Trace Chain Response Shared S B) (owner : Owner S B) (attempt : Nat)
    (evidence : Evidence Chain Response Shared) (published : Bool) : Trace Chain Response Shared S B :=
  let receipt : Occurrence Chain Response Shared S B := ⟨⟨owner, attempt⟩, evidence⟩
  { before with
    installed := if published then Function.update before.installed owner (some receipt) else before.installed
    receipts := before.receipts ++ [receipt] }

def finished (started : Trace Chain Response Shared S B) (attempt : Nat) (index : Fin B) (raw : Pqxdh.Bytes)
    (receipt : Option (PqxdhInitialFinishReceipt.Receipt (KernelOf Chain) Response Shared)) (published : Bool) :
    Trace Chain Response Shared S B :=
  match receipt with
  | none => started
  | some receipt => note started (.beacon index) attempt (.beacon raw receipt) published

abbrev State (Chain M P I D K Response Shared Origin : Type) (S B : Nat) :=
  (Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) × Trace Chain Response Shared S B

noncomputable def compiler (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (StateT (State Chain M P I D K Response Shared Origin S B)
        (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B)))
  | .inr (.finish index raw) => fun before => do
      let attempt := before.2.nextAttempt
      let started := begin before.2
      let result ← PqxdhInitialFinishReceipt.owner mark preForward calls applicationForward initialForward decode raw
        (before.1.1.roles.1.2 index)
      pure (result.1.1.1,
        ((install index before.1.1 result.1.1.2, PqxdhInitialOriginPost.finish before.1.2 index result.1.2),
          finished started attempt index raw result.2 result.1.1.1.isSome))
  | query => fun before =>
      (fun result => (result.1, (result.2, before.2))) <$>
        (PqxdhInitialOriginPost.compiler mark sender route decode query).run before.1

def built (started : Trace Chain Response Shared S B) (attempt : Nat)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (index : Fin S) (front : Front Chain M P I D K S B)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (receipt : Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))) : Trace Chain Response Shared S B :=
  match receipt with
  | none => started
  | some receipt =>
      let published := match reply with
        | .ok (some response) => decide (response.keyId = receipt.candidate.key_id) &&
            ((front.roles.1.1 index).server.peers response.keyId).isSome
        | _ => false
      note started (.server index receipt.candidate.key_id) attempt (.server ready receipt) published

noncomputable def sequence (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) :
    StateT (State Chain M P I D K Response Shared Origin S B)
      (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B)) Result := fun before => do
  let attempt := before.2.nextAttempt
  let started := begin before.2
  let result ← (PqxdhInitialBuilderReceipt.build source initial sender index metadata ready).run before.1.1
  (simulateQ (compiler mark sender route decode) (post result.1.1)).run
    ((result.2, PqxdhInitialOriginPost.afterBuilder before.1.2 result.2 index origin result.1.1),
      built started attempt ready index result.2 result.1.1 result.1.2)

/-- Erasing only occurrence evidence recovers the exact existing origin-marked source query, retaining its complete native frontend and Boolean coordinate marker. -/
theorem step_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : State Chain M P I D K Response Shared Origin S B) :
    Prod.map id Prod.fst <$>
      (compiler (X := X) mark sender route decode query).run before =
      (PqxdhInitialOriginPost.compiler mark sender route decode query).run before.1 := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [compiler, StateT.run, Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, id_map']
  · simp only [compiler, StateT.run, Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, id_map']
  · simp only [compiler, PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, Functor.map_map]
    rw [← PqxdhInitialFinishReceipt.owner_erase]
    simp only [Functor.map_map]
    rfl

/-- The complete adaptive source Post program keeps every original reply, frontend field and coordinate-origin event when only the private occurrence trace is erased. -/
theorem program_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : State Chain M P I D K Response Shared Origin S B) :
    Prod.map id Prod.fst <$>
      (simulateQ (compiler (X := X) mark sender route decode) client).run before =
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run before.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (step_erase mark sender route decode) client before

/-- The actual first Server builder, complete reinstallation and entire original Post schedule preserve their source programs when only occurrence evidence is erased. -/
theorem sequence_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : State Chain M P I D K Response Shared Origin S B) :
    Prod.map id Prod.fst <$>
      (sequence (X := X) source initial mark origin sender route decode index metadata ready post).run before =
      (PqxdhInitialOriginPost.sequence source initial mark origin sender route decode index metadata ready post).run before.1 := by
  simp only [sequence, PqxdhInitialOriginPost.sequence, StateT.run, map_bind]
  have erased := PqxdhInitialBuilderReceipt.build_erase (extra := extra) (X := X)
    (SourceResponse := Response) (Shared := Shared) source initial sender index metadata ready before.1.1
  simp only [StateT.run] at erased
  rw [← erased]
  simp only [bind_map_left, Prod.map_def, id_eq]
  apply bind_congr
  intro result
  exact program_erase mark sender route decode (post result.1.1) _

def attemptCost : (PqxdhInitialGenericPost.Spec extra S B).Domain → Nat
  | .inr (.finish _ _) => 1
  | _ => 0

private theorem finished_count (started : Trace Chain Response Shared S B) (attempt : Nat)
    (index : Fin B) (raw : Pqxdh.Bytes)
    (receipt : Option (PqxdhInitialFinishReceipt.Receipt (KernelOf Chain) Response Shared)) (published : Bool) :
    (finished started attempt index raw receipt published).nextAttempt = started.nextAttempt := by
  cases receipt <;> rfl

/-- Each original attempted finish consumes one ordinal even on failure or an inactive phase; original record, public, reveal and selector requests consume none. -/
theorem step_attempts (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : State Chain M P I D K Response Shared Origin S B)
    (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support ((compiler (X := X) mark sender route decode query).run before)) :
    result.2.2.nextAttempt = before.2.nextAttempt + attemptCost query := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [compiler, StateT.run, support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    rfl
  · simp only [compiler, StateT.run, support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    rfl
  · simp only [compiler, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨original, _, final⟩ := supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ final
    exact finished_count (begin before.2) before.2.nextAttempt index raw original.2 original.1.1.1.isSome

/-- The same bounded adaptive source schedule advances its private ordinal monotonically and by at most its original Post-query allowance. No failed attempt is omitted from this accounting. -/
theorem program_attempts (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget)
    (before : State Chain M P I D K Response Shared Origin S B)
    (result : Result × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support ((simulateQ (compiler (X := X) mark sender route decode) client).run before)) :
    before.2.nextAttempt ≤ result.2.2.nextAttempt ∧
      result.2.2.nextAttempt ≤ before.2.nextAttempt + budget := by
  induction client using OracleComp.inductionOn generalizing budget before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | query_bind query outside ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨head, first, rest⟩ := supported
      have counted := step_attempts mark sender route decode query before head first
      obtain ⟨lower, upper⟩ := ih head.1 (budget - 1) (bounded.2 head.1) head.2 result rest
      have one : attemptCost query ≤ 1 := by
        rcases query with (request | request) | ⟨index, raw⟩ <;> simp only [attemptCost] <;> omega
      omega

/-- The source history has strictly increasing actual attempt ordinals, all before the next allocation. -/
def Ordered (trace : Trace Chain Response Shared S B) : Prop :=
  trace.receipts.Pairwise (fun first later => first.token.attempt < later.token.attempt) ∧
    ∀ receipt ∈ trace.receipts, receipt.token.attempt < trace.nextAttempt

/-- Empty annotation asserts no ownership or initialization property for any preexisting role. -/
theorem empty_ordered : Ordered (empty : Trace Chain Response Shared S B) := by
  simp [Ordered, empty]

private theorem begin_ordered (before : Trace Chain Response Shared S B) (ordered : Ordered before) :
    Ordered (begin before) := by
  exact ⟨ordered.1, fun receipt member => Nat.lt_succ_of_lt (ordered.2 receipt member)⟩

private theorem note_started (before : Trace Chain Response Shared S B) (ordered : Ordered before)
    (owner : Owner S B) (evidence : Evidence Chain Response Shared) (published : Bool) :
    Ordered (note (begin before) owner before.nextAttempt evidence published) := by
  simp only [Ordered, note, begin, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton, forall_eq, List.mem_append]
  refine ⟨⟨ordered.1, trivial, ordered.2⟩, ?_⟩
  intro receipt member
  rcases member with old | rfl
  · exact Nat.lt_succ_of_lt (ordered.2 receipt old)
  · exact Nat.lt_succ_self _

private theorem finished_ordered (before : Trace Chain Response Shared S B) (ordered : Ordered before)
    (index : Fin B) (raw : Pqxdh.Bytes)
    (receipt : Option (PqxdhInitialFinishReceipt.Receipt (KernelOf Chain) Response Shared)) (published : Bool) :
    Ordered (finished (begin before) before.nextAttempt index raw receipt published) := by
  cases receipt with
  | none => exact begin_ordered before ordered
  | some receipt => exact note_started before ordered _ _ published

/-- Every original source query preserves distinct chronological initializer occurrences, even when a finish fails after initialization. -/
theorem step_ordered (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : State Chain M P I D K Response Shared Origin S B) (ordered : Ordered before.2)
    (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support ((compiler (X := X) mark sender route decode query).run before)) :
    Ordered result.2.2 := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [compiler, StateT.run, support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    exact ordered
  · simp only [compiler, StateT.run, support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    exact ordered
  · simp only [compiler, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨original, _, final⟩ := supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ final
    exact finished_ordered before.2 ordered index raw original.2 original.1.1.1.isSome

/-- The complete adaptive Post retains the actual chronological allocation invariant under every supported source reply. -/
theorem program_ordered (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : State Chain M P I D K Response Shared Origin S B) (ordered : Ordered before.2)
    (result : Result × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support ((simulateQ (compiler (X := X) mark sender route decode) client).run before)) :
    Ordered result.2.2 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ordered
  | query_bind query outside ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨head, first, rest⟩ := supported
      exact ih head.1 head.2 (step_ordered mark sender route decode query before ordered head first) result rest

private theorem built_ordered (before : Trace Chain Response Shared S B) (ordered : Ordered before)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (index : Fin S) (front : Front Chain M P I D K S B)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (receipt : Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))) :
    Ordered (built (begin before) before.nextAttempt ready index front reply receipt) := by
  cases receipt with
  | none => exact begin_ordered before ordered
  | some receipt => exact note_started before ordered _ _ _

/-- Starting the same first Server Builder and complete Post with no occurrence labels yields strictly ordered actual initializer receipts. Existing native roles remain unrestricted. -/
theorem sequence_ordered (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)
    (result : Result × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support
      ((sequence (X := X) source initial mark origin sender route decode index metadata ready post).run (before, empty))) :
    Ordered result.2.2 := by
  simp only [sequence, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨builtResult, _, rest⟩ := supported
  exact program_ordered mark sender route decode _ _
    (built_ordered empty empty_ordered ready index builtResult.2 builtResult.1.1 builtResult.1.2) result rest

private theorem built_count (started : Trace Chain Response Shared S B) (attempt : Nat)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (index : Fin S) (front : Front Chain M P I D K S B)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (receipt : Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))) :
    (built started attempt ready index front reply receipt).nextAttempt = started.nextAttempt := by
  cases receipt <;> rfl

/-- One first Builder plus at most q original Post queries allocates at most 1 + q actual attempt ordinals, including every rejection and failed publication. -/
theorem sequence_attempts (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (budget : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound budget)
    (before : State Chain M P I D K Response Shared Origin S B)
    (result : Result × State Chain M P I D K Response Shared Origin S B)
    (supported : result ∈ support
      ((sequence (X := X) source initial mark origin sender route decode index metadata ready post).run before)) :
    before.2.nextAttempt + 1 ≤ result.2.2.nextAttempt ∧
      result.2.2.nextAttempt ≤ before.2.nextAttempt + 1 + budget := by
  simp only [sequence, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨builtResult, _, rest⟩ := supported
  have counted := program_attempts mark sender route decode _ budget (bounded builtResult.1.1) _ result rest
  simpa only [built_count, begin] using counted

/-- Private occurrence annotations preserve every source oracle-class budget for the full Builder and adaptive Post. No primitive or callback work is removed. -/
theorem sequence_queries (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : State Chain M P I D K Response Shared Origin S B)
    (predicate : (Spec extra Chain I D K X Response Shared S B).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    ((sequence source initial mark origin sender route decode index metadata ready post).run before).IsQueryBoundP predicate budget ↔
      ((PqxdhInitialOriginPost.sequence source initial mark origin sender route decode index metadata ready post).run before.1).IsQueryBoundP predicate budget := by
  rw [← sequence_erase, isQueryBoundP_map_iff]

/-- Chronologically distinct initializer occurrences have distinct owner/attempt tokens even when all their secret and transcript bytes coincide. -/
theorem distinct_tokens (trace : Trace Chain Response Shared S B) (ordered : Ordered trace) :
    trace.receipts.Pairwise (fun first later => first.token ≠ later.token) := by
  apply ordered.1.imp
  intro first later increasing same
  have equal := congrArg Token.attempt same
  omega

end BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_attempts

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_attempts

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.empty_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.empty_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.step_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.program_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_attempts

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.sequence_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.distinct_tokens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence.distinct_tokens
