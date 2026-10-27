import BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin
import BeaconcryptCore.Computational.PqxdhInitialPendingPost
import BeaconcryptCore.Computational.PqxdhInitialPendingAccepted
import BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds
import BeaconcryptCore.Computational.RawCtxPublishedRecords

/-!
The full original post compiler retains an explicit private installation-origin map and records successful original sends together with the origin installed at that owner. Successful Beacon finishes update that map from their actual prepared initializer; failed and inactive finishes preserve it. Every original request, optional reply, role field and reveal-history update remains in source order.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginPost
open PqxdhInitialPendingPost RawCtxProtocolReveals
variable {ι Chain M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

structure Trace (Origin : Type) (S B : Nat) where
  installed : Owner S B → Option Origin
  published : List (RawCtxPublishedRecords.Publication S B × Origin)

def record (before : Trace Origin S B) (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (reply : (RawCtxProtocolReveals.SourceSpec S B).Range query) : Trace Origin S B :=
  let added := (RawCtxPublishedRecords.record query reply).filterMap
    (fun publication => (before.installed publication.1).map (fun origin => (publication, origin)))
  { before with published := before.published ++ added }

def finish (before : Trace Origin S B) (index : Fin B) (origin : Option Origin) : Trace Origin S B :=
  match origin with
  | none => before
  | some origin => { before with installed := Function.update before.installed (.beacon index) (some origin) }

noncomputable def compiler (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (StateT (Front Chain M P I D K S B × Trace Origin S B)
        (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B)))
  | .inl (.inl query) => fun before => do
      let result ← simulateQ liveForward ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run before.1.roles)
      pure (result.1, ({ before.1 with roles := result.2 }, record before.2 query result.1))
  | .inl (.inr query) => fun before => do
      let reply ← selectorForward query
      pure (reply, before)
  | .inr (.finish index raw) => fun before => do
      let result ← PqxdhInitialFinishOrigin.owner mark preForward calls applicationForward initialForward decode raw (before.1.roles.1.2 index)
      pure (result.1.1, (install index before.1 result.1.2, finish before.2 index result.2))

/-- Erasing only private origin and publication metadata recovers each complete original post operation. -/
theorem step_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Front Chain M P I D K S B × Trace Origin S B) :
    Prod.map id Prod.fst <$> (compiler (X := X) (Response := Response) mark sender route decode query).run before =
      (PqxdhInitialPendingPost.compiler sender route decode query).run before.1 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · simp only [compiler, PqxdhInitialPendingPost.compiler, StateT.run, map_bind, map_pure]
    rfl
  · simp only [compiler, PqxdhInitialPendingPost.compiler, StateT.run, map_bind, map_pure]
    rfl
  · simp only [compiler, PqxdhInitialPendingPost.compiler, StateT.run, bind_pure_comp, Functor.map_map]
    rw [← PqxdhInitialFinishOrigin.erase mark preForward calls applicationForward initialForward decode raw (before.1.roles.1.2 index)]
    simp only [Functor.map_map]
    rfl

/-- The complete adaptive original post client retains its exact result and full frontend state when the private transcript is erased. -/
theorem program_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Chain M P I D K S B × Trace Origin S B) :
    Prod.map id Prod.fst <$> (simulateQ (compiler (X := X) (Response := Response) mark sender route decode) client).run before =
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) client).run before.1 := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step_erase mark sender route decode query before]
    simp only [bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 result.2

/-- Every all-reply primitive-class budget is preserved by the complete private origin/publication transcript. -/
theorem query_bound (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Chain M P I D K S B × Trace Origin S B)
    (predicate : (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (compiler mark sender route decode) client).run before).IsQueryBoundP predicate budget ↔
      ((simulateQ (PqxdhInitialPendingPost.compiler sender route decode) client).run before.1).IsQueryBoundP predicate budget := by
  rw [← program_erase mark sender route decode client before]
  exact (isQueryBoundP_map_iff _ _ _).symm

/-- Each newly appended record has both an actual successful send reply and the origin installed at that owner before the operation. -/
theorem record_member (before : Trace Origin S B)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (reply : (RawCtxProtocolReveals.SourceSpec S B).Range query)
    (publication : RawCtxPublishedRecords.Publication S B) (origin : Origin) :
    (publication, origin) ∈ (record before query reply).published ↔
      (publication, origin) ∈ before.published ∨
        publication ∈ RawCtxPublishedRecords.record query reply ∧ before.installed publication.1 = some origin := by
  simp only [record, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (old | ⟨found, actual, mapped⟩)
    · exact Or.inl old
    · obtain ⟨value, installed, equality⟩ := Option.map_eq_some_iff.mp mapped
      cases equality
      exact Or.inr ⟨actual, installed⟩
  · rintro (old | ⟨actual, installed⟩)
    · exact Or.inl old
    · exact Or.inr ⟨publication, actual, by simp only [installed, Option.map_some]⟩

/-- The successful-origin finish uses the exact same interpreted preparation and complete first-receive tail, preserving all underlying state effects. -/
theorem owner_interpretation {κ Kernel : Type} {spec : OracleSpec κ} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → OracleComp spec (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K) :
    simulateQ impl (PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw state) =
      PqxdhInitialFinishOrigin.owner mark (impl ∘ₛ pre)
        (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply))
        (fun secrets => simulateQ impl (initial secrets)) decode raw state := by
  unfold PqxdhInitialFinishOrigin.owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => exact simulateQ_pure _ _
    | some prepared =>
      simp only [bind_pure_comp, simulateQ_map, PqxdhInitialPendingPost.tail_interpretation]
  all_goals exact simulateQ_pure _ _

/-- Every successful finish in the actual interpreted compiler records an origin from that same complete original finish, with all ambient effects retained. -/
theorem finish_supported {State : Type}
    (impl : QueryImpl (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B) (StateT State ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : Front Chain M P I D K S B × Trace Origin S B)
    (ambient : State) (result : (Option Pqxdh.Bytes × (Front Chain M P I D K S B × Trace Origin S B)) × State)
    (supported : result ∈ support ((simulateQ impl
      ((compiler mark sender route decode (.inr (.finish index raw))).run before)).run ambient))
    (success : result.1.1.isSome = true) :
    ∃ (finished : PqxdhInitialFinishOrigin.Result (KernelOf Chain) Origin I D K × State) (origin : Origin),
      finished ∈ support ((PqxdhInitialFinishOrigin.owner mark (impl ∘ₛ preForward)
        (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (applicationForward reply))
        (fun secrets => simulateQ impl (initialForward secrets)) decode raw (before.1.roles.1.2 index)).run ambient) ∧
      finished.1.2 = some origin ∧
      result = ((finished.1.1.1, (install index before.1 finished.1.1.2, finish before.2 index finished.1.2)), finished.2) ∧
      result.1.2.2.installed (.beacon index) = some origin := by
  change result ∈ support ((simulateQ impl (do
    let finished ← PqxdhInitialFinishOrigin.owner mark preForward calls applicationForward initialForward decode raw (before.1.roles.1.2 index)
    pure (finished.1.1, (install index before.1 finished.1.2, finish before.2 index finished.2)))).run ambient) at supported
  simp only [bind_pure_comp, simulateQ_map, owner_interpretation, StateT.run_map, support_map] at supported
  obtain ⟨finished, reached, equality⟩ := supported
  subst result
  have present := PqxdhInitialFinishOrigin.published mark (impl ∘ₛ preForward)
    (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
    (fun reply => simulateQ impl (applicationForward reply))
    (fun secrets => simulateQ impl (initialForward secrets)) decode raw (before.1.roles.1.2 index)
    ambient finished reached
  have marker : finished.1.2.isSome = true := present.trans success
  obtain ⟨origin, originEq⟩ := Option.isSome_iff_exists.mp marker
  refine ⟨finished, origin, reached, originEq, rfl, ?_⟩
  simp only [finish, originEq, Function.update_self]

def afterBuilder (before : Trace Origin S B) (front : Front Chain M P I D K S B)
    (index : Fin S) (origin : Origin) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) : Trace Origin S B :=
  match reply with
  | .ok (some response) =>
      match (front.roles.1.1 index).server.peers response.keyId with
      | none => before
      | some peer =>
          let owner := Owner.server index response.keyId
          { installed := Function.update before.installed owner (some origin)
            published := before.published ++ [((owner, peer.kernel.control.send_sequence), origin)] }
  | _ => before

noncomputable def sequence (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) :
    StateT (Front Chain M P I D K S B × Trace Origin S B)
      (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B)) Result := fun before => do
  let built ← (PqxdhInitialPendingBuilder.build source initial sender index metadata ready).run before.1
  (simulateQ (compiler mark sender route decode) (post built.1)).run
    (built.2, afterBuilder before.2 built.2 index origin built.1)

/-- The actual first builder, its returned response, installed peer and complete original post client are retained when only the private transcript is erased. -/
theorem sequence_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Chain M P I D K S B × Trace Origin S B) :
    Prod.map id Prod.fst <$> ((sequence (X := X) (Response := Response) source initial mark origin
      sender route decode index metadata ready post).run before) =
      (PqxdhInitialPendingAccepted.sequence source initial sender route decode index metadata ready post).run before.1 := by
  simp only [sequence, StateT.run, PqxdhInitialPendingAccepted.sequence, map_bind]
  apply bind_congr
  intro built
  exact program_erase mark sender route decode (post built.1) _

/-- A new first-response transcript entry requires an actual successful builder reply and its actual installed peer; its sequence is read from that same returned kernel. -/
theorem builder_recorded (before : Trace Origin S B) (front : Front Chain M P I D K S B)
    (index : Fin S) (origin : Origin) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (publication : RawCtxPublishedRecords.Publication S B) (recordedOrigin : Origin)
    (recorded : (publication, recordedOrigin) ∈ (afterBuilder before front index origin reply).published)
    (new : (publication, recordedOrigin) ∉ before.published) :
    ∃ (response : PqxdhServerRegistrationPublication.Response) (peer : RawCtxGenericRoleStorage.Peer (KernelOf Chain) P),
      reply = .ok (some response) ∧ (front.roles.1.1 index).server.peers response.keyId = some peer ∧
      publication = (.server index response.keyId, peer.kernel.control.send_sequence) ∧ recordedOrigin = origin := by
  cases reply with
  | fail error => exact False.elim (new recorded)
  | div => exact False.elim (new recorded)
  | ok reply =>
    cases reply with
    | none => exact False.elim (new recorded)
    | some response =>
      cases found : (front.roles.1.1 index).server.peers response.keyId with
      | none => simp only [afterBuilder, found] at recorded; exact False.elim (new recorded)
      | some peer =>
        simp only [afterBuilder, found, List.mem_append, List.mem_singleton] at recorded
        have same := recorded.resolve_left new
        cases same
        exact ⟨response, peer, rfl, found, rfl, rfl⟩

/-- The complete instrumented first-builder and post program pays the same explicit all-reply callback bill as its original source. -/
theorem sequence_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (before : Front Chain M P I D K S B × Trace Origin S B) :
    ((sequence (X := X) (Response := Response) source initial mark origin sender route decode index metadata ready post).run before).IsTotalQueryBound
      (7 + qPost * 67) := by
  apply (isQueryBound_map_iff _ (Prod.map id Prod.fst) _ _ _).mp
  rw [sequence_erase]
  exact PqxdhInitialPendingSourceBounds.sequence_total source initial sender route decode index metadata ready post qPost bounded before.1

end BeaconcryptCore.Computational.PqxdhInitialOriginPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.step_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.step_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.program_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.query_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.record_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.record_member
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.owner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.owner_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.finish_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.finish_supported
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.sequence_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.sequence_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.builder_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.builder_recorded
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPost.sequence_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPost.sequence_total
