import BeaconcryptCore.Computational.PqxdhInitialPendingAccepted
import BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets
import BeaconcryptCore.Computational.PqxdhInitialFusedBudgets

/-!
The full original post schedule has an explicit conservative callback bill in its pending representation. This counts raw receive skips, sends, live reads, preparation, application, initialization, selectors and builder auxiliaries before any primitive interpretation. The bounds concern the literal source oracle program under every reply; probability equalities do not transport resource bounds.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds
open PqxdhInitialPendingPost PqxdhBeaconPhase2Bounds
variable {ι Chain M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual enriched receive retains all fifty-one possible derivations and its one opening callback. -/
theorem receive_total (kernel : KernelOf Chain) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (RawCtxPendingOwnerQueries.calls.receive kernel sequence context).IsTotalQueryBound 52 := by
  apply simulate_total RawCtxPendingOwnerQueries.receiveForward _ 52
  · apply total_of_partition (fun query => query.isLeft = true) _ 51 1
    · exact RawCtxPendingReceiveQueries.receive_bound kernel sequence context
    · apply IsQueryBoundP.of_imp (p' := fun query => query.isRight = true) _
        (RawCtxPendingReceiveQueries.opening_bound _)
      intro query selected
      cases query <;> simp_all
  · intro query
    exact (isQueryBoundP_true_iff _ _).mp ((isQueryBoundP_query_iff _ _ _).mpr (by decide))

/-- An actual enriched send makes at most one derivation and one sealing callback, including failed sealing. -/
theorem send_total (kernel : KernelOf Chain) (context : RawCtxSourceSend.SealContext) :
    (RawCtxPendingOwnerQueries.calls.send kernel context).IsTotalQueryBound 2 := by
  apply simulate_total RawCtxPendingOwnerQueries.sendForward _ 2
  · cases RawCtxChainSend.normalBegin kernel context with
    | exhausted => trivial
    | requested pending => exact ⟨by omega, fun _ => ⟨by change 0 < 2 - 1; decide, fun _ => True.intro⟩⟩
  · intro query
    exact (isQueryBoundP_true_iff _ _).mp ((isQueryBoundP_query_iff _ _ _).mpr (by decide))

private theorem one_query {κ : Type} {spec : OracleSpec κ} (query : spec.Domain) :
    (spec.query query : OracleComp spec (spec.Range query)).IsTotalQueryBound 1 :=
  ⟨by change 0 < 1; decide, fun _ => True.intro⟩

/-- Every original live record or read request costs at most fifty-two pending callbacks under all replies and complete role states. -/
theorem live_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : RawCtxPendingFamilyLiveQueries.State Chain M P I D K S B) :
    ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run state).IsTotalQueryBound 52 := by
  cases query with
  | inl request =>
      simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff]
      apply simulate_total RawCtxPendingFamilyLiveQueries.primitiveForward _ 52 _ (fun _ => one_query _)
      apply (isQueryBoundP_true_iff _ _).mp
      exact RawCtxGenericFamilyBudgets.family_step RawCtxPendingOwnerQueries.calls
        RawCtxPendingOwnerQueries.publicForward (fun _ => True) (fun _ => 52)
        (fun entry target context => (receive_total entry target context).isQueryBoundP)
        (fun entry context => ((send_total entry context).mono (by decide)).isQueryBoundP)
        (fun _ => ((one_query _).mono (by decide)).isQueryBoundP) sender route decode request state.1
  | inr request =>
      simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff]
      exact (one_query _).mono (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- The full post first-receive continuation reserves one application callback and the complete original pending raw receive. -/
theorem after_total (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : KernelOf Chain) :
    (PqxdhInitialGenericBeacon.afterInitial
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Shared := Shared) (S := S) (B := B))
      applicationForward decode pending kernel).IsTotalQueryBound 53 := by
  simp only [PqxdhInitialGenericBeacon.afterInitial, applicationForward]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      apply (isQueryBoundP_true_iff _ _).mp
      apply RawCtxGenericFamilyBudgets.owner_raw calls (fun _ => True) 52 _ decode raw _
      intro entry target context
      change (simulateQ primitiveForward (RawCtxPendingOwnerQueries.calls.receive entry target context)).IsQueryBoundP (fun _ => True) 52
      exact (simulate_total primitiveForward _ 52 (receive_total entry target context) (fun _ => one_query _)).isQueryBoundP

set_option backward.isDefEq.respectTransparency false in
/-- The original optional initializer adds one explicit callback before the whole first-receive tail. -/
theorem tail_total (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    (PqxdhInitialGenericBeacon.tail
      (calls (Chain := Chain) (extra := extra) (I := I) (D := D) (K := K) (X := X) (Shared := Shared) (S := S) (B := B))
      applicationForward initialForward decode pending).IsTotalQueryBound 54 := by
  simp only [PqxdhInitialGenericBeacon.tail, initialForward]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some kernel => exact after_total decode pending kernel

/-- Every attempted Beacon finish reserves thirteen preparation callbacks and fifty-four initializer/application/receive callbacks, including every rejection branch. -/
theorem owner_total (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K) :
    (PqxdhInitialGenericBeacon.owner preForward
      (calls (extra := extra) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      applicationForward initialForward decode raw state).IsTotalQueryBound 67 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [PqxdhInitialGenericBeacon.owner, active]
      apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 54)
      · exact simulate_total preForward _ 13 (PqxdhPhase2SharedBounds.prepare_total _ _ _ _ _ _) (fun _ => one_query _)
      · intro pending
        cases pending with
        | none => trivial
        | some pending =>
            simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
            exact tail_total decode pending
  | _ => simp only [PqxdhInitialGenericBeacon.owner, active]; trivial

/-- A source post request costs at most sixty-seven pending callbacks, including live records, public reads, selectors and attempted registrations. -/
theorem step_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Front Chain M P I D K S B) :
    ((compiler (X := X) (Response := Response) (Shared := Shared) sender route decode query).run before).IsTotalQueryBound 67 := by
  rcases query with (query | query) | query
  · simp only [compiler, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact (simulate_total liveForward _ 52 (live_total sender route decode query before.roles) (fun _ => one_query _)).mono (by decide)
  · simp only [compiler, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact (one_query _).mono (by decide)
  · cases query with
    | finish index raw =>
        simp only [compiler, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
        exact owner_total decode raw (before.roles.1.2 index)

/-- An arbitrary adaptive original post client retains its full schedule and pays sixty-seven callbacks per admitted source query. -/
theorem program_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : Front Chain M P I D K S B) :
    ((simulateQ (compiler (X := X) (Response := Response) (Shared := Shared) sender route decode) client).run before).IsTotalQueryBound (qPost * 67) := by
  apply (isQueryBoundP_true_iff _ _).mp
  exact interpreted_total_bound _ (fun _ => True) 67 qPost
    (fun query state => (step_total sender route decode query state).isQueryBoundP) client bounded before

/-- The complete first-send publication tail reserves the derivation, sealing, erasure and serialization callbacks. -/
theorem publication_total (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : KernelOf Chain) (metadata : P)
    (state : PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericPublication.afterInitialization
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward candidate authenticated kernel metadata state).IsTotalQueryBound 4 := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  apply isTotalQueryBound_bind (n₁ := 2) (n₂ := 2)
  · exact simulate_total primitiveForward _ 2 (send_total kernel _) (fun _ => one_query _)
  · rintro ⟨advanced, encrypted⟩
    apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) (one_query _)
    intro erased
    cases encrypted with
    | none => trivial
    | some encrypted =>
        exact isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (one_query _)
          (fun reply => by cases reply <;> trivial)

/-- Every original candidate gate and the complete first-send tail fit seven pending callbacks for arbitrary initializer success, failure or divergence. -/
theorem candidate_total (initial : RustM (KernelOf Chain)) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : P)
    (state : PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericBuilder.candidate
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward initial candidate data metadata state).IsTotalQueryBound 7 := by
  unfold PqxdhInitialGenericBuilder.candidate
  apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 6) (one_query _)
  intro valid
  cases valid
  · trivial
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 5) (one_query _)
    intro reserved
    cases reserved
    · trivial
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => trivial
      | div => trivial
      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          split
          · trivial
          · split
            · apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 4) (one_query _)
              intro allocated
              cases allocated
              · trivial
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : candidate.key_id_binding with
                | fail error => trivial
                | div => trivial
                | ok binding =>
                    simp only [IsTotalQueryBound, isQueryBound_map_iff]
                    exact publication_total candidate _ kernel metadata state
            · trivial

private theorem continue_total {α β κ : Type} {spec : OracleSpec κ}
    (result : RustM α) (next : α → OracleComp spec (RustM β)) (budget : Nat)
    (bounded : ∀ value, (next value).IsTotalQueryBound budget) :
    (PqxdhInitialGenericBuilder.continueRust result next).IsTotalQueryBound budget := by
  cases result
  all_goals first | exact bounded _ | trivial

/-- Pure allocation and registration preparation add no pending callback before the same seven-call candidate program. -/
theorem ready_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (state : PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericBuilder.readyBuild source
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward initial binding ready metadata state).IsTotalQueryBound 7 := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild
  apply continue_total
  rintro (_ | next)
  all_goals try trivial
  apply continue_total
  rintro (prepared | _)
  all_goals first | exact candidate_total initial _ ready.application metadata state | trivial

/-- The complete consumed-registration builder has seven pending callbacks, preserving every reinstall and error branch. -/
theorem builder_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) :
    ((PqxdhInitialPendingBuilder.build (extra := extra) (X := X) (Response := Response) (Shared := Shared)
      source initial sender index metadata ready).run before).IsTotalQueryBound 7 := by
  simp only [PqxdhInitialPendingBuilder.build, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  exact ready_total source initial _ ready metadata _

/-- The single complete accepted source retains its first response and every adaptive post request with an explicit all-reply callback bill. -/
theorem sequence_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (before : Front Chain M P I D K S B) :
    ((PqxdhInitialPendingAccepted.sequence (X := X) (Response := Response) (Shared := Shared)
      source initial sender route decode index metadata ready post).run before).IsTotalQueryBound (7 + qPost * 67) := by
  simp only [PqxdhInitialPendingAccepted.sequence, StateT.run_bind]
  exact isTotalQueryBound_bind (builder_total source initial sender index metadata ready before)
    (fun result => program_total sender route decode (post result.1) qPost (bounded result.1) result.2)

end BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.receive_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.receive_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.send_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.send_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.live_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.live_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.after_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.after_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.tail_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.tail_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.owner_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.owner_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.step_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.step_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.program_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.program_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.publication_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.publication_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.candidate_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.candidate_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.ready_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.ready_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.builder_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.builder_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.sequence_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds.sequence_total
