import BeaconcryptCore.Computational.PqxdhInitialHalfBuilderMap
import BeaconcryptCore.Computational.PqxdhInitialHalfPrivateObserver

/-!
The actual first Server builder precedes the complete original adaptive post schedule. Its admission, send, erase and publication callbacks have no adversary read, and installation preserves the original reveal history. The full source disclosure invariant therefore starts from the literal pre-builder history and is derived through the same native-read interpreter.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure
open PqxdhInitialPendingPost PqxdhInitialDisclosureState PqxdhSecretInputKdf
open RawCtxSelectedChain
variable {ι M P I D K X Response Shared Result Origin Z : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem aux_quiet (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    (auxForward (extra := extra) (Chain := Slot) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) (S := S) (B := B) query).IsQueryBoundP (isRead (extra := extra)) 0 :=
  (isQueryBoundP_query_iff _ _ _).mpr (by simp only [isRead, IsEmpty.forall_iff])

/-- Original first-send, erase and optional serialization callbacks contain no adversary disclosure query. -/
theorem after_quiet (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : KernelOf Slot) (metadata : P)
    (before : PqxdhInitialGenericPublication.State (KernelOf Slot) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericPublication.afterInitialization
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward candidate authenticated kernel metadata before).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  apply isQueryBoundP_bind (n := 0) (m := 0) (primitive_quiet (RawCtxPendingOwnerQueries.calls.send kernel _))
  intro sent _
  apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
  intro erased _
  cases sent.2 with
  | none => trivial
  | some encrypted =>
      apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
      intro written _
      cases written <;> trivial

/-- Every original admission branch either rejects or continues to the same disclosure-free first-send tail. -/
theorem candidate_quiet (first : RustM (KernelOf Slot)) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : P)
    (before : PqxdhInitialGenericPublication.State (KernelOf Slot) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericBuilder.candidate
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward first candidate data metadata before).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialGenericBuilder.candidate
  apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
  intro valid _
  cases valid
  · trivial
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
    intro reserved _
    cases reserved
    · trivial
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases first with
      | fail error => trivial
      | div => trivial
      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          split
          · trivial
          · split
            · apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
              intro allocated _
              cases allocated
              · trivial
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : candidate.key_id_binding with
                | fail error => trivial
                | div => trivial
                | ok binding =>
                    exact (isQueryBoundP_map_iff _ _ _).mpr (after_quiet candidate _ kernel metadata before)
            · trivial

/-- The actual current allocator and Ready preparation introduce no family disclosure callback. -/
theorem ready_quiet (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (first : RustM (KernelOf Slot))
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (before : PqxdhInitialGenericPublication.State (KernelOf Slot) M P (List Pqxdh.Bytes)) :
    (PqxdhInitialGenericBuilder.readyBuild source
      (calls (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      auxForward first binding ready metadata before).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild
  cases next : pqxdh.server_next_key_id before.control with
  | fail error => trivial
  | div => trivial
  | ok result =>
      cases result with
      | Err error => trivial
      | Ok key =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare before.control
            (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
            ⟨before.server.identity, before.identityKeyId⟩
            (if (before.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => trivial
          | div => trivial
          | ok result =>
              cases result with
              | Err error => trivial
              | Ok candidate => exact candidate_quiet first candidate ready.application metadata before

/-- The complete actual pre-first-send builder has zero adversary reads, including consumption and unsuccessful publication. -/
theorem build_quiet (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (first : RustM (KernelOf Slot))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : Front Slot M P I D K S B) :
    ((PqxdhInitialPendingBuilder.build (extra := extra) (X := X) (Response := Response) (Shared := Shared)
      source first sender index metadata ready).run before).IsQueryBoundP (isRead (extra := extra)) 0 :=
  (isQueryBoundP_map_iff _ _ _).mpr (ready_quiet source first _ ready metadata _)

/-- Consumption and reinstalling the actual builder result preserve the literal pre-builder reveal history on every Rust branch. -/
theorem reinstall_history (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : Front Slot M P I D K S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State (KernelOf Slot) M P (List Pqxdh.Bytes))) :
    (PqxdhInitialPendingBuilder.reinstall index (PqxdhInitialPendingBuilder.consume index ready before) result).2.roles.2 = before.roles.2 := by
  cases result <;> rfl

/-- The full original builder and adaptive post derive final disclosure facts from the actual pre-builder history; no final-history premise is assumed. -/
theorem sequence_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (disclosed : List RatchetChain)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (first : RustM (KernelOf Slot))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) (state : State Z)
    (valid : Invariant target disclosed before.1.roles.2 state)
    (result : (Result × (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × State Z)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialOriginPost.sequence source first mark origin sender route decode index metadata ready post).run before)).run state)) :
    Invariant target disclosed result.1.2.1.roles.2 result.2 := by
  change result ∈ support ((simulateQ impl (do
    let built ← (PqxdhInitialPendingBuilder.build source first sender index metadata ready).run before.1
    (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (post built.1)).run
      (built.2, PqxdhInitialOriginPost.afterBuilder before.2 built.2 index origin built.1))).run state) at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨built, reached, rest⟩ := supported
  have kept := quiet_program target impl rules _ (build_quiet source first sender index metadata ready before.1) state built reached
  have history : built.1.2.roles.2 = before.1.roles.2 := by
    change built ∈ support ((simulateQ impl (PqxdhInitialPendingBuilder.reinstall index
      (PqxdhInitialPendingBuilder.consume index ready before.1) <$>
      PqxdhInitialGenericBuilder.readyBuild source calls auxForward first
        ⟨(PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before.1)).server.identity,
          (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before.1)).identityKeyId⟩
        ready metadata (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before.1)))).run state) at reached
    simp only [simulateQ_map, StateT.run_map, support_map] at reached
    obtain ⟨original, _, rfl⟩ := reached
    exact reinstall_history index ready before.1 original.1
  exact schedule_invariant target impl rules disclosed mark sender route decode (post built.1.1) _ built.2
    (history.symm ▸ invariant_keep target disclosed before.1.roles.2 state built.2 valid kept) result rest

end BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.after_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.after_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.candidate_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.candidate_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.ready_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.ready_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.build_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.build_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.reinstall_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.reinstall_history

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.sequence_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure.sequence_invariant
