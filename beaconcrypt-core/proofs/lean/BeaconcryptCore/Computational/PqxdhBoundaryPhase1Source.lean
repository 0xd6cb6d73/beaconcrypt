-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLivePhase1Bundle

/-! Exact source-order Phase-1 callbacks and complete-state continuations. The public Rust adapter correspondence remains reviewed transcription. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source
open PqxdhEd25519EufCma PqxdhJointPhase1SourceWriter
open PqxdhBeaconPhase1Publication (State prepare publish)
open PqxdhLivePhase1Bundle (Spec Public identityArray)
variable {I D K A Result : Type}

/-- The literal Phase-1 signing request retains the owner index and exact tagged message. -/
def signRequest (index : Nat) (message : Pqxdh.Bytes) : (Spec D).Domain :=
  .inr (.inl (.inr (.service index (.sign message))))

/-- The source prekey, one-time, PQ request order, with each rejected reply and its callback state retained. -/
def orderedSigning (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    StateT A ProbComp (Option Phase1Candidate) := do
  let pre ← implementation (signRequest index (prekeyMessage keys.prekey))
  match pre with
  | none => pure none
  | some pre =>
    let one ← implementation (signRequest index (oneTimeMessage keys.oneTime))
    match one with
    | none => pure none
    | some one =>
      let pq ← implementation (signRequest index (pqMessage keys.pqKey))
      pure (pq.map fun pq => candidate identity keys pre one pq)

/-- The existing key-free source signing block is exactly this ordered complete callback program. -/
theorem signing_exact (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    simulateQ implementation (PqxdhLivePhase1Bundle.signing index identity keys) =
      orderedSigning implementation index identity keys := by
  rw [PqxdhLivePhase1Bundle.signing_interpretation]
  simp only [signingProgram, orderedSigning, signRequest, simulateQ_bind, simulateQ_spec_query]
  congr 1
  funext pre
  cases pre <;> simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  congr 1
  funext one
  cases one <;> simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rfl

/-- Every signing result and the complete callback poststate feed the arbitrary source continuation. -/
theorem signing_continuation (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (auxiliary : A)
    (next : Option Phase1Candidate × A → ProbComp Result) :
    (simulateQ implementation (PqxdhLivePhase1Bundle.signing index identity keys)).run auxiliary >>= next =
      (orderedSigning implementation index identity keys).run auxiliary >>= next := by
  rw [signing_exact]

/-- Optional source serialization precedes role publication; failed writer effects remain in the complete callback state. -/
theorem writing_continuation (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (identity : Std.Array Std.U8 32#usize) (candidate : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ implementation (PqxdhLivePhase1Bundle.writing identity candidate generated state)).run auxiliary >>= next =
      match prepare state generated with
      | none => next ((none, state), auxiliary)
      | some prepared => (implementation (.inr (.inr candidate))).run auxiliary >>= fun reply =>
        match reply.1 with
        | none => next ((none, state), reply.2)
        | some bytes => next ((some bytes, publish identity prepared state), reply.2) := by
  rw [PqxdhLivePhase1Bundle.writing_interpretation, PqxdhBeaconPhase1Publication.afterSigning_complete]
  cases chosen : prepare state generated <;> simp only
  apply bind_congr
  rintro ⟨_ | bytes, post⟩ <;> rfl

/-- The explicit evaluated source tail; complete primitive state is passed through every optional result. -/
def preparedExecution (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (projection : Public I D K) (generated : Option D)
    (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) : ProbComp Result :=
      match prepare state generated with
      | none => next ((none, state), auxiliary)
      | some prepared =>
        (orderedSigning implementation (projection.index state.beacon.identity)
          (projection.identity state.beacon.identity)
          ⟨projection.dh prepared.prekey, projection.dh prepared.oneTime, projection.kem prepared.kem⟩).run auxiliary >>= fun signed =>
          match signed.1 with
          | none => next ((none, state), signed.2)
          | some candidate => (implementation (.inr (.inr candidate))).run signed.2 >>= fun written =>
            match written.1 with
            | none => next ((none, state), written.2)
            | some bytes => next ((some bytes, publish (identityArray (projection.identity state.beacon.identity)) prepared state), written.2)

/-- The source continuation uses the actual selected key tuple, three ordered optional signatures, then the original writer, retaining every callback poststate. -/
theorem prepared_continuation (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (projection : Public I D K) (generated : Option D)
    (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ implementation (PqxdhLivePhase1Bundle.afterGenerated projection generated state)).run auxiliary >>= next =
      preparedExecution implementation projection generated state auxiliary next := by
  unfold preparedExecution
  rw [PqxdhLivePhase1Bundle.afterGenerated_complete]
  simp_rw [← PqxdhLivePhase1Bundle.signing_interpretation, signing_exact]
  cases chosen : prepare state generated <;> simp only
  apply bind_congr
  rintro ⟨_ | candidate, post⟩ <;> simp only
  rw [PqxdhBeaconPhase1Publication.afterSigning_complete, chosen]
  apply bind_congr
  rintro ⟨_ | bytes, final⟩ <;> rfl

/-- The complete bundle call keeps generation at its source position, then executes the exact source tail and arbitrary whole-state continuation, including every failure. -/
theorem bundle_continuation (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (projection : Public I D K) (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ implementation (PqxdhLivePhase1Bundle.bundle projection state)).run auxiliary >>= next =
      match state.beacon.phase with
      | .fresh _ _ _ => (implementation (.inl ())).run auxiliary >>= fun generated =>
        preparedExecution implementation projection generated.1 state generated.2 next
      | .freshWithCoins _ _ _ _ => preparedExecution implementation projection none state auxiliary next
      | _ => next ((none, state), auxiliary) := by
  rw [PqxdhLivePhase1Bundle.bundle_complete]
  simp_rw [prepared_continuation]
  rfl

/-- Each actual bundle call has at most one generation, three signature requests and one writer request; these are service counts, not a claim that callback work is free. -/
theorem bundle_service_caps (projection : Public I D K) (state : State (I := I) (D := D) (K := K)) :
    (PqxdhLivePhase1Bundle.bundle projection state).IsQueryBoundP (PqxdhLivePhase1Bundle.IsKind (D := D) .generation) 1 ∧
    (PqxdhLivePhase1Bundle.bundle projection state).IsQueryBoundP (PqxdhLivePhase1Bundle.IsKind (D := D) .signing) 3 ∧
    (PqxdhLivePhase1Bundle.bundle projection state).IsQueryBoundP (PqxdhLivePhase1Bundle.IsKind (D := D) .serialization) 1 := by
  simpa only [reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero] using
    And.intro (PqxdhLivePhase1Bundle.bundle_bound projection state .generation)
      (And.intro (PqxdhLivePhase1Bundle.bundle_bound projection state .signing)
        (PqxdhLivePhase1Bundle.bundle_bound projection state .serialization))

end BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.signing_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.signing_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.signing_continuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.signing_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.writing_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.writing_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.prepared_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.prepared_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.bundle_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.bundle_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.bundle_service_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Source.bundle_service_caps
