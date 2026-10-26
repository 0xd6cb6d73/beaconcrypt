import BeaconcryptCore.Computational.RawCtxQueryOccurrence

/-!
The original full receive/send programs have only their exact pending KDF continuations and occurrences in their actual completed callback tails. The receive proof follows the source skip rank; the send proof includes the advanced optional sealing result. These are compositional syntax laws. Concrete outer source induction must discharge the explicit continuation-property premises, so no security or arbitrary retagging premise is introduced. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingQueryTails
open RawCtxPendingOwnerQueries RawCtxQueryOccurrence

abbrev Property (Chain Result : Type) := (query : (Spec Chain).Domain) →
  ((Spec Chain).Range query → OracleComp (Spec Chain) Result) → Prop

noncomputable def receiveTail {Chain Result : Type}
    (after : Kernel Chain × core.option.Option RawCtxWholeOwner.Decrypted → OracleComp (Spec Chain) Result)
    (pending : RawCtxChainReceive.Kdf Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : Chain × RatchetMaterial) : OracleComp (Spec Chain) Result :=
  simulateQ receiveForward (RawCtxPendingReceiveQueries.program (RawCtxChainReceive.normalResume pending reply)) >>= after

noncomputable def receiveProgram {Chain Result : Type}
    (after : Kernel Chain × core.option.Option RawCtxWholeOwner.Decrypted → OracleComp (Spec Chain) Result)
    (effect : RawCtxChainReceive.Effect Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    OracleComp (Spec Chain) Result :=
  simulateQ receiveForward (RawCtxPendingReceiveQueries.program effect) >>= after

/-- Complete receive syntax has only original pending tails or occurrences in its actual completed callback continuation. -/
theorem receive_occurs {Chain Result : Type}
    (after : Kernel Chain × core.option.Option RawCtxWholeOwner.Decrypted → OracleComp (Spec Chain) Result)
    (property : Property Chain Result)
    (finished : ∀ result query next, Occurs query next (after result) →
      RawCtxPendingMixedPrefix.ownerSelected query = true → property query next)
    (pendingGood : ∀ pending, property (.inl (.inl pending)) (receiveTail after pending))
    (effect : RawCtxChainReceive.Effect Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (query : (Spec Chain).Domain) (next : (Spec Chain).Range query → OracleComp (Spec Chain) Result)
    (occurs : Occurs query next (receiveProgram after effect))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : property query next := by
  generalize depth : RawCtxChainReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
      cases effect with
      | rejected entry context =>
          simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_pure, pure_bind] at occurs
          exact finished (entry, .None) query next occurs selected
      | openRequested pending =>
          simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_bind,
            simulateQ_spec_query, simulateQ_pure, receiveForward, bind_assoc, pure_bind] at occurs
          rcases query_cases query (.inl (.inr pending)) next
            (fun reply => after (RawCtxChainReceive.normalFinish pending reply)) occurs with same | ⟨reply, later⟩
          · have sameQuery := congrArg Sigma.fst same
            change query = .inl (.inr pending) at sameQuery
            rw [sameQuery] at selected
            cases selected
          · exact finished (RawCtxChainReceive.normalFinish pending reply) query next later selected
      | kdfRequested pending =>
          simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_bind,
            simulateQ_spec_query, receiveForward, bind_assoc] at occurs
          rcases query_cases query (.inl (.inl pending)) next (receiveTail after pending) occurs with same | ⟨reply, later⟩
          · exact (congrArg (fun pair : Σ q, (Spec Chain).Range q → OracleComp (Spec Chain) Result =>
              property pair.1 pair.2) same).mpr (pendingGood pending)
          · exact ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply)
              (RawCtxChainReceive.normalResume pending reply) later rfl

noncomputable def sendTail {Chain Result : Type}
    (after : Kernel Chain × Option RawCtxSourceSend.Encrypted → OracleComp (Spec Chain) Result)
    (pending : RawCtxChainSend.Kdf Chain Chain RatchetMaterial RawCtxSourceSend.SealContext)
    (reply : Chain × RatchetMaterial) : OracleComp (Spec Chain) Result := do
  let ready := RawCtxChainSend.ready pending reply
  let sealed ← (Spec Chain).query (.inr (.inl (.inr ready)))
  after (ready.advanced, sealed)

noncomputable def sendProgram {Chain Result : Type}
    (after : Kernel Chain × Option RawCtxSourceSend.Encrypted → OracleComp (Spec Chain) Result)
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    OracleComp (Spec Chain) Result :=
  simulateQ sendForward (RawCtxPendingOwnerQueries.sendProgram start) >>= after

/-- Complete send syntax has only its original pending tail or occurrences after the actual advanced seal result. -/
theorem send_occurs {Chain Result : Type}
    (after : Kernel Chain × Option RawCtxSourceSend.Encrypted → OracleComp (Spec Chain) Result)
    (property : Property Chain Result)
    (finished : ∀ result query next, Occurs query next (after result) →
      RawCtxPendingMixedPrefix.ownerSelected query = true → property query next)
    (pendingGood : ∀ pending, property (.inr (.inl (.inl pending))) (sendTail after pending))
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext)
    (query : (Spec Chain).Domain) (next : (Spec Chain).Range query → OracleComp (Spec Chain) Result)
    (occurs : Occurs query next (sendProgram after start))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : property query next := by
  cases start with
  | exhausted entry context =>
      simp only [sendProgram, RawCtxPendingOwnerQueries.sendProgram, simulateQ_pure, pure_bind] at occurs
      exact finished (entry, none) query next occurs selected
  | requested pending =>
      simp only [sendProgram, RawCtxPendingOwnerQueries.sendProgram, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, sendForward, bind_assoc, pure_bind] at occurs
      rcases query_cases query (.inr (.inl (.inl pending))) next (sendTail after pending) occurs with same | ⟨reply, later⟩
      · exact (congrArg (fun pair : Σ q, (Spec Chain).Range q → OracleComp (Spec Chain) Result =>
          property pair.1 pair.2) same).mpr (pendingGood pending)
      · simp only [sendTail] at later
        rcases query_cases query (.inr (.inl (.inr (RawCtxChainSend.ready pending reply)))) next
          (fun sealed => after ((RawCtxChainSend.ready pending reply).advanced, sealed)) later with same | ⟨sealed, afterSeal⟩
        · have sameQuery := congrArg Sigma.fst same
          change query = .inr (.inl (.inr (RawCtxChainSend.ready pending reply))) at sameQuery
          rw [sameQuery] at selected
          cases selected
        · exact finished ((RawCtxChainSend.ready pending reply).advanced, sealed) query next afterSeal selected

end BeaconcryptCore.Computational.RawCtxPendingQueryTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingQueryTails.receive_occurs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingQueryTails.receive_occurs

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingQueryTails.send_occurs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingQueryTails.send_occurs
