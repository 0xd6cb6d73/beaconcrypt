import BeaconcryptCore.Computational.PqxdhServerAuthPublicationIdentity
import BeaconcryptCore.Computational.PqxdhRegistrationAdmission
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-!
Actual R1 Phase1 acceptance retains its original signed fields and verified tuple through the pending-token boundary. These source receipts keep the actual optional prefix and root-service replies; the existing attached-verification adapter is explicit only when translating to the maintained signature detector. Whole-run journal attribution and its joint-signature reduction remain separate consumers.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerRootPreparation PqxdhServerStaticDhSource
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Original decoder and field-getter replies of the reached verification. -/
def Decoded (codec : Codec Reader Response) (raw : Pqxdh.Bytes) (verified : Verified Reader) : Prop :=
  codec.read1 raw = some verified.reader ∧
  codec.identity verified.reader = some verified.candidate.identityKey ∧
  codec.preField verified.reader = some verified.candidate.preKey ∧
  codec.oneField verified.reader = some verified.candidate.oneTimeKey ∧
  codec.pqField verified.reader = some verified.candidate.pqKey

/-- The actual successful raw verification phase supplies the original candidate's complete attached-verifier acceptance. No signature-security premise is needed for this source fact. -/
theorem verify_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (raw : Pqxdh.Bytes) (before after : List Pqxdh.Bytes) (verified : Verified Reader)
    (supported : (some verified, after) ∈ support ((simulateQ
      (prefixImpl setup.serverDomain (serverAux setup codec checks) (fun _ => pure ()))
      (verifyInput raw)).run before)) :
    Decoded codec raw verified ∧
    PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate = some (verified.identity, verified.keys) := by
  simp only [verifyInput, simulateQ_bind, simulateQ_spec_query, prefixImpl, serverAux,
    pure_bind] at supported
  repeat' first
    | split at supported
    | (simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, prefixImpl,
        serverAux, StateT.run_pure, pure_bind, Option.bind_eq_bind, Option.bind, Option.pure_def, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported)
    | contradiction
  all_goals simp_all [Decoded, PqxdhJointPhase1Reports.sourceAccept]

/-- Successful generation, encapsulation and conversion retain the same raw-reader and verified signed-field receipt. -/
theorem prefix_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (raw : Pqxdh.Bytes) (before after : List Pqxdh.Bytes)
    (input : Inputs Reader ScalarBytes PeerEncoding)
    (supported : (some input, after) ∈ support ((serverPrefix setup codec checks raw).run before)) :
    Decoded codec raw input.verified ∧
    PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      input.verified.candidate = some (input.verified.identity, input.verified.keys) := by
  simp only [serverPrefix, collect, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  rcases supported with ⟨⟨_ | verified, middle⟩, checked, reached⟩
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, Option.some_ne_none, false_and] at reached
  exact (PqxdhRegistrationAdmission.collect_verified _ verified middle after input reached).symm ▸
    verify_receipt setup codec checks raw before middle verified checked

/-- The existing attached-verification adapter exposes precisely the accepted unsigned tuple used by the joint identity reduction. The adapter is explicit for arbitrary input buffers. -/
theorem prefix_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (raw : Pqxdh.Bytes) (before after : List Pqxdh.Bytes)
    (input : Inputs Reader ScalarBytes PeerEncoding)
    (supported : (some input, after) ∈ support ((serverPrefix setup codec checks raw).run before))
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify input.verified.candidate =
      some (input.verified.identity, input.verified.keys) :=
  (PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint adapter input.verified.candidate).symm.trans
    (prefix_receipt setup codec checks raw before after input supported).2

/-- With the existing adapter, a changed accepted unsigned tuple is exactly the maintained three-field substitution event, without selecting a field or assuming signature uniqueness. -/
theorem prefix_fields_or_substitution (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (raw : Pqxdh.Bytes) (before after : List Pqxdh.Bytes)
    (input : Inputs Reader ScalarBytes PeerEncoding)
    (supported : (some input, after) ∈ support ((serverPrefix setup codec checks raw).run before))
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    {Context : Type} (material : PqxdhEd25519EufCma.Phase1Material Context) :
    input.verified.keys = material.keyTuple ∨
      PqxdhEd25519EufCma.phase1FieldSubstitutionBit setup.joint.verify input.verified.identity
        material input.verified.candidate = true :=
  Classical.byCases (fun equal => Or.inl equal) (fun different => Or.inr
    ((PqxdhEd25519EufCma.phase1FieldSubstitutionBit_eq_true_iff _ _ _ _).mpr
      ⟨input.verified.keys, prefix_accept setup codec checks raw before after input supported adapter, different⟩))

open PqxdhServerAuthEntryFactor

/-- A successful source accept retains its actual prefix input, root-service reply and newly installed token at the current allocated index. Arbitrary selected-entry services remain explicit. -/
theorem accept_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) {τ : Type} (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (index : Nat) (after : FlatState KemSK τ)
    (supported : (some index, after) ∈ support
      ((acceptStep setup codec checks publicValue services raw).run state)) :
    index = state.1.sessions ∧ ∃ input consumed reply table root,
      (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run state.1.server.consumed) ∧
      (reply, table) ∈ support ((services.derive (PqxdhServerRelatedRootInput.message input)).run state.2.2) ∧
      reply.value = some root ∧
      after.1.pending index = some ⟨root, PqxdhServerClearedRoot.pending (binding setup publicValue) input⟩ ∧
      Decoded codec raw input.verified ∧
      PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
        input.verified.candidate = some (input.verified.identity, input.verified.keys) := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  rcases supported with ⟨⟨_ | input, consumed⟩, collectedRun, supported⟩
  all_goals simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported
  split_ifs at supported with nonzero
  all_goals simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, Option.some_ne_none, false_and] at supported
  rcases supported with ⟨⟨reply, table⟩, derived, sameIndex, rfl⟩
  cases reply <;> simp only [afterDerive, Reply.value, Option.some.injEq, reduceCtorEq] at sameIndex
  all_goals refine ⟨sameIndex, input, consumed, _, table, _, collectedRun, derived, rfl, ?_,
    prefix_receipt setup codec checks raw state.1.server.consumed consumed input collectedRun⟩
  all_goals simp only [sameIndex, afterDerive, Reply.value, Function.update_self]

/-- A rejected complete accept leaves every pending token unchanged, including all prefix and root-service rejection branches. -/
theorem accept_rejection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) {τ : Type} (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state after : FlatState KemSK τ)
    (supported : (none, after) ∈ support
      ((acceptStep setup codec checks publicValue services raw).run state)) :
    after.1.pending = state.1.pending := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  repeat' first
    | (obtain ⟨⟨reply, table⟩, step, supported⟩ := supported)
    | split at supported
    | (simp only [afterDerive, support_pure, Set.mem_singleton_iff, mem_support_bind_iff,
        Prod.mk.injEq] at supported)
  all_goals rfl

/-- An accept changes no pending lookup away from its literal current allocation index. Guessed future handles are not treated as prior occurrences. -/
theorem accept_other (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) {τ : Type} (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Nat × FlatState KemSK τ)
    (supported : result ∈ support ((acceptStep setup codec checks publicValue services raw).run state))
    (index : Nat) (different : index ≠ state.1.sessions) :
    result.2.1.pending index = state.1.pending index :=
  (acceptStep_resources setup codec checks publicValue services raw state result supported).2.2.elim
    (fun unchanged => congrFun unchanged index)
    (fun ⟨token, updated⟩ => by simpa only [Function.update_of_ne different] using congrFun updated index)

/-- Every post-accept token is either exactly an earlier token or was created by this successful callback, with its actual prefix and root-service receipt. -/
theorem pending_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) {τ : Type} (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Nat × FlatState KemSK τ)
    (supported : result ∈ support ((acceptStep setup codec checks publicValue services raw).run state))
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (found : result.2.1.pending index = some token) :
    state.1.pending index = some token ∨
      (index = state.1.sessions ∧ result.1 = some index ∧ ∃ input consumed reply table root,
        (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run state.1.server.consumed) ∧
        (reply, table) ∈ support ((services.derive (PqxdhServerRelatedRootInput.message input)).run state.2.2) ∧
        reply.value = some root ∧ token = ⟨root, PqxdhServerClearedRoot.pending (binding setup publicValue) input⟩ ∧
        Decoded codec raw input.verified ∧
        PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
          input.verified.candidate = some (input.verified.identity, input.verified.keys)) := by
  rcases result with ⟨_ | allocated, after⟩
  · exact Or.inl ((congrFun (accept_rejection setup codec checks publicValue services raw state after supported) index).symm.trans found)
  · by_cases same : index = state.1.sessions
    · obtain ⟨allocatedEq, input, consumed, reply, table, root, collected, derived, rooted, installed, decoded, accepted⟩ :=
        accept_receipt setup codec checks publicValue services raw state allocated after supported
      exact Or.inr ⟨same, congrArg some (allocatedEq.trans same.symm), input, consumed, reply, table, root,
        collected, derived, rooted, Option.some.inj (found.symm.trans
          ((congrArg after.1.pending (same.trans allocatedEq.symm)).trans installed)), decoded, accepted⟩
    · exact Or.inl ((accept_other setup codec checks publicValue services raw state
        (some allocated, after) supported index same).symm.trans found)

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.verify_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.verify_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_fields_or_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.prefix_fields_or_substitution

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_rejection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.accept_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.pending_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt.pending_source
