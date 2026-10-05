import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedChronology

/-! The original audited source retains every executed private input up to the captured callback. Unexecuted saved requests are not added to the prior history. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
local notation "Spec" => PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B
local notation "Backend" => PqxdhInitialNativeAudit.State A N C
local notation "impl" => PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage pre application initial selector aux

/-- The full concrete callback appends exactly its original executed private input; all other callbacks preserve the list while retaining their complete native effects. -/
theorem query_inputs (query : (Spec).Domain) (before : Backend) (result : (Spec).Range query × Backend)
    (supported : result ∈ support ((impl query).run before)) :
    result.2.1.1.2 = PqxdhInitialNativeLog.inputs query before.1.1.2 := by
  have erased : (result.1, result.2.1) ∈ support
      ((PqxdhInitialNativeLog.handler source writer stage
        (PqxdhInitialNativeAudit.external pre application initial selector aux) query).run before.1) := by
    rw [← PqxdhInitialNativeAudit.query_erase source writer stage pre application initial selector aux, support_map]
    exact ⟨result, supported, rfl⟩
  simp only [PqxdhInitialNativeLog.handler, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at erased
  obtain ⟨reply, _, same⟩ := erased
  exact congrArg (fun value => value.2.1.2) same

/-- Every earlier executed input survives the complete concrete callback, including external initialization and failed record work. -/
theorem query_monotone (query : (Spec).Domain) (before : Backend) (result : (Spec).Range query × Backend)
    (supported : result ∈ support ((impl query).run before)) :
    before.1.1.2 ⊆ result.2.1.1.2 := by
  rw [query_inputs source writer stage pre application initial selector aux query before result supported]
  cases query with
  | inl query =>
      cases found : RawCtxSelectedFamilyContext.queryAddress query <;>
        simp [PqxdhInitialNativeLog.inputs, RawCtxSelectiveFamilyLog.inputs, found]
  | inr query =>
      exact List.Subset.refl _

/-- Every original executed private input survives the full adaptive source computation, including arbitrary later replies and callback effects. -/
theorem program_monotone (work : OracleComp Spec Result) (before : Backend) (result : Result × Backend)
    (supported : result ∈ support ((simulateQ impl work).run before)) :
    before.1.1.2 ⊆ result.2.1.1.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using
        supported ▸ List.Subset.refl before.1.1.2
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      exact supported.elim fun reply evidence =>
        List.Subset.trans (query_monotone source writer stage pre application initial selector aux query before reply evidence.1)
          (ih reply.1 reply.2 result evidence.2)

/-- The saved unexecuted request retains every earlier source input. The scanner's concrete carried frame and exact full backend are preserved. -/
theorem pending_monotone {Tag : Type}
    (privateQuery : (Spec).Domain → Bool) (selected : (Spec).Domain → Backend → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (frame : Tag → RawCtxForwardAnnotation.Frame Spec Result)
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag Spec) Result)
    (covered : RawCtxForwardCoverage.Covered privateQuery work)
    (sound : RawCtxForwardAnnotation.Sound frame work)
    (before after : Backend) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag after ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection impl work covered before)) :
    before.1.1.2 ⊆ after.1.1.2 := by
  apply RawCtxStatefulPrefixInvariant.scan_valid selected impl
    (fun state => before.1.1.2 ⊆ state.1.1.2)
    (fun query current valid _ reply head => List.Subset.trans valid
      (query_monotone source writer stage pre application initial selector aux query current reply head))
    (simulateQ RawCtxForwardAnnotation.erase work) before (List.Subset.refl _)
    (RawCtxForwardScan.pack frame (.pending tag after))
  rw [← RawCtxForwardScan.scan_pack privateQuery selected selection impl frame work covered sound before, support_map]
  exact ⟨.pending tag after, supported, rfl⟩

/-- Every successful original send has executed and recorded the exact KDF input of its pre-send kernel. Optional sealing and writer effects remain in the source computation. -/
theorem send_inputs (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (context : RawCtxSourceSend.SealContext) (before : Backend)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × Backend)
    (supported : result ∈ support ((simulateQ impl
      (simulateQ PqxdhInitialPendingPost.primitiveForward (RawCtxPendingOwnerQueries.calls.send kernel context))).run before))
    (record : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some record) :
    RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ result.2.1.1.2 := by
  rcases PqxdhFirstRecordStopTagged.send_begin kernel context with ⟨other, exhausted⟩ | ⟨pending, started, entryEq, requestEq⟩
  · simp only [RawCtxPendingOwnerQueries.calls, exhausted, RawCtxPendingOwnerQueries.sendProgram,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases returned
  · simp only [RawCtxPendingOwnerQueries.calls, started, RawCtxPendingOwnerQueries.sendProgram,
      simulateQ_bind, simulateQ_spec_query, RawCtxPendingOwnerQueries.sendForward,
      PqxdhInitialPendingPost.primitiveForward, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨derived, first, sealed, second, rfl⟩ := supported
    apply query_monotone source writer stage pre application initial selector aux _ _ _ second
    rw [query_inputs source writer stage pre application initial selector aux _ _ _ first]
    simp [PqxdhInitialNativeLog.inputs, RawCtxSelectiveFamilyLog.inputs,
      RawCtxSelectedFamilyContext.queryAddress, RawCtxSelectedFamilyContext.primitiveAddress, requestEq]

end BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.query_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.query_inputs
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.query_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.query_monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.program_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.program_monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.pending_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.pending_monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.send_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInputLog.send_inputs
