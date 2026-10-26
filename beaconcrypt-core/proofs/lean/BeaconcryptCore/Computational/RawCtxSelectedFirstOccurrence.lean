import BeaconcryptCore.Computational.RawCtxFirstParentPrefix

/-!
The selected cursor follows global private KDF addresses across all roles. Every executed private request remains in the shared private table, so a missing selected address cannot already occur in the chronological private-request history. After a sender advances the cursor, a paired receiver reusing the old address keeps the same cached full output; it is not a selected cache collision unless the next cursor address itself repeats that address. These are operational facts and do not rule out byte aliases between independently obtained keys.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily
open RawCtxSelectiveFamilyLog (LoggedState)
variable {A Result : Type} {S B : Nat}

def Recorded (state : LoggedState A) : Prop :=
  ∀ address, address ∈ state.2 → ∃ output, state.1.2.1 address = some output

/-- The actual empty chronological history satisfies reverse cache provenance for every retained table. -/
theorem empty_recorded (state : RawCtxPendingSelectiveFamily.State A) :
    Recorded (state, []) := by
  simp [Recorded]

/-- Every actual callback preserves prior request bindings and installs its own binding before recording it. -/
theorem step_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (Spec S B).Domain) (state : LoggedState A) (recorded : Recorded state)
    (result : (Spec S B).Range query × LoggedState A)
    (supported : result ∈ support (((RawCtxSelectiveFamilyLog.handler source writer stage) query).run state)) :
    Recorded result.2 := by
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  intro address occurred
  cases found : RawCtxSelectedFamilyContext.queryAddress query with
  | none =>
      have same := RawCtxPendingNonKdfStore.callback_store source writer stage query found state.1 reply actual
      obtain ⟨output, cached⟩ := recorded address (by simpa only [RawCtxSelectiveFamilyLog.inputs, found] using occurred)
      exact ⟨output, by simpa only [same] using cached⟩
  | some request =>
      obtain ⟨response, exactState⟩ := RawCtxPendingParentCallbacks.kdf_state source writer stage query request found state.1 reply actual
      rw [exactState]
      by_cases same : address = request
      · subst address
        exact ⟨response, by simp⟩
      · have old : address ∈ state.2 := by
          simpa [RawCtxSelectiveFamilyLog.inputs, found, same] using occurred
        obtain ⟨output, cached⟩ := recorded address old
        exact ⟨output, by simpa only [QueryCache.cacheQuery_of_ne (spec := JointKdfRO) state.1.2.1 response same] using cached⟩

/-- The full adaptive live execution retains every globally executed private address. -/
theorem program_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec S B) Result) (state : LoggedState A) (recorded : Recorded state)
    (result : Result × LoggedState A)
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state)) :
    Recorded result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact recorded
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1 reply.2 (step_recorded source writer stage query state recorded reply head) result tail

/-- The complete actual stopped prefix retains reverse provenance, including unselected calls from every owner. -/
theorem scan_recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (Spec S B).Domain → LoggedState A → Bool)
    (client : OracleComp (Spec S B) Result) (state : LoggedState A) (recorded : Recorded state)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec S B) Result (LoggedState A))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (RawCtxSelectiveFamilyLog.handler source writer stage) client state)) : Recorded result.2 := by
  exact RawCtxStatefulPrefixInvariant.scan_valid selected (RawCtxSelectiveFamilyLog.handler source writer stage) Recorded
    (fun query before valid _ reply head => step_recorded source writer stage query before valid reply head)
    client state recorded result supported

/-- A missing address has never occurred in the actual complete private-request history. -/
theorem missing_first (state : LoggedState A) (recorded : Recorded state) (address : JointKdfAddress)
    (missing : state.1.2.1 address = none) : address ∉ state.2 := by
  intro occurred
  obtain ⟨output, cached⟩ := recorded address occurred
  rw [missing] at cached
  cases cached

/-- Selection depends on the full global address, regardless of the owner or send/receive callback class. -/
theorem same_address (depth : Nat) (first second : (Spec S B).Domain) (state : LoggedState A)
    (same : RawCtxSelectedFamilyContext.queryAddress first = RawCtxSelectedFamilyContext.queryAddress second) :
    RawCtxFirstParentPrefix.selected depth first state = RawCtxFirstParentPrefix.selected depth second state := by
  simp only [RawCtxFirstParentPrefix.selected, RawCtxPendingParentCallbacks.parentCut,
    RawCtxFirstParentPrefix.hit, same]

/-- An earlier paired address is unselected after the global cursor moves to a different address. -/
theorem paired_unselected (depth : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (address : JointKdfAddress) (found : RawCtxSelectedFamilyContext.queryAddress query = some address)
    (different : address ≠ cursorAddress state.1.2.2) :
    RawCtxFirstParentPrefix.selected depth query state = false := by
  simp [RawCtxFirstParentPrefix.selected, RawCtxPendingParentCallbacks.parentCut,
    RawCtxFirstParentPrefix.hit, found, matched, different]

/-- A paired send/receive hit retains the entire shared response, table and advanced cursor. Repeated cursor inputs remain a separate branch. -/
theorem paired_hit (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (address : JointKdfAddress) (store : Store) (output : FullOutput)
    (found : store.1 address = some output) (different : address ≠ cursorAddress store.2) :
    privateStep source stage address store = pure (output, store) := by
  rw [private_hit source stage address store output found, cache_hit store.1 address output found]
  simp [advance, matched, different]

end BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.empty_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.empty_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.step_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.step_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.program_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.program_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.scan_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.scan_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.missing_first' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.missing_first

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.same_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.same_address

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.paired_unselected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.paired_unselected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.paired_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFirstOccurrence.paired_hit
