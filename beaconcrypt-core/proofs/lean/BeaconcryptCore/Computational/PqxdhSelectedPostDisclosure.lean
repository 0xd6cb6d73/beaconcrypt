import BeaconcryptCore.Computational.PqxdhSelectedPostCompiler

/-!
Actual hidden-material disclosure remains in the original outer post history through every later selector, attempted registration and record operation. The comparison stops only before returning that unavailable material. Its fresh event equality retains the complete adaptive program and does not constrain an adversary's decision after compromise.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open PqxdhSelectedPostCompiler (Optional SourceState)
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

noncomputable def normal :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (SourceState M P I D K A N C S B) ProbComp) :=
  fun query before => match query with
  | .inl (.inl request) =>
      (fun result => (some result.1, ({ before.1 with roles := result.2.1 }, result.2.2))) <$>
        (RawCtxSelectedMessageStopping.normal
          (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read) key request).run
            (before.1.roles, before.2)
  | query => (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before

def Good (state : SourceState M P I D K A N C S B) : Prop := RawCtxSelectedMessageFreshness.hidden state.1.roles.2 = false

/-- The two concrete source callbacks preserve the same complete state distribution at each request; only a hidden disclosure reply is withheld. -/
theorem step_state (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : SourceState M P I D K A N C S B) :
    Prod.snd <$> (normal pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before =
      Prod.snd <$> (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before := by
  rcases query with (request | request) | request
  · cases request with
    | inl request =>
      simp only [normal, PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
        RawCtxSelectedMessageStopping.normal, RawCtxSelectedMessageStopping.stopping,
        OptionT.run_mk, StateT.run, Functor.map_map]
    | inr request => rfl
  · rfl
  · cases request; rfl

/-- No original outer source operation can remove an earlier hidden-key disclosure, including a later attempted Beacon registration or private selector callback. -/
theorem normal_good (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : SourceState M P I D K A N C S B)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × SourceState M P I D K A N C S B)
    (supported : result ∈ support ((normal pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before))
    (good : Good result.2) : Good before := by
  rcases query with (request | request) | request
  · simp only [normal, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, actual, rfl⟩ := supported
    exact RawCtxSelectedMessageStopping.normal_good
      (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read) key request
      (before.1.roles, before.2) reply actual good
  · simp only [normal, PqxdhSelectedPostCompiler.original, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact good
  · cases request with
    | finish index raw =>
      simp only [normal, PqxdhSelectedPostCompiler.original, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact good

/-- The concrete stopped callback retains the same disclosure evidence even if its caller could continue after the internal stop. -/
theorem original_good (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : SourceState M P I D K A N C S B)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × SourceState M P I D K A N C S B)
    (supported : result ∈ support ((PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before))
    (good : Good result.2) : Good before := by
  have observed : result.2 ∈ support (Prod.snd <$>
      (normal pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before) := by
    rw [step_state pre application initial selector aux source writer prior parent key target nonce next sender route read query before]
    simp only [support_map, Set.mem_image]
    exact ⟨result, supported, rfl⟩
  simp only [support_map, Set.mem_image] at observed
  obtain ⟨reply, actual, same⟩ := observed
  exact normal_good pre application initial selector aux source writer prior parent key target nonce next sender route read query before reply actual (same ▸ good)

noncomputable def handler (stopped : Bool) :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (SourceState M P I D K A N C S B) ProbComp) :=
  if stopped then PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read
  else normal pre application initial selector aux source writer prior parent key target nonce next sender route read

/-- Any complete adaptive outer continuation retains an earlier hidden-key disclosure in either the ordinary or stopped source. -/
theorem schedule_good (stopped : Bool) (work : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : SourceState M P I D K A N C S B) (result : Result × SourceState M P I D K A N C S B)
    (supported : result ∈ support ((simulateQ (handler pre application initial selector aux source writer prior parent key target nonce next sender route read stopped) work).run before))
    (good : Good result.2) : Good before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact good
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, actual, tail⟩ := supported
    have after := ih reply.1 reply.2 tail
    cases stopped with
    | false => exact normal_good pre application initial selector aux source writer prior parent key target nonce next sender route read query before reply actual after
    | true => exact original_good pre application initial selector aux source writer prior parent key target nonce next sender route read query before reply actual after

-- The finite-query source has discrete successful outputs, even when retained fields are arbitrary types.
local instance : MeasurableSpace (Result × SourceState M P I D K A N C S B) := ⊤
local instance : DiscreteMeasurableSpace (Result × SourceState M P I D K A N C S B) := ⟨fun _ => by simp⟩

/-- A previously disclosed hidden key makes every complete output with retained freshness impossible, independently of the final decision. -/
theorem output_bad_zero (stopped : Bool) (work : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : SourceState M P I D K A N C S B) (result : Result × SourceState M P I D K A N C S B)
    (bad : ¬ Good before) (good : Good result.2) :
    𝒟[(simulateQ (handler pre application initial selector aux source writer prior parent key target nonce next sender route read stopped) work).run before] {result} = 0 := by
  rw [← prEvent_eq_evalDist_singleton]
  exact prEvent_eq_zero_of_not_mem_support _ fun supported =>
    bad (schedule_good pre application initial selector aux source writer prior parent key target nonce next sender route read stopped work before result supported good)

noncomputable def Discloses (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : SourceState M P I D K A N C S B) : Prop :=
  match query with
  | .inl (.inl (.inr request)) => RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.roles).1 = none
  | _ => False

/-- Before an actual hidden skipped-key disclosure, the ordinary and stopped outer source return the same complete callback result and poststate. -/
theorem step_agree (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : SourceState M P I D K A N C S B)
    (clear : ¬ Discloses (extra := extra) query before) :
    (normal pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before =
      (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before := by
  rcases query with (request | request) | request
  · cases request with
    | inl request =>
      simp only [normal, PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
        RawCtxSelectedMessageStopping.normal, RawCtxSelectedMessageStopping.stopping,
        OptionT.run_mk, StateT.run, Functor.map_map]
    | inr request =>
      cases emitted : RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.roles).1 with
      | none => exact False.elim (clear emitted)
      | some value =>
        simp only [normal, PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
          RawCtxSelectedMessageStopping.normal, RawCtxSelectedMessageStopping.stopping,
          OptionT.run_mk, StateT.run, map_pure, emitted,
          RawCtxSelectedMessageReveals.emit_exact key request _ value emitted]
  · rfl
  · cases request; rfl

noncomputable def afterRead (request : RawCtxProtocolReveals.Request S B) (before : SourceState M P I D K A N C S B) : SourceState M P I D K A N C S B :=
  ({ before.1 with roles := (RawCtxSelectedMessageReveals.step request before.1.roles).2 }, before.2)

private theorem discloses_shape (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : SourceState M P I D K A N C S B) (disclosed : Discloses (extra := extra) query before) :
    ∃ request, query = .inl (.inl (.inr request)) ∧ RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.roles).1 = none := by
  rcases query with ((request | request) | request) | request
  · exact False.elim disclosed
  · exact ⟨request, rfl, disclosed⟩
  · exact False.elim disclosed
  · cases request
    exact False.elim disclosed

/-- The exact withheld source read itself records hidden disclosure in the full outer state; missing and known-key replies do not satisfy this premise. -/
theorem disclosed_bad (request : RawCtxProtocolReveals.Request S B) (before : SourceState M P I D K A N C S B)
    (disclosed : RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.roles).1 = none) :
    ¬ Good (afterRead request before) := by
  have hidden := (RawCtxSelectedMessageReveals.stopped_iff request (RawCtxSelectedMessageReveals.step request before.1.roles).1).mp disclosed
  change RawCtxSelectedMessageFreshness.hiddenObservation ⟨request, RawCtxSelectedMessageReveals.selectedReply request before.1.roles.1⟩ = true at hidden
  simp only [Good, afterRead, RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageFreshness.hidden_note,
    hidden, Bool.or_true, Bool.true_eq_false, not_false_eq_true]

private theorem normal_read (request : RawCtxProtocolReveals.Request S B) (before : SourceState M P I D K A N C S B) :
    (normal pre application initial selector aux source writer prior parent key target nonce next sender route read (.inl (.inl (.inr request)))).run before =
      pure (some (RawCtxSelectedMessageReveals.interpretReply key request (RawCtxSelectedMessageReveals.step request before.1.roles).1), afterRead request before) := by
  simp only [normal, RawCtxSelectedMessageStopping.normal, StateT.run, map_pure, afterRead]

private theorem original_read (request : RawCtxProtocolReveals.Request S B) (before : SourceState M P I D K A N C S B) :
    (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read (.inl (.inl (.inr request)))).run before =
      pure (RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.roles).1, afterRead request before) := by
  simp only [PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
    RawCtxSelectedMessageStopping.stopping, OptionT.run_mk, StateT.run, map_pure, afterRead]

/-- The complete outer source and hidden-disclosure-stopped source assign the same probability to every full fresh output, for any adaptive continuation. -/
theorem output_good (work : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : SourceState M P I D K A N C S B) (result : Result × SourceState M P I D K A N C S B)
    (good : Good result.2) :
    𝒟[(simulateQ (normal pre application initial selector aux source writer prior parent key target nonce next sender route read) work).run before] {result} =
      𝒟[(simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read) work).run before] {result} := by
  classical
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases clear : ¬ Discloses (extra := extra) query before
    · rw [step_agree pre application initial selector aux source writer prior parent key target nonce next sender route read query before clear]
      rw [← prEvent_eq_evalDist_singleton _ result, ← prEvent_eq_evalDist_singleton _ result,
        OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply tsum_congr
      intro reply
      have same := ih reply.1 reply.2
      rw [← prEvent_eq_evalDist_singleton _ result, ← prEvent_eq_evalDist_singleton _ result] at same
      rw [same]
    · obtain ⟨request, rfl, disclosed⟩ := discloses_shape query before (not_not.mp clear)
      rw [normal_read pre application initial selector aux source writer prior parent key target nonce next sender route read request before,
        original_read pre application initial selector aux source writer prior parent key target nonce next sender route read request before]
      simp only [pure_bind, disclosed]
      have bad := disclosed_bad request before disclosed
      exact (output_bad_zero pre application initial selector aux source writer prior parent key target nonce next sender route read false
        (continuation (some (RawCtxSelectedMessageReveals.interpretReply key request (RawCtxSelectedMessageReveals.step request before.1.roles).1)))
        (afterRead request before) result bad good).trans
          (output_bad_zero pre application initial selector aux source writer prior parent key target nonce next sender route read true
            (continuation none) (afterRead request before) result bad good).symm

/-- Every final event gated by the actual retained disclosure history has equal probability in the complete ordinary and stopped outer source. -/
theorem event_good (work : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : SourceState M P I D K A N C S B) (event : Result × SourceState M P I D K A N C S B → Prop) :
    𝒟[(simulateQ (normal pre application initial selector aux source writer prior parent key target nonce next sender route read) work).run before] {result | event result ∧ Good result.2} =
      𝒟[(simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read) work).run before] {result | event result ∧ Good result.2} := by
  classical
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, OracleComp.prEvent_eq_tsum_ite,
    OracleComp.prEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases good : Good result.2
  · simp only [good, and_true]
    have same := output_good pre application initial selector aux source writer prior parent key target nonce next sender route read work before result good
    rw [← prEvent_eq_evalDist_singleton _ result, ← prEvent_eq_evalDist_singleton _ result] at same
    rw [same]
  · simp only [good, and_false, ite_false]

/-- The original byte-based selected-material freshness event already excludes every withheld disclosure across the full outer schedule. Stopping therefore adds zero error without constraining any final decision on compromised executions. -/
theorem event_fresh (remaining known : List RatchetChain)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : SourceState M P I D K A N C S B) (event : Option Result × SourceState M P I D K A N C S B → Prop) :
    𝒟[(simulateQ (normal pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before] {result | event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) known
        (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.roles.2)} =
      𝒟[(simulateQ (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender route read)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before] {result | event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) known
          (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.roles.2)} := by
  have factor : (fun result : Option Result × SourceState M P I D K A N C S B =>
      (event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) known
        (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.roles.2)) ∧ Good result.2) =
      (fun result => event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) known
        (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.roles.2)) := by
    funext result
    apply propext
    exact ⟨And.left, fun h => ⟨h, ((RawCtxSelectedMessageFreshness.fresh_keys key remaining known result.2.1.roles.2).mp h.2).1.1⟩⟩
  simpa only [factor] using event_good pre application initial selector aux source writer prior parent key target nonce next sender route read
    (RawCtxSelectedFamilyNonceCoupling.optionalClient work) before
    (fun result => event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) known
      (RawCtxSelectedMessageFreshness.interpretHistory key result.2.1.roles.2))

end BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.step_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.step_state
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.normal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.normal_good
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.original_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.original_good
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.schedule_good
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.output_bad_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.output_bad_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.step_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.step_agree
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.disclosed_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.disclosed_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.output_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.output_good
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.event_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.event_fresh
