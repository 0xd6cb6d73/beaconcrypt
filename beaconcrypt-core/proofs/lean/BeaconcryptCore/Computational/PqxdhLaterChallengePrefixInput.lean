import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog

/-! Earlier successful challenges in the original adaptive wrapper contribute their actual pre-send input to the same reached source log. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput
open PqxdhFirstRecordConfidentiality (ConfPostSpec AdvSpec)
open PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace
open RawCtxProtocolReveals (Owner)
variable {ι A Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A challenge already chosen at an earlier wrapper state retains its successful target reply whenever the later original wrapper target holds. -/
theorem kept_target (number : Std.U64) (before after : State)
    (retained : Kept before after) (chosen : before.pair.isSome) (target : Target number after) :
    Target number before := by
  exact ⟨chosen, by simpa only [(retained.1 chosen).2] using target.2.1, retained.2 target.2.2⟩

/-- The same wrapper prefix contains an actual successful challenge and its full reached suffix, before the current saved callback. -/
def Earlier (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before current : State) (ambient after : A) : Prop :=
  ∃ (left right : Pqxdh.Bytes) (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
      (prior : State) (source sentAfter : A) (record : RawCtxSourceSend.Encrypted),
    Reaches impl owner number bit client before ambient ((AdvSpec extra S B).query (.inr (left, right)) >>= next) prior source ∧
      prior.pair = none ∧ left.length = right.length ∧ prior.otherTarget = false ∧
      (some record, sentAfter) ∈ support ((simulateQ impl (send owner (if bit then right else left))).run source) ∧
      Reaches impl owner number bit (next (some record))
        { prior with pair := some (left, right), reply := some (some record) } sentAfter rest current after ∧
      record.sequence = number

/-- A reached target after the literal unused wrapper state has an earlier actual successful challenge, with both portions of the original adaptive prefix retained. -/
theorem reaches_earlier {impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp)}
    {owner : Owner S B} {number : Std.U64} {bit : Bool}
    {client rest : OracleComp (AdvSpec extra S B) Result}
    {before current : State} {ambient after : A}
    (reached : Reaches impl owner number bit client before ambient rest current after)
    (unused : before.pair = none) (target : Target number current) :
    Earlier impl owner number bit client rest before current ambient after := by
  induction reached with
  | here client before ambient =>
      simp only [Target, unused, Option.isSome_none, Bool.false_eq_true, false_and] at target
  | later query next before ambient step rest current after actual tail ih =>
      have extend : Earlier impl owner number bit (next step.1.1) rest step.1.2 current step.2 after →
          Earlier impl owner number bit ((AdvSpec extra S B).query query >>= next) rest before current ambient after :=
        fun ⟨left, right, continuation, prior, source, sentAfter, record, reached, remaining⟩ =>
          ⟨left, right, continuation, prior, source, sentAfter, record,
            .later query next before ambient step _ prior source actual reached, remaining⟩
      rcases query with request | ⟨left, right⟩
      · refine extend (ih ?_ target)
        have forwarded : (handler (extra := extra) owner number bit (.inl request)).run before =
            (fun reply => (screen before request reply, observe owner number before request reply)) <$>
              ((ConfPostSpec extra S B).query request : OracleComp (ConfPostSpec extra S B) _) := by
          simp only [handler, StateT.run, bind_pure_comp]
        rw [forwarded, simulateQ_map, StateT.run_map, support_map] at actual
        obtain ⟨reply, _, rfl⟩ := actual
        exact unused
      · by_cases equal : left.length = right.length
        · rw [challenge_step owner number bit left right equal before unused] at actual
          simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at actual
          obtain ⟨⟨reply, sentAfter⟩, sent, rfl⟩ := actual
          have kept := PqxdhLaterChallengePaths.reaches_kept impl owner number bit _ _ _ _ _ _ tail
          obtain ⟨record, returned, sequence⟩ := target.2.1
          rw [(kept.1 (by rfl)).2] at returned
          have same : reply = some record := Option.some.inj returned
          subst reply
          exact ⟨left, right, next, before, ambient, sentAfter, record, .here _ before ambient,
            unused, equal, kept.2 target.2.2, sent, tail, sequence⟩
        · have refused : (handler (extra := extra) owner number bit (.inr (left, right))).run before =
              Pure.pure ((none : Option RawCtxSourceSend.Encrypted), before) := by
            simp only [handler, StateT.run, equal, ne_eq, not_false_eq_true, or_true, ite_true]
          rw [refused, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
          subst step
          exact extend (ih unused target)

section Source
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

variable {M P Origin : Type}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Full" => (PqxdhInitialPendingPost.Front RatchetChain M P I D K S B ×
  PqxdhInitialOriginPost.Trace Origin S B) × Backend
local notation "postImpl" => PqxdhLaterChallengeCutChronology.postImpl mark sender route decode impl


/-- The actual earlier challenge and both original prefix pieces, with its pre-send input retained in a specified chronological log. -/
def InputBefore (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before current : PqxdhRecordConfidentialityChallenge.State) (ambient after : Full)
    (inputs : List JointKdfAddress) : Prop :=
    ∃ (left right : Pqxdh.Bytes) (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
        (prior : PqxdhRecordConfidentialityChallenge.State) (requestState sentAfter : Full)
        (record : RawCtxSourceSend.Encrypted) (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain),
      Reaches postImpl owner number bit client before ambient
        ((AdvSpec extra S B).query (.inr (left, right)) >>= next) prior requestState ∧
      prior.pair = none ∧ left.length = right.length ∧ prior.otherTarget = false ∧
      (some record, sentAfter) ∈ support
        ((simulateQ postImpl (send owner (if bit then right else left))).run requestState) ∧
      Reaches postImpl owner number bit (next (some record))
        { prior with pair := some (left, right), reply := some (some record) } sentAfter rest current after ∧
      record.sequence = number ∧
      RawCtxGenericRoleFamily.selectedKernel owner requestState.1.1.roles.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ inputs

/-- The actual earlier challenge's pre-send kernel contributes its input to the log at the reached callback, after every intervening original source operation. -/
theorem earlier_input (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before current : PqxdhRecordConfidentialityChallenge.State) (ambient after : Full)
    (earlier : Earlier postImpl owner number bit client rest before current ambient after) :
    ∃ (left right : Pqxdh.Bytes) (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
        (prior : PqxdhRecordConfidentialityChallenge.State) (requestState sentAfter : Full)
        (record : RawCtxSourceSend.Encrypted) (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain),
      Reaches postImpl owner number bit client before ambient
        ((AdvSpec extra S B).query (.inr (left, right)) >>= next) prior requestState ∧
      prior.pair = none ∧ left.length = right.length ∧ prior.otherTarget = false ∧
      (some record, sentAfter) ∈ support
        ((simulateQ postImpl (send owner (if bit then right else left))).run requestState) ∧
      Reaches postImpl owner number bit (next (some record))
        { prior with pair := some (left, right), reply := some (some record) } sentAfter rest current after ∧
      record.sequence = number ∧
      RawCtxGenericRoleFamily.selectedKernel owner requestState.1.1.roles.1 = some kernel ∧
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain ∈ after.2.1.1.2 := by
  rcases earlier with ⟨left, right, next, prior, requestState, sentAfter, record,
    priorReached, unused, equal, clean, sent, suffix, sequence⟩
  obtain ⟨kernel, selected, member⟩ := PqxdhLaterChallengeSendLog.challenge_input
    source writer stage pre application initial selector aux mark sender route decode
    owner (if bit then right else left) requestState sentAfter record sent
  have retained := PqxdhLaterChallengePrefixLog.reaches_monotone
    source writer stage pre application initial selector aux mark sender route decode
    owner number bit _ _ _ _ sentAfter after suffix
  exact ⟨left, right, next, prior, requestState, sentAfter, record, kernel,
    priorReached, unused, equal, clean, sent, suffix, sequence, selected, retained member⟩

/-- The actual callback-local scan retains an earlier successful challenge input at its saved unexecuted request. No freshness or separation is assumed. -/
theorem pending_input {Tag Value : Type}
    (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (before current : PqxdhRecordConfidentialityChallenge.State) (ambient after : Full)
    (reached : Reaches postImpl owner number bit client before ambient rest current after)
    (unused : before.pair = none) (target : Target number current)
    (privateQuery : (Spec).Domain → Bool) (selected : (Spec).Domain → Backend → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (frame : Tag → RawCtxForwardAnnotation.Frame Spec Value)
    (work : OracleComp (RawCtxForwardAnnotation.Spec Tag Spec) Value)
    (covered : RawCtxForwardCoverage.Covered privateQuery work)
    (sound : RawCtxForwardAnnotation.Sound frame work)
    (saved : Backend) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag saved ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection impl work covered after.2)) :
    InputBefore source writer stage pre application initial selector aux mark sender route decode
      owner number bit client rest before current ambient after saved.1.1.2 := by
  obtain ⟨left, right, next, prior, requestState, sentAfter, record, kernel,
    priorReached, unusedPrior, equal, clean, sent, suffix, sequence, selectedKernel, member⟩ :=
      earlier_input source writer stage pre application initial selector aux mark sender route decode
        owner number bit client rest before current ambient after (reaches_earlier reached unused target)
  have retained := PqxdhLaterChallengeInputLog.pending_monotone
    source writer stage pre application initial selector aux privateQuery selected selection frame
    work covered sound after.2 saved tag supported
  exact ⟨left, right, next, prior, requestState, sentAfter, record, kernel,
    priorReached, unusedPrior, equal, clean, sent, suffix, sequence, selectedKernel, retained member⟩

end Source

end BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.kept_target' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.kept_target
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.reaches_earlier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.reaches_earlier
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.earlier_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.earlier_input
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.pending_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput.pending_input
