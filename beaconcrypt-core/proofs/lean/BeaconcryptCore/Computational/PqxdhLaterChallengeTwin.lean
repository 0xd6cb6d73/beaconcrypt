-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy
import BeaconcryptCore.Computational.PqxdhLaterChallengeAddress

/-! The literal later challenge uses the complete retained-parent Post compiler and its original private transcript. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeTwin
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)

/-- The literal challenge send interpreted by the unchanged complete instrumented Post compiler. -/
noncomputable def send (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before : InsState M P I D K A N C S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option (Option RawCtxSourceSend.Encrypted) × InsState M P I D K A N C S B) :=
  ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next
    sender route read mark monitor) (PqxdhRecordConfidentialityChallenge.send owner plaintext)).run).run before

set_option backward.isDefEq.respectTransparency false in
/-- The original private publication transcript and both instrumentation flags accompany the complete two-plaintext send relation, for either owner at its reached selected input. -/
theorem send_twin (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (owner : RawCtxProtocolReveals.Owner S B) (before : InsState M P I D K A N C S B)
    (selected : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (send pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner left before)
      (send pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner right before) := by
  have live := PqxdhLaterFamilySendPrivacy.live_twin left right equal source writer prior parent target nonce next read
    sender route owner before.1.1.roles selected separate
  cases owner
  all_goals simp only [send, PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest,
    simulateQ_spec_query, insImpl, OptionT.run_mk, StateT.run]
  all_goals refine twin_map left right live _ _ ?_ (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  all_goals intro a b same
  all_goals subst b
  all_goals rcases a with ⟨_ | (_ | record), front⟩
  all_goals cases before.2.2.1 <;> rfl

/-- The literal later wrapper composed with the complete existing instrumented Post interpreter. -/
noncomputable def handler (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (PqxdhFirstRecordConfidentiality.AdvSpec extra S B)
      (Stepper PqxdhRecordConfidentialityChallenge.State (InsState M P I D K A N C S B)) :=
  fun query current => simulateQ
    (insImpl pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor)
    ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current)

set_option backward.isDefEq.respectTransparency false in
/-- An admitted challenge executes its original send and retains the actual optional reply, old competing-publication flag and full instrumented state, including outer refusal. -/
theorem challenge_run (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B) :
    runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
      monitor owner number bit (.inr (left, right))) current before =
    (fun result => (result.1.map (fun reply =>
      (reply, { current with pair := some (left, right), reply := some reply })), result.2)) <$>
      send pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner (if bit then right else left) before := by
  have step := PqxdhRecordConfidentialityChallenge.challenge_step (extra := extra) owner number bit left right equal current unused
  simp only [StateT.run] at step
  simp only [runStepper, handler, StateT.run, send]
  rw [step]
  simp only [simulateQ_map, OptionT.run_map]
  exact StateT.run_map _ _ _

/-- The actual accepted challenge step is twin in either direction at its reached selected input. Its returned wrapper stores the literal challenge pair while retaining all old publication observations. -/
theorem challenge_twin (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B)
    (selected : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b ∧ ∀ reply after, a.1 = some (reply, after) → after.pair = some (left, right))
      (fun _ => False) (fun _ => False)
      (runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number false (.inr (left, right))) current before)
      (runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number true (.inr (left, right))) current before) := by
  rw [challenge_run pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number false left right equal current unused before,
    challenge_run pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number true left right equal current unused before]
  refine twin_map left right
    (send_twin pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      left right equal owner before selected separate) _ _ ?_ (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  rintro a _ rfl
  refine ⟨rfl, ?_⟩
  intro reply after returned
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at returned
  obtain ⟨value, _, _, rfl⟩ := returned
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The composed handler runs exactly the original whole wrapper program under the existing Post interpreter. Every source reply selects the same continuation, and outer refusal retains its full state. -/
theorem program (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    {Result : Type} (work : OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) :
    simulateQ (insImpl (P := P) pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor)
      ((simulateQ (PqxdhRecordConfidentialityChallenge.handler owner number bit) work).run current) =
    (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit) work).run current := by
  induction work using OracleComp.inductionOn generalizing current with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change _ = simulateQ _ ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) >>= _
    exact bind_congr fun result => ih result.1 result.2

/-- The literal later Post endpoint is exactly the composed optional run with its original target decision. No common, cached, competing-publication or failed-challenge outcome is replaced. -/
theorem post_run {Selection : Type}
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (selection : Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (before : InsState M P I D K A N C S B) :
    ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor)
      (PqxdhRecordConfidentialityChallenge.post adversary owner number bit selection reply)).run).run before =
    (fun result => (result.1.map (PqxdhRecordConfidentialityChallenge.output number), result.2)) <$>
      runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number bit) (adversary selection reply)) PqxdhRecordConfidentialityChallenge.initial before := by
  unfold PqxdhRecordConfidentialityChallenge.post
  rw [simulateQ_map, program]
  simp only [runStepper, OptionT.run_map, StateT.run_map]

end BeaconcryptCore.Computational.PqxdhLaterChallengeTwin

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.send_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.send_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.challenge_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.challenge_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.challenge_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.challenge_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.program
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.post_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeTwin.post_run
