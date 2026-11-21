-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptLedger

/-! Exact receipt properties of the actual complete signing block, before either writer outcome. The one-time draw, all private/native return fields and each creation index's chronological transcript remain in the same source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhRegistrationJointIssuedAttempts (Fixed history)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointAttemptTrace (LiveFixed NativeResult)
open PqxdhRegistrationJointAttemptLedger (Receipt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The exact source result retains all seeds, the immutable receipt fields, and its complete per-index signing history. -/
def Good (setup : Setup baseSpec KemSK) (index : Nat) (receipt : Receipt)
    (pool : PqxdhDynamicIdentityPool.SourceState) (result : NativeResult KemSK × List Phase1KeyTuple) : Prop :=
  result.1.2.seeds = pool.seeds ∧ Fixed receipt.prekey receipt.pqKey result.2 ∧
    LiveFixed setup result.1.1.2 receipt.prekey receipt.pqKey ∧
    ∀ selected, messagesAt selected result.1.2.transcript =
      if selected = index then history result.2 else messagesAt selected pool.transcript

/-- The prepared signing block updates the actual receipt before serialization; rejection retains its three signatures just like successful publication. -/
theorem after_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (receipt : Receipt)
    (fixed : Fixed receipt.prekey receipt.pqKey receipt.attempts)
    (live : LiveFixed setup owner receipt.prekey receipt.pqKey)
    (exactLog : messagesAt index pool.transcript = history receipt.attempts) :
    Good setup index receipt pool
      (PqxdhRegistrationJointAttemptTrace.after setup codec index owner generated pool receipt.attempts) := by
  refine ⟨PqxdhRegistrationJointBundle.after_seeds setup codec index owner generated pool,
    PqxdhRegistrationJointAttemptTrace.after_fixed setup codec index owner generated pool receipt.attempts _ _ fixed live, ?_, ?_⟩
  · intro actual present
    exact live actual ((PqxdhRegistrationJointAttemptTrace.after_basis setup codec index owner generated pool).symm.trans present)
  · intro selected
    by_cases same : selected = index
    · subst selected
      simpa using PqxdhRegistrationJointSigningTranscript.attempt_after setup codec index owner generated pool receipt.attempts exactLog
    · simpa only [ite_eq_right same, PqxdhRegistrationJointAttemptTrace.after] using PqxdhRegistrationJointSigningTranscript.attempt_other setup codec index selected owner generated pool (Ne.symm same)

/-- Every result of the actual one-time sampler and writer has the full receipt property; inactive branches retain the exact previous state and attempts. -/
theorem trace_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) (receipt : Receipt)
    (fixed : Fixed receipt.prekey receipt.pqKey receipt.attempts)
    (live : LiveFixed setup owner receipt.prekey receipt.pqKey)
    (exactLog : messagesAt index pool.transcript = history receipt.attempts)
    (result : NativeResult KemSK × List Phase1KeyTuple)
    (supported : result ∈ support (PqxdhRegistrationJointAttemptTrace.trace setup codec index owner pool receipt.attempts)) :
    Good setup index receipt pool result := by
  cases phase : owner.beacon.phase <;>
    simp only [PqxdhRegistrationJointAttemptTrace.trace, phase, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case fresh =>
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after_good setup codec index owner (some scalar) pool receipt fixed live exactLog
  all_goals subst result
  case freshWithCoins => exact after_good setup codec index owner none pool receipt fixed live exactLog
  all_goals refine ⟨rfl, fixed, live, ?_⟩
  all_goals intro selected; by_cases same : selected = index <;> simp [same, exactLog]

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties.after_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties.after_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties.trace_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties.trace_good
