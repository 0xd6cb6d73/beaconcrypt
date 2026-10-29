-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo
import BeaconcryptCore.Computational.RegistrationNativePublicRootFrame

/-! The actual private source interpretation preserves every prepared source root through arbitrary mixed-client interleavings. This functional invariant includes failed preparation and repeated literal descriptors, so native live-token material demand need not assume an external cache receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State M handler)
open RegistrationNativePublicSourceEffects (close)
open RegistrationNativePublicSourceState (MemoCorrect)
open RegistrationNativePublicRootFrame (replace)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem close_roots_kept (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : M n KemSK Value)
    (framed : ∀ memo before, Prod.map id (replace memo) <$> work.run before = work.run (replace memo before))
    (before : State n KemSK) (result : Value × State n KemSK)
    (supported : result ∈ support ((close setup seed scalar work).run before)) : result.2.roots = before.roots := by
  have same := congrArg (simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar))
    (framed before.roots before)
  rw [simulateQ_map] at same
  have restored : replace before.roots before = before := rfl
  rw [restored] at same
  change Prod.map id (replace before.roots) <$> (close setup seed scalar work).run before =
    (close setup seed scalar work).run before at same
  rw [← same, support_map] at supported
  obtain ⟨inner, _possible, equal⟩ := supported
  exact (congrArg (fun output : Value × State n KemSK => output.2.roots) equal).symm

private theorem ordinary_stable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : M n KemSK Value)
    (framed : ∀ memo before, Prod.map id (replace memo) <$> work.run before = work.run (replace memo before))
    (before : State n KemSK) (result : Value × State n KemSK)
    (correct : MemoCorrect setup seed scalar before.roots)
    (supported : result ∈ support ((close setup seed scalar work).run before)) :
    MemoCorrect setup seed scalar result.2.roots ∧
      ∀ message root, before.roots message = some root → result.2.roots message = some root := by
  have equal := close_roots_kept setup seed scalar work framed before result supported
  rw [equal]
  exact ⟨correct, fun _ _ stored => stored⟩

/-- Every native source callback preserves all earlier prepared roots and exact source correctness, including failed preparations. -/
theorem query_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK) (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK)
    (correct : MemoCorrect setup seed scalar before.roots)
    (supported : result ∈ support ((close setup seed scalar (handler setup wire route sign query)).run before)) :
    MemoCorrect setup seed scalar result.2.roots ∧
      ∀ message root, before.roots message = some root → result.2.roots message = some root := by
  cases query with
  | inl query => cases query with
    | inl message =>
        have actual : (close setup seed scalar (handler setup wire route sign (.inl (.inl message)))).run before =
            pure ((RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message).map (fun _ => message),
              { before with roots := (Function.update before.roots message
                (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message)) }) := by
          simp only [handler,
            ]
          rfl
        rw [actual, mem_support_pure_iff] at supported
        subst result
        exact ⟨RegistrationNativePublicSourceMemo.update_correct setup seed scalar before.roots correct message,
          RegistrationNativePublicSourceMemo.update_keeps setup seed scalar before.roots correct message⟩
    | inr query => cases query with
      | inl query => cases query with
        | inl message =>
            have actual : (close setup seed scalar (handler setup wire route sign (.inl (.inr (.inl (.inl message)))))).run before =
                pure ((before.roots message).map (fun root => RegistrationNativePairedChoice.Choice.known
                  (PqxdhServerAuthKeySchedule.fromRoot setup.source root)), before) := by
              simp only [handler]
              rfl
            rw [actual, mem_support_pure_iff] at supported
            subst result
            exact ⟨correct, fun _ _ stored => stored⟩
        | inr query =>
            exact ordinary_stable setup seed scalar _
              (fun memo state => RegistrationNativePublicRootFrame.common_replace setup wire sign memo query state)
              before result correct supported
      | inr query =>
          exact ordinary_stable setup seed scalar _
            (fun memo state => RegistrationNativePublicRootFrame.routed_replace setup memo query state)
            before result correct supported
  | inr query =>
      exact ordinary_stable setup seed scalar _
        (fun memo state => RegistrationNativePublicRootFrame.world_replace memo _ state)
        before result correct supported

/-- Entire adaptive mixed-client source programs retain all earlier prepared root receipts. -/
theorem program_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (correct : MemoCorrect setup seed scalar before.roots)
    (supported : result ∈ support ((close setup seed scalar (simulateQ (handler setup wire route sign) work)).run before)) :
    MemoCorrect setup seed scalar result.2.roots ∧
      ∀ message root, before.roots message = some root → result.2.roots message = some root := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      change result ∈ support (pure (output, before)) at supported
      rw [mem_support_pure_iff] at supported
      subst result
      exact ⟨correct, fun _ _ stored => stored⟩
  | query_bind query next ih =>
      have split : (close setup seed scalar (simulateQ (handler setup wire route sign)
          (((RegistrationNativePublicFrontend.Spec n KemSK).query query :
            OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) >>= next))).run before = (do
          let step ← (close setup seed scalar (handler setup wire route sign query)).run before
          (close setup seed scalar (simulateQ (handler setup wire route sign) (next step.1))).run step.2) := by
        simp only [close, simulateQ_bind, simulateQ_spec_query, StateT.run,
          StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      rw [split, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨firstCorrect, firstKeeps⟩ := query_stable setup wire route sign seed scalar query before step correct reached
      obtain ⟨lastCorrect, lastKeeps⟩ := ih step.1 step.2 result firstCorrect tail
      exact ⟨lastCorrect, fun message root stored => lastKeeps message root (firstKeeps message root stored)⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence.query_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence.query_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence.program_stable
