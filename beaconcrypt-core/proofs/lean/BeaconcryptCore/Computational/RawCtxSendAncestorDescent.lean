import BeaconcryptCore.Computational.RawCtxSendPathMeeting

/-!
An actual same-lineage repeated send input descends through equal predecessor inputs until it reaches either the initial root or two distinct inputs with equal next-chain outputs. Retained predecessor retries are kept exactly; they are not misclassified as guesses of the child input. This is deterministic source-path classification, with every endpoint measured on the same retained cache and chronological input list. Probability transfer and cryptographic-origin allocation are separate consuming steps.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSendAncestorDescent
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids PqxdhJointKdfGame
open RawCtxCursorLineage RawCtxKdfRequestTable RawCtxSendPathMeeting

/-- Equal send inputs at strictly increasing positions are traced backwards through actual equal predecessors, ending in a root return or a distinct-input next-chain collision. -/
theorem walk_return (table : Table) (root : RootOutput) (first second : Nat)
    (before after : List RootOutput × RootOutput)
    (ordered : first < second)
    (left : walk table first root = some before)
    (right : walk table second root = some after)
    (same : before.2 = after.2) :
    RootHit table root after.1 ∨ NextCollision table after.1 after.1 := by
  induction first generalizing second before after with
  | zero =>
      have leftEq : ([], root) = before := by simpa [walk] using left
      subst before
      cases second with
      | zero => omega
      | succ second =>
          cases prefixWalk : walk table second root with
          | none => simp [walk, prefixWalk] at right
          | some earlier =>
              cases found : table (RawCtxFirstParentRisk.inputAddress earlier.2) with
              | none => simp [walk, prefixWalk, found] at right
              | some output =>
                  have rightEq : (earlier.1 ++ [earlier.2], nextChain output) = after := by
                    simpa [walk, prefixWalk, found] using right
                  subst after
                  exact Or.inl ⟨earlier.2, by simp, output, found, same.symm⟩
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases firstWalk : walk table first root with
          | none => simp [walk, firstWalk] at left
          | some leftPrefix =>
              cases secondWalk : walk table second root with
              | none => simp [walk, secondWalk] at right
              | some rightPrefix =>
                  cases leftFound : table (RawCtxFirstParentRisk.inputAddress leftPrefix.2) with
                  | none => simp [walk, firstWalk, leftFound] at left
                  | some leftOutput =>
                      cases rightFound : table (RawCtxFirstParentRisk.inputAddress rightPrefix.2) with
                      | none => simp [walk, secondWalk, rightFound] at right
                      | some rightOutput =>
                          have leftEq : (leftPrefix.1 ++ [leftPrefix.2], nextChain leftOutput) = before := by
                            simpa [walk, firstWalk, leftFound] using left
                          have rightEq : (rightPrefix.1 ++ [rightPrefix.2], nextChain rightOutput) = after := by
                            simpa [walk, secondWalk, rightFound] using right
                          subst before after
                          by_cases priorSame : leftPrefix.2 = rightPrefix.2
                          · rcases ih second leftPrefix rightPrefix (by omega) firstWalk secondWalk priorSame with rootReturn | collision
                            · left
                              obtain ⟨input, member, output, found, value⟩ := rootReturn
                              exact ⟨input, List.mem_append_left _ member, output, found, value⟩
                            · right
                              obtain ⟨a, aIn, b, bIn, different, aOut, bOut, aFound, bFound, outputEq⟩ := collision
                              exact ⟨a, List.mem_append_left _ aIn, b, List.mem_append_left _ bIn,
                                different, aOut, bOut, aFound, bFound, outputEq⟩
                          · right
                            have leftMember := RawCtxSendLineageCollision.walk_earlier table first (second + 1)
                              (by omega) root leftPrefix _ firstWalk right
                            exact ⟨leftPrefix.2, leftMember, rightPrefix.2, by simp, priorSame,
                              leftOutput, rightOutput, leftFound, rightFound, same⟩

/-- Every chronological input has a genuine strictly earlier source counter in the same complete walk, including repeated cached inputs. -/
theorem walk_member (table : Table) (root : RootOutput) (steps : Nat)
    (result : List RootOutput × RootOutput) (known : walk table steps root = some result)
    (input : RootOutput) (member : input ∈ result.1) :
    ∃ position < steps, ∃ earlier, walk table position root = some (earlier, input) := by
  induction steps generalizing result with
  | zero =>
      have same : ([], root) = result := by simpa [walk] using known
      subst result
      simp at member
  | succ steps ih =>
      cases previousWalk : walk table steps root with
      | none => simp [walk, previousWalk] at known
      | some previous =>
          cases found : table (RawCtxFirstParentRisk.inputAddress previous.2) with
          | none => simp [walk, previousWalk, found] at known
          | some output =>
              have same : (previous.1 ++ [previous.2], nextChain output) = result := by
                simpa [walk, previousWalk, found] using known
              subst result
              simp only [List.mem_append, List.mem_singleton] at member
              rcases member with old | last
              · obtain ⟨position, smaller, earlier, walked⟩ := ih previous previousWalk old
                exact ⟨position, by omega, earlier, walked⟩
              · subst input
                exact ⟨steps, by omega, previous.1, previousWalk⟩

/-- Every actual cached cycle has a finite source-position witness and descends to a root return or distinct-input next-output collision on that same chronological path. -/
theorem cycle_return (table : Table) (root : RootOutput) (position : Nat)
    (cycle : RawCtxSendLineageCollision.Cycle table root position) :
    ∃ inputs, inputs.length = position ∧
      (RootHit table root inputs ∨ NextCollision table inputs inputs) := by
  obtain ⟨inputs, target, walked, repeated⟩ := cycle
  obtain ⟨first, ordered, earlier, priorWalk⟩ := walk_member table root position (inputs, target) walked target repeated
  exact ⟨inputs, (walk_shape table position root (inputs, target) walked).1,
    walk_return table root first position (earlier, target) (inputs, target) ordered priorWalk walked rfl⟩

open RawCtxPendingSelectiveFamily
variable {M P I D K A Result : Type} {S B : Nat}

/-- Actual admitted send followed by its original same-installation LIVE suffix supplies the descent event, including writer failures and all final cached inputs. -/
theorem source_return (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (first : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (initialState : State A) (initialPath : RawCtxSourceSendPath.Path root first initialState.2.1)
    (active : first.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × State A)
    (sentActual : sent ∈ support ((simulateQ (RawCtxSourceSendPath.sendImpl source writer stage)
      (RawCtxSourceSend.send first context)).run initialState))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some sent.1.1)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry sent.2.1 sent.2.2))
    (later : ConcreteRatchetKernel)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some later)
    (same : first.refined.send_chain = later.refined.send_chain) :
    ∃ inputs, inputs.length = later.refined.control.send_sequence.val ∧
      (RootHit result.2.2.1 root inputs ∨ NextCollision result.2.2.1 inputs inputs) := by
  exact cycle_return result.2.2.1 root later.refined.control.send_sequence.val
    (RawCtxSourceSendOrder.source_cycle source writer stage root first context initialState initialPath active sent sentActual
      selected sender route decode client entry installed result supported later retained same)

end BeaconcryptCore.Computational.RawCtxSendAncestorDescent

/-- info: 'BeaconcryptCore.Computational.RawCtxSendAncestorDescent.walk_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendAncestorDescent.walk_return

/-- info: 'BeaconcryptCore.Computational.RawCtxSendAncestorDescent.walk_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendAncestorDescent.walk_member

/-- info: 'BeaconcryptCore.Computational.RawCtxSendAncestorDescent.cycle_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendAncestorDescent.cycle_return

/-- info: 'BeaconcryptCore.Computational.RawCtxSendAncestorDescent.source_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendAncestorDescent.source_return
