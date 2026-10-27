import BeaconcryptCore.Computational.RawCtxSourceSendOrder

/-!
A meeting of two source send paths is classified on their actual shared cache. Equal initial chains remain an explicit case. Otherwise one reached output hits the other initial chain, or two distinct reached inputs have equal next-chain outputs. No injectivity, independent-key premise, or probability bound is assumed. The lists retain actual chronological inputs, so repeated cache hits are not silently removed from later query accounting.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSendPathMeeting
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxCursorLineage RawCtxKdfRequestTable RawCtxFirstParentRisk

def RootHit (table : Table) (root : RootOutput) (inputs : List RootOutput) : Prop :=
  ∃ input ∈ inputs, ∃ output, table (inputAddress input) = some output ∧ nextChain output = root

def NextCollision (table : Table) (left right : List RootOutput) : Prop :=
  ∃ l ∈ left, ∃ r ∈ right, l ≠ r ∧ ∃ lo ro,
    table (inputAddress l) = some lo ∧ table (inputAddress r) = some ro ∧ nextChain lo = nextChain ro

def Meeting (table : Table) (leftRoot rightRoot : RootOutput) (left right : List RootOutput) : Prop :=
  leftRoot = rightRoot ∨ RootHit table leftRoot right ∨ RootHit table rightRoot left ∨ NextCollision table left right

/-- Extending the actual chronological input lists preserves the same witnessed meeting event. -/
theorem meeting_mono (table : Table) (leftRoot rightRoot : RootOutput) (left right left' right' : List RootOutput)
    (hl : ∀ input ∈ left, input ∈ left') (hr : ∀ input ∈ right, input ∈ right')
    (event : Meeting table leftRoot rightRoot left right) : Meeting table leftRoot rightRoot left' right' := by
  rcases event with same | ⟨input, present, output, found, hit⟩ | ⟨input, present, output, found, hit⟩ |
    ⟨l, lp, r, rp, distinct, lo, ro, lf, rf, same⟩
  · exact Or.inl same
  · exact Or.inr (Or.inl ⟨input, hr input present, output, found, hit⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨input, hl input present, output, found, hit⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨l, hl l lp, r, hr r rp, distinct, lo, ro, lf, rf, same⟩))

/-- Equal terminals of two complete cached walks have an exact root-hit or distinct-input collision explanation in those same walks. -/
theorem walk_meeting (table : Table) (n m : Nat) (leftRoot rightRoot : RootOutput)
    (left right : List RootOutput) (target : RootOutput)
    (hl : walk table n leftRoot = some (left, target))
    (hr : walk table m rightRoot = some (right, target)) :
    Meeting table leftRoot rightRoot left right := by
  induction n generalizing m left right target with
  | zero =>
    have eq : ([], leftRoot) = (left, target) := by simpa [walk] using hl
    cases eq
    cases m with
    | zero =>
      have eq : ([], rightRoot) = (right, leftRoot) := by simpa [walk] using hr
      exact Or.inl (Prod.mk.inj eq).2.symm
    | succ m =>
      cases previous : walk table m rightRoot with
      | none => simp [walk, previous] at hr
      | some before =>
        cases found : table (inputAddress before.2) with
        | none => simp [walk, previous, found] at hr
        | some output =>
          have eq : (before.1 ++ [before.2], nextChain output) = (right, leftRoot) := by
            simpa [walk, previous, found] using hr
          exact Or.inr (Or.inl ⟨before.2, by rw [← (Prod.mk.inj eq).1]; simp,
            output, found, (Prod.mk.inj eq).2⟩)
  | succ n ih =>
    cases previousL : walk table n leftRoot with
    | none => simp [walk, previousL] at hl
    | some beforeL =>
      cases foundL : table (inputAddress beforeL.2) with
      | none => simp [walk, previousL, foundL] at hl
      | some outputL =>
        have eqL : (beforeL.1 ++ [beforeL.2], nextChain outputL) = (left, target) := by
          simpa [walk, previousL, foundL] using hl
        cases m with
        | zero =>
          have eqR : ([], rightRoot) = (right, target) := by simpa [walk] using hr
          exact Or.inr (Or.inr (Or.inl ⟨beforeL.2, by rw [← (Prod.mk.inj eqL).1]; simp,
            outputL, foundL, (Prod.mk.inj eqL).2.trans (Prod.mk.inj eqR).2.symm⟩))
        | succ m =>
          cases previousR : walk table m rightRoot with
          | none => simp [walk, previousR] at hr
          | some beforeR =>
            cases foundR : table (inputAddress beforeR.2) with
            | none => simp [walk, previousR, foundR] at hr
            | some outputR =>
              have eqR : (beforeR.1 ++ [beforeR.2], nextChain outputR) = (right, target) := by
                simpa [walk, previousR, foundR] using hr
              by_cases same : beforeL.2 = beforeR.2
              · have earlier := ih m beforeL.1 beforeR.1 beforeL.2 previousL (by simpa only [same] using previousR)
                apply meeting_mono table leftRoot rightRoot beforeL.1 beforeR.1 left right _ _ earlier
                · intro input present
                  rw [← (Prod.mk.inj eqL).1]
                  exact List.mem_append_left _ present
                · intro input present
                  rw [← (Prod.mk.inj eqR).1]
                  exact List.mem_append_left _ present
              · exact Or.inr (Or.inr (Or.inr ⟨beforeL.2, by rw [← (Prod.mk.inj eqL).1]; simp,
                  beforeR.2, by rw [← (Prod.mk.inj eqR).1]; simp, same, outputL, outputR,
                  foundL, foundR, (Prod.mk.inj eqL).2.trans (Prod.mk.inj eqR).2.symm⟩))

/-- The exact native counters bound both witness lists; all witnessed edges belong to the original retained paths. -/
theorem paths_meeting (table : Table) (leftRoot rightRoot : RootOutput)
    (first second : ConcreteRatchetKernel)
    (leftPath : RawCtxSourceSendPath.Path leftRoot first table)
    (rightPath : RawCtxSourceSendPath.Path rightRoot second table)
    (same : first.refined.send_chain = second.refined.send_chain) :
    ∃ left right, left.length = first.refined.control.send_sequence.val ∧
      right.length = second.refined.control.send_sequence.val ∧ Meeting table leftRoot rightRoot left right := by
  obtain ⟨left, hl⟩ := leftPath
  obtain ⟨right, hr⟩ := rightPath
  refine ⟨left, right, (walk_shape table _ _ _ hl).1, (walk_shape table _ _ _ hr).1, ?_⟩
  exact walk_meeting table _ _ leftRoot rightRoot left right
    (RawCtxSelectedQueryTrace.rootVector second.refined.send_chain) (by simpa only [same] using hl) hr

/-- One original LIVE run carries both source owner paths into the same complete cache before their send inputs are compared. Owner identities need not be inferred from their bytes. -/
theorem source_meeting {A M P I D K Result : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (leftRoot rightRoot : RootOutput) (leftOwner rightOwner : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxPendingSelectiveFamily.State A)
    (leftInitial : RawCtxSourceFamilyPath.NativeGood leftRoot leftOwner entry.1 state)
    (rightInitial : RawCtxSourceFamilyPath.NativeGood rightRoot rightOwner entry.1 state)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry state.1 state.2))
    (first second : ConcreteRatchetKernel)
    (leftFound : RawCtxProtocolReveals.selectedKernel leftOwner result.1.2.1 = some first)
    (rightFound : RawCtxProtocolReveals.selectedKernel rightOwner result.1.2.1 = some second)
    (same : first.refined.send_chain = second.refined.send_chain) :
    ∃ left right, left.length = first.refined.control.send_sequence.val ∧
      right.length = second.refined.control.send_sequence.val ∧ Meeting result.2.2.1 leftRoot rightRoot left right := by
  exact paths_meeting result.2.2.1 leftRoot rightRoot first second
    ((RawCtxSourceFamilyPath.source source writer stage leftRoot leftOwner sender route decode client entry state
      leftInitial result supported).2 first leftFound)
    ((RawCtxSourceFamilyPath.source source writer stage rightRoot rightOwner sender route decode client entry state
      rightInitial result supported).2 second rightFound) same

/-- A prior actual send and a later source owner use the same complete retained cache for this chronological meeting classification. The earlier seal may have returned no frame. -/
theorem chronological_meeting {A M P I D K Result : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (leftRoot rightRoot : RootOutput) (first : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A) (leftInitial : RawCtxSourceSendPath.Path leftRoot first state.2.1)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (sentActual : sent ∈ support ((simulateQ (RawCtxSourceSendPath.sendImpl source writer stage)
      (RawCtxSourceSend.send first context)).run state))
    (owner : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B)
    (rightInitial : RawCtxSourceFamilyPath.NativeGood rightRoot owner entry.1 sent.2)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry sent.2.1 sent.2.2))
    (second : ConcreteRatchetKernel)
    (rightFound : RawCtxProtocolReveals.selectedKernel owner result.1.2.1 = some second)
    (same : first.refined.send_chain = second.refined.send_chain) :
    ∃ left right, left.length = first.refined.control.send_sequence.val ∧
      right.length = second.refined.control.send_sequence.val ∧ Meeting result.2.2.1 leftRoot rightRoot left right := by
  have sentPath := RawCtxSourceSendPath.send_path source writer stage leftRoot first context state leftInitial sent sentActual
  have finalPath := RawCtxSourceFamilyPath.source source writer stage rightRoot owner sender route decode
    client entry sent.2 rightInitial result supported
  exact paths_meeting result.2.2.1 leftRoot rightRoot first second
    (RawCtxSourceSendPath.path_extends leftRoot first sent.2.2.1 result.2.2.1
      (RawCtxSourceSendPath.path_extends leftRoot first state.2.1 sent.2.2.1 leftInitial sentPath.1) finalPath.1)
    (finalPath.2 second rightFound) same

end BeaconcryptCore.Computational.RawCtxSendPathMeeting

/-- info: 'BeaconcryptCore.Computational.RawCtxSendPathMeeting.meeting_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendPathMeeting.meeting_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxSendPathMeeting.walk_meeting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendPathMeeting.walk_meeting

/-- info: 'BeaconcryptCore.Computational.RawCtxSendPathMeeting.paths_meeting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendPathMeeting.paths_meeting

/-- info: 'BeaconcryptCore.Computational.RawCtxSendPathMeeting.source_meeting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendPathMeeting.source_meeting

/-- info: 'BeaconcryptCore.Computational.RawCtxSendPathMeeting.chronological_meeting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendPathMeeting.chronological_meeting
