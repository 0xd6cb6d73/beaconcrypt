import BeaconcryptCore.Computational.RawCtxFunctionalFamily
import BeaconcryptCore.Computational.RawCtxSendPathMeeting

/-!
The actual fixed retained private interpreter supplies the same complete responses used by the source directional-path analysis. This connects the functional native family to cached-walk witnesses without replacing public HKDF, resampling projections, or asserting independence of supplied roots.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxCursorLineage RawCtxKdfRequestTable
variable {AD PT CT A M P I D K Result : Type} {S B : Nat}

def table (prior : Prior) : Table := QueryCache.ofFn (fun address => some (prior address))

/-- The source ratchet request uses exactly the walk's input bytes and production domain label. -/
theorem request_address (chain : RatchetChain) :
    address (RawCtxChainSend.nativeRequest chain) =
      RawCtxFirstParentRisk.inputAddress (RawCtxSelectedQueryTrace.rootVector chain) := by
  change (⟨PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO,
    PqxdhRefinement.absBytes chain.bytes⟩ : JointKdfAddress) =
      ⟨Pqxdh.INFO_R, PqxdhRefinement.absBytes chain.bytes⟩
  simpa only [pqxdh.SYM_RATCHET_INFO] using
    congrArg (fun domain => (⟨domain, PqxdhRefinement.absBytes chain.bytes⟩ : JointKdfAddress))
      PqxdhRefinement.absBytes_SYM_RATCHET_INFO

/-- The actual full retained response supplies its second32 coordinate as the next source chain. -/
theorem interpreted_chain (prior : Prior) (chain : RatchetChain) :
    RawCtxSelectedQueryTrace.rootVector
        (interpretedStep (RawCtxFunctionalFamily.execute prior) chain).chain =
      PqxdhOrderedChainHybrids.nextChain
        (prior (address (RawCtxChainSend.nativeRequest chain))) := by
  simpa only [RawCtxInterpretedReceive.decodeResponse, interpretedStep, interpretedResponse,
    RawCtxFunctionalFamily.execute, RawCtxChainSend.nativeRequest,
    RawCtxSelectedQueryTrace.rootVector_concrete] using
      congrArg (fun result => RawCtxSelectedQueryTrace.rootVector result.1)
        (RawCtxFreshChainCut.decoded_parts (prior (address (RawCtxChainSend.nativeRequest chain))))

/-- A complete source chain position has the same chronological private-input walk in its retained view. -/
theorem source_walk (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (root : RatchetChain) (n : Nat) :
    ∃ inputs, walk (table prior) n (RawCtxSelectedQueryTrace.rootVector root) =
      some (inputs, RawCtxSelectedQueryTrace.rootVector
        (Ratchet.chainAt (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) root n)) := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨inputs, walked⟩ := ih
    refine ⟨inputs ++ [RawCtxSelectedQueryTrace.rootVector
      (Ratchet.chainAt (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) root n)], ?_⟩
    rw [walk, walked]
    simp [table]
    simpa only [Ratchet.chainAt, Function.iterate_succ_apply', withInterpreter, request_address] using
      (interpreted_chain prior
        (Ratchet.chainAt (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) root n)).symm

/-- The original source reachability certificate supplies its exact counter-length send path. -/
theorem reachable_path (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (reachable : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
      sendOrigin receiveOrigin entry) :
    RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin) entry (table prior) := by
  obtain ⟨send, receive, refined, aligned⟩ := reachable
  simpa only [RawCtxSourceSendPath.Path, refined.sendSequence, refined.sendChain, aligned] using
    source_walk prior cr sendOrigin send.n

/-- The literal retained-view native send preserves the same directional source path through every optional seal and writer result. -/
theorem native_send_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (reachable : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
      sendOrigin receiveOrigin entry)
    (context : RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ
      ((RawCtxFunctionalFamily.native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send entry context)).run state)) :
    RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin) result.1.1 (table prior) := by
  apply reachable_path prior cr sendOrigin receiveOrigin result.1.1
  exact RawCtxFunctionalPositions.send cr (RawCtxFunctionalFamily.execute prior) sendOrigin receiveOrigin
    entry reachable context (RawCtxFunctionalFamily.sealing source writer prior) state result
    (by simpa only [RawCtxFunctionalFamily.send_handler] using supported)

/-- Returning to the old input on an actual admitted retained-view send exposes a cycle; writer failure is included and strict counter advancement is derived from the source run. -/
theorem native_send_cycle (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (reachable : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
      sendOrigin receiveOrigin entry)
    (context : RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState A)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ
      ((RawCtxFunctionalFamily.native source writer prior ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send entry context)).run state))
    (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX)
    (same : entry.refined.send_chain = result.1.1.refined.send_chain) :
    RawCtxSendLineageCollision.Cycle (table prior) (RawCtxSelectedQueryTrace.rootVector sendOrigin)
      result.1.1.refined.control.send_sequence.val := by
  apply RawCtxSendLineageCollision.same_direction_cycle (table prior) _ entry result.1.1
    (reachable_path prior cr sendOrigin receiveOrigin entry reachable)
    (native_send_path source writer prior cr sendOrigin receiveOrigin entry reachable context state result supported)
    _ same
  obtain ⟨_, _, _, _, _, _, _, _, _, _, advanced, _⟩ :=
    RawCtxSourceSend.send_nonexhausted_support _ entry context state active result supported
  omega

/-- A literal successful source constructor supplies the original empty path without a distribution or key-independence premise. -/
theorem initialized_path (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (constructed : ConcreteRatchetKernel.new sendOrigin receiveOrigin = ok entry) :
    RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin) entry (table prior) := by
  apply reachable_path prior cr sendOrigin receiveOrigin entry
  exact RawCtxFunctionalPositions.initialized cr (RawCtxFunctionalFamily.execute prior)
    sendOrigin receiveOrigin entry constructed

/-- A selected stored kernel carries its literal directional path; arbitrary unannotated owner state is not assigned an origin. -/
theorem stored_path (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (entry : RawCtxFunctionalFamily.Stored cr prior) (sendOrigin receiveOrigin : RatchetChain)
    (marked : RawCtxFunctionalFamily.origins cr prior entry = some (sendOrigin, receiveOrigin)) :
    RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin)
      (RawCtxFunctionalFamily.kernel cr prior entry) (table prior) := by
  cases entry with
  | inl original => cases marked
  | inr located =>
    have same := Option.some.inj marked
    cases same
    exact reachable_path prior cr located.sendOrigin located.receiveOrigin located.kernel located.valid

def FamilyPaths (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (state : RawCtxGenericFamilyLive.State (RawCtxFunctionalFamily.Stored cr prior) M P I D K S B) : Prop :=
  ∀ owner entry, RawCtxGenericRoleFamily.selectedKernel owner state.1 = some entry →
    ∀ sendOrigin receiveOrigin, RawCtxFunctionalFamily.origins cr prior entry = some (sendOrigin, receiveOrigin) →
      RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin)
        (RawCtxFunctionalFamily.kernel cr prior entry) (table prior)

/-- Selected initialized owners in a complete retained-view family have paths at their actual counters; other native owners remain unrestricted. -/
theorem family_paths (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (state : RawCtxGenericFamilyLive.State (RawCtxFunctionalFamily.Stored cr prior) M P I D K S B) :
    FamilyPaths prior cr state := by
  exact fun _ entry _ sendOrigin receiveOrigin marked =>
    stored_path prior cr entry sendOrigin receiveOrigin marked

/-- Every supported original adaptive LIVE result lifts to the same complete retained-view source run with counter-length paths for its annotated owners. This is a support consumer of the exact full-state law, not a probability or freshness claim. -/
theorem native_family_paths (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxGenericFamilyLive.State (RawCtxFunctionalFamily.Stored cr prior) M P I D K S B)
    (ambient : RawCtxSharedPrimitive.SharedState A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ (RawCtxFunctionalFamily.backend source writer prior)
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run
        (RawCtxGenericFamilyLive.nativeState (RawCtxFunctionalFamily.kernel cr prior) state))).run ambient)) :
    ∃ reached ∈ support (((simulateQ
        (RawCtxFunctionalFamily.storedImpl cr source writer prior sender route decode) client).run state).run ambient),
      ((reached.1.1, RawCtxGenericFamilyLive.nativeState (RawCtxFunctionalFamily.kernel cr prior) reached.1.2), reached.2) = result ∧
      FamilyPaths prior cr reached.1.2 := by
  rw [RawCtxFunctionalFamily.stored_source, StateT.run_map, support_map] at supported
  obtain ⟨reached, actual, same⟩ := supported
  exact ⟨reached, actual, same, family_paths prior cr reached.1.2⟩

/-- Equal sending inputs from two retained source owners expose exact counter-length root-hit or next-output collision witnesses. Equal roots remain an explicit case, without identifying the owners or their installation occurrences. -/
theorem stored_meeting (prior : Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (first second : RawCtxFunctionalFamily.Stored cr prior)
    (leftSend leftReceive rightSend rightReceive : RatchetChain)
    (leftMarked : RawCtxFunctionalFamily.origins cr prior first = some (leftSend, leftReceive))
    (rightMarked : RawCtxFunctionalFamily.origins cr prior second = some (rightSend, rightReceive))
    (same : (RawCtxFunctionalFamily.kernel cr prior first).refined.send_chain =
      (RawCtxFunctionalFamily.kernel cr prior second).refined.send_chain) :
    ∃ left right,
      left.length = (RawCtxFunctionalFamily.kernel cr prior first).refined.control.send_sequence.val ∧
      right.length = (RawCtxFunctionalFamily.kernel cr prior second).refined.control.send_sequence.val ∧
      RawCtxSendPathMeeting.Meeting (table prior) (RawCtxSelectedQueryTrace.rootVector leftSend)
        (RawCtxSelectedQueryTrace.rootVector rightSend) left right := by
  exact RawCtxSendPathMeeting.paths_meeting (table prior) _ _ _ _
    (stored_path prior cr first leftSend leftReceive leftMarked)
    (stored_path prior cr second rightSend rightReceive rightMarked) same

end BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.request_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.request_address

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.interpreted_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.interpreted_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.source_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.source_walk

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.reachable_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.reachable_path

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_send_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_send_path

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_send_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_send_cycle

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.initialized_path

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.stored_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.stored_path

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.family_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.family_paths

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_family_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.native_family_paths

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.stored_meeting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath.stored_meeting
