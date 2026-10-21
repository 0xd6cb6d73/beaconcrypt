import BeaconcryptCore.Computational.RawCtxSelectedSendAddress
import BeaconcryptCore.Computational.RawCtxSourceFamilyPath
import BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions
import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-!
Every source send advances along its own retained directional path, including failed seals. This module exposes exact path repetition and cross-direction meeting events from the actual source cache and counters. These events are not assumed unlikely: their source initialization and evolving-output reductions must be charged by the consuming experiment. Legitimate paired receive traversal is not a send occurrence.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSendLineageCollision
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxCursorLineage RawCtxKdfRequestTable

/-- Splitting the actual cached walk preserves every chronological input and its terminal chain. -/
theorem walk_add (table : Table) (first rest : Nat) (root : RootOutput) :
    walk table (first + rest) root = (do
      let before ← walk table first root
      let after ← walk table rest before.2
      pure (before.1 ++ after.1, after.2)) := by
  induction rest with
  | zero => simp [walk]
  | succ rest ih =>
      rw [show first + (rest + 1) = (first + rest) + 1 by omega, walk, ih]
      cases left : walk table first root with
      | none => simp
      | some before =>
          cases right : walk table rest before.2 with
          | none => simp [walk, right]
          | some after =>
              cases found : table (RawCtxFirstParentRisk.inputAddress after.2) <;>
                simp [walk, right, found, List.append_assoc]

/-- Every nonempty executed path records its initial input, before any later repeated inputs. -/
theorem walk_head (table : Table) (steps : Nat) (root : RootOutput)
    (result : List RootOutput × RootOutput) (known : walk table (steps + 1) root = some result) :
    root ∈ result.1 := by
  rw [show steps + 1 = 1 + steps by omega, walk_add] at known
  cases first : table (RawCtxFirstParentRisk.inputAddress root) with
  | none => simp [walk, first] at known
  | some output =>
      cases rest : walk table steps (nextChain output) with
      | none => simp [walk, first, rest] at known
      | some suffix =>
          have same : ([root] ++ suffix.1, suffix.2) = result := by simpa [walk, first, rest] using known
          subst result
          simp

/-- An earlier terminal input is a chronological input of every strictly later successful walk from the same root. -/
theorem walk_earlier (table : Table) (first later : Nat) (ordered : first < later) (root : RootOutput)
    (before after : List RootOutput × RootOutput)
    (left : walk table first root = some before) (right : walk table later root = some after) :
    before.2 ∈ after.1 := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_lt ordered
  rw [Nat.add_assoc, walk_add, left] at right
  cases tail : walk table (rest + 1) before.2 with
  | none => simp [tail] at right
  | some suffix =>
      have same : (before.1 ++ suffix.1, suffix.2) = after := by simpa [tail] using right
      subst after
      exact List.mem_append_right _ (walk_head table rest before.2 suffix tail)

def Cycle (table : Table) (root : RootOutput) (position : Nat) : Prop :=
  ∃ earlier input, walk table position root = some (earlier, input) ∧ input ∈ earlier

/-- Equal old send chains at strictly increasing source counters expose an actual repeated input in the same retained directional walk. -/
theorem same_direction_cycle (table : Table) (root : RootOutput)
    (first second : ConcreteRatchetKernel)
    (firstPath : RawCtxSourceSendPath.Path root first table)
    (secondPath : RawCtxSourceSendPath.Path root second table)
    (ordered : first.refined.control.send_sequence.val < second.refined.control.send_sequence.val)
    (same : first.refined.send_chain = second.refined.send_chain) :
    Cycle table root second.refined.control.send_sequence.val := by
  obtain ⟨before, left⟩ := firstPath
  obtain ⟨after, right⟩ := secondPath
  refine ⟨after, RawCtxSelectedQueryTrace.rootVector second.refined.send_chain, right, ?_⟩
  have earlier := walk_earlier table _ _ ordered root _ _ left right
  simpa only [same] using earlier

/-- A nonexhausted actual send returning to its old chain witnesses a cached source cycle, even when the seal/writer returns None. Both path and strict-counter premises are derived from that execution. -/
theorem source_send_cycle {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat) (root : RootOutput)
    (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A) (valid : RawCtxSourceSendPath.Path root entry state.2.1)
    (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (RawCtxSourceSendPath.sendImpl source writer stage)
      (RawCtxSourceSend.send entry context)).run state))
    (same : entry.refined.send_chain = result.1.1.refined.send_chain) :
    Cycle result.2.2.1 root result.1.1.refined.control.send_sequence.val := by
  have preserved := RawCtxSourceSendPath.send_path source writer stage root entry context state valid result supported
  obtain ⟨pending, response, afterKdf, _, _, _, _, _, _, _, sequence, _⟩ :=
    RawCtxSourceSend.send_nonexhausted_support (RawCtxSourceSendPath.sendImpl source writer stage)
      entry context state active result supported
  exact same_direction_cycle result.2.2.1 root entry result.1.1
    (RawCtxSourceSendPath.path_extends root entry state.2.1 result.2.2.1 valid preserved.1)
    preserved.2 (by omega) same

/-- The two actual initial send chains alias exactly when the two halves of their one shared64 response coincide. Complementary receive use creates no second send owner. -/
theorem initial_send_alias (c : Pqxdh.Crypto) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (beacon server : ConcreteRatchetKernel)
    (beaconCreated : PqxdhInitialReplyErasure.kernelOf true response = ok beacon)
    (serverCreated : PqxdhInitialReplyErasure.kernelOf false response = ok server) :
    beacon.refined.send_chain = server.refined.send_chain ↔
      PqxdhInitialRatchetComplementarity.firstHalf response.bytes =
        PqxdhInitialRatchetComplementarity.secondHalf response.bytes := by
  obtain ⟨beaconOrigin, serverOrigin, originalBeacon, originalServer, actualBeacon, actualServer,
    beaconBytes, serverBytes, beaconRefined, serverRefined⟩ := PqxdhInitialSuppliedPositions.pair_refines c response
  have hb := RustM.ok.inj (actualBeacon.symm.trans beaconCreated)
  have hs := RustM.ok.inj (actualServer.symm.trans serverCreated)
  subst beacon server
  rw [beaconRefined.sendChain, serverRefined.sendChain]
  constructor
  · intro same
    exact serverBytes.symm.trans ((congrArg BeaconcryptCore.Refinement.RepresentationBridge.absChain same.symm).trans beaconBytes)
  · intro same
    exact PqxdhInitialRatchetComplementarity.chain_eq_of_refines beaconBytes (serverBytes.trans same)

/-- The native half comparison is exactly equality of the two retained vectors of that same response. -/
theorem initial_half_alias (first second : RootOutput) :
    PqxdhInitialRatchetComplementarity.firstHalf (RawCtxSelectedInitialConstructor.response64 (first ++ second)).bytes =
      PqxdhInitialRatchetComplementarity.secondHalf (RawCtxSelectedInitialConstructor.response64 (first ++ second)).bytes ↔
        first = second := by
  have halves := RawCtxSelectedInitialConstructor.halves64 first second
  change BeaconcryptCore.Refinement.RepresentationBridge.absChain (RawCtxFreshChainCut.concreteChain first) = _ ∧
    BeaconcryptCore.Refinement.RepresentationBridge.absChain (RawCtxFreshChainCut.concreteChain second) = _ at halves
  rw [← halves.1, ← halves.2]
  constructor
  · intro same
    have bytes := congrArg RawCtxSelectedQueryTrace.rootVector
      (BeaconcryptCore.Refinement.RepresentationBridge.absChain_injective same)
    simpa only [RawCtxSelectedQueryTrace.rootVector_concrete] using bytes
  · rintro rfl
    rfl

def InitialAlias (output : HmacBlock) : Prop :=
  PqxdhSecretInputKdf.first32 output = RawCtxSelectedInitialSampler.initialOther output

/-- For the actual two source constructors, the bad initial send alias is measured on their single original64 response. -/
theorem initial_source_event (c : Pqxdh.Crypto) (output : HmacBlock)
    (beacon server : ConcreteRatchetKernel)
    (beaconCreated : PqxdhInitialReplyErasure.kernelOf true (RawCtxSelectedInitialConstructor.response64 output) = ok beacon)
    (serverCreated : PqxdhInitialReplyErasure.kernelOf false (RawCtxSelectedInitialConstructor.response64 output) = ok server) :
    beacon.refined.send_chain = server.refined.send_chain ↔ InitialAlias output := by
  rw [initial_send_alias c _ beacon server beaconCreated serverCreated]
  have halves := initial_half_alias (PqxdhSecretInputKdf.first32 output) (RawCtxSelectedInitialSampler.initialOther output)
  simpa only [RawCtxSelectedInitialConstructor.split_reconstruct, InitialAlias] using halves

/-- One uniform full64 source response pays one 256-bit equality term for its two sending directions. It is never replaced by two independent role responses. -/
theorem initial_alias_uniform :
    Pr{let x ← ($ᵗ HmacBlock)}[InitialAlias x] ≤ (1 : ENNReal) / (2 ^ 256 : ENNReal) := by
  have law := RawCtxSelectedInitialSampler.initial_observed
    (fun second first => (pure (first, second) : ProbComp (RootOutput × RootOutput)))
  have event := law.prEvent_eq (fun pair : RootOutput × RootOutput => pair.1 = pair.2)
  generalize sampledBlock : ($ᵗ HmacBlock : ProbComp HmacBlock) = block at event ⊢
  generalize sampledRoot : ($ᵗ RootOutput : ProbComp RootOutput) = root at event
  rw [bind_pure_comp _ block, prEvent_map] at event
  refine event.trans_le ?_
  refine prEvent_bind_le_of_forall_le root _ _ fun second => ?_
  rw [bind_pure_comp _ root, prEvent_map]
  subst sampledRoot
  simpa only [List.mem_singleton, List.length_singleton, Nat.cast_one] using
    RawCtxSelectedInputCandidates.uniform_candidates [second]

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_alias_uniform_vcvioLegacy :
    probEvent ($ᵗ BeaconcryptCore.Computational.PqxdhSecretInputKdf.HmacBlock) BeaconcryptCore.Computational.RawCtxSendLineageCollision.InitialAlias ≤ 1 / 2 ^ 256 :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_alias_uniform

noncomputable def initialTrace {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → RustM ConcreteRatchetKernel → ProbComp Result) :
    ProbComp (Context × HmacBlock × Result) := do
  let context ← sample
  let output ← $ᵗ HmacBlock
  let result ← observe context output
    (PqxdhInitialReplyErasure.kernelOf true (RawCtxSelectedInitialConstructor.response64 output))
    (PqxdhInitialReplyErasure.kernelOf false (RawCtxSelectedInitialConstructor.response64 output))
  pure (context, output, result)

/-- The actual paired constructors and an arbitrary complete continuation retain the same initial-response collision bound. No success or freshness conditioning changes the sampler. -/
theorem initial_observed_alias {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → RustM ConcreteRatchetKernel → ProbComp Result) :
    Pr{let result ← initialTrace sample observe}[InitialAlias result.2.1] ≤ (1 : ENNReal) / (2 ^ 256 : ENNReal) := by
  unfold initialTrace
  refine prEvent_bind_le_of_forall_le _ _ _ fun context => ?_
  refine (prEvent_bind_le_prEvent_of_support _ _ InitialAlias _ ?_).trans initial_alias_uniform
  intro output _ different
  rw [bind_pure_comp _ (observe context output _ _), prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ fun _ => different

set_option maxRecDepth 2048 in
/-- The paired initializer draws one64-byte response, paying the full original context sampler and every possible continuation cost. -/
theorem initial_trace_uniform {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → RustM ConcreteRatchetKernel → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output beacon server,
      (observe context output beacon server).IsTotalQueryBound qObserve) :
    (initialTrace sample observe).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  unfold initialTrace
  exact isTotalQueryBound_bind sampleBound fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun output => by
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using observeBound context output _ _

end BeaconcryptCore.Computational.RawCtxSendLineageCollision

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_add

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_head

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_earlier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.walk_earlier

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.same_direction_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.same_direction_cycle

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.source_send_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.source_send_cycle

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_send_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_send_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_half_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_half_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_source_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_source_event

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_alias_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_alias_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_observed_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_observed_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_trace_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendLineageCollision.initial_trace_uniform
