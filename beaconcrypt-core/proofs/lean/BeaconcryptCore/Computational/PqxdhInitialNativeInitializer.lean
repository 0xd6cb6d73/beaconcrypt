import BeaconcryptCore.Computational.PqxdhInitialRootAudit
import BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler

/-!
The actual later-chain initializer performs the original classified root lookup in the retained root cache and constructs the complete source Beacon kernel from that same response. Its private audit retains the exact input and its two output chains. The earlier selected root and supplied64 response are fixed before the later parent draw; no new selected chain is passed to this service.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient PqxdhInitialRootAudit
open PqxdhCorrelatedExpand
open PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid PqxdhInitialRootLabelService
variable {A N : Type}

noncomputable def initial (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Ambient A N RootOracle.QueryCache PqxdhInitialParentObserverCompiler.InitialReply :=
  fun state => (fun reply => ((reply.1, some (kernel reply).refined), state)) <$>
    retained fixed selected previousRoot response (PqxdhInitialRootLabelBridge.request fixed secrets)

/-- The actual retained service reuses exactly the selected initializer response and keeps the complete shared, identity and cache state. -/
theorem selected_initial (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (matching : PqxdhInitialRootLabelBridge.request fixed secrets = .family selected) :
    initial (A := A) (N := N) fixed selected previousRoot response secrets =
      pure (previousRoot, some (kernel (previousRoot, response)).refined) := by
  funext state cache
  simp only [initial, matching, retained]
  rfl

/-- Once the exact64 response has been obtained, the actual source constructor retains no initializer input in its kernel. -/
theorem kernel_input_unused (left right : RootOutput) (response : Response) :
    kernel (left, response) = kernel (right, response) :=
  PqxdhInitialReplyErasure.beacon_kernel_root_unused _ _ response

/-- Every actual supplied-response initializer starts at source send counter zero, regardless of its root or response bytes. -/
theorem kernel_send_zero (fixed : FixedHkdfSha512NoSaltSource) (reply : AuditReply) :
    (kernel reply).refined.control.send_sequence.val = 0 := by
  obtain ⟨beaconOrigin, serverOrigin, beacon, server, hb, hs, bo, so, br, sr⟩ :=
    PqxdhInitialSuppliedPositions.pair_refines fixed.crypto reply.2
  have same : beacon = kernel reply := by
    apply RustM.ok.inj
    rw [← hb]
    change pqxdh.concrete.resume_initial_ratchet_kdf
      (PqxdhInitialRatchetComplementarity.beaconPending
        (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) reply.2 = _
    rw [PqxdhBeaconPhase2Publication.normalInitial_exact,
      PqxdhInitialReplyErasure.beacon_kernel_root_unused _ (PqxdhRootTableInitialization.rootArray reply.1)]
    rfl
  simpa only [same] using br.sendSequence

/-- The actual initializer's only uniform cost is the at-most32-byte original root-cache lookup; auditing and kernel construction add no random draw. -/
theorem initial_uniform (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : RootOracle.QueryCache) :
    ((initial fixed selected previousRoot response secrets state).run cache).IsTotalQueryBound 32 := by
  simpa only [initial, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using
    retained_uniform fixed selected previousRoot response (PqxdhInitialRootLabelBridge.request fixed secrets) cache

set_option backward.isDefEq.respectTransparency false in
/-- Erasing only the private root audit yields the same original labelled response lookup and complete source kernel, with the original ambient state and cache. -/
theorem initial_erase (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : RootOracle.QueryCache) :
    (fun result => ((result.1.1.2, result.1.2), result.2)) <$>
      ((initial fixed selected previousRoot response secrets state).run cache) =
      (fun result => ((some (kernel (List.Vector.replicate 32 0, result.1)).refined, state), result.2)) <$>
        ((labelled fixed selected response (PqxdhInitialRootLabelBridge.request fixed secrets)).run cache) := by
  have erased := congrArg (fun work => work.run cache)
    (retained_erase fixed selected previousRoot response (PqxdhInitialRootLabelBridge.request fixed secrets))
  simp only [StateT.run_map] at erased
  rw [← erased]
  simp only [initial, StateT.run_map, Functor.map_map]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Every supported actual initializer reply contains its exact audited source kernel with zero initial send counter and the established positional invariant. -/
theorem initial_supported (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : RootOracle.QueryCache)
    (result : (PqxdhInitialParentObserverCompiler.InitialReply × (RawCtxSharedPrimitive.SharedState A × N)) × RootOracle.QueryCache)
    (supported : result ∈ support ((initial fixed selected previousRoot response secrets state).run cache)) :
    ∃ reply : AuditReply,
      result.1.1 = (reply.1, some (kernel reply).refined) ∧ result.1.2 = state ∧
        RawCtxPositionedOwner.Positioned fixed.crypto (kernel reply).refined.send_chain (kernel reply).refined.receive_chain (kernel reply) ∧
        (kernel reply).refined.control.send_sequence.val = 0 := by
  simp only [initial, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  exact ⟨reply.1, rfl, rfl, positioned fixed.crypto reply.1, kernel_send_zero fixed reply.1⟩

end BeaconcryptCore.Computational.PqxdhInitialNativeInitializer

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.selected_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.selected_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.kernel_input_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.kernel_input_unused
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.kernel_send_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.kernel_send_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeInitializer.initial_supported
