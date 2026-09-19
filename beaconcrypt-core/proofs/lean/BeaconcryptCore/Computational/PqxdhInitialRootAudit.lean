import BeaconcryptCore.Computational.PqxdhInitialRootLabelService
import BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions
import BeaconcryptCore.Computational.RawCtxSelectedQueryTrace

/-!
After the initializer comparison has drawn an independent64-byte response, its earlier root may be retained privately for subsequent chain cuts. This audit records the exact initializer input together with its response, without an additional sample or public reply. Erasing the input recovers the original service and full cache. The three candidate values are that input and the two actual initialized chains. The audit is not used as the root-free observer of the earlier Extract comparison.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootAudit
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand
open PqxdhCorrelatedExpandHybrid PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService

abbrev AuditReply := RootOutput × Response

noncomputable def native (fixed : FixedHkdfSha512NoSaltSource) :
    Request → StateT RootOracle.QueryCache ProbComp AuditReply
  | .known root => pure (root, realInitial fixed root)
  | .family message => do
      let root ← uniformImpl (.inr message)
      pure (root, realInitial fixed root)

noncomputable def retained (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response) :
    Request → StateT RootOracle.QueryCache ProbComp AuditReply
  | .known root => native fixed (.known root)
  | .family message => if message = selected then pure (previousRoot, response)
      else native fixed (.family message)

/-- The exact native root lookup, including cache hits and misses, is unchanged after removing only the private audit field. -/
theorem native_erase (fixed : FixedHkdfSha512NoSaltSource) (query : Request) :
    Prod.snd <$> native fixed query = PqxdhInitialRootLabelService.native fixed query := by
  cases query <;> simp only [native, PqxdhInitialRootLabelService.native, map_bind, map_pure]
  rfl

/-- A later chain cut retains the earlier selected root privately; removing that audit field gives the exact original selected-response service for every request. -/
theorem retained_erase (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response) (query : Request) :
    Prod.snd <$> retained fixed selected previousRoot response query =
      labelled fixed selected response query := by
  cases query with
  | known root => rfl
  | family message =>
      simp only [retained, labelled]
      split
      · rfl
      · exact native_erase fixed (.family message)

noncomputable def kernel (reply : AuditReply) : ConcreteRatchetKernel :=
  PqxdhBeaconPhase2Publication.normalInitial
    (PqxdhInitialRatchetComplementarity.beaconPending
      (PqxdhRootTableInitialization.rootArray reply.1)) reply.2

noncomputable def candidates (reply : AuditReply) : List RootOutput :=
  [reply.1, RawCtxSelectedQueryTrace.rootVector (kernel reply).refined.send_chain,
    RawCtxSelectedQueryTrace.rootVector (kernel reply).refined.receive_chain]

/-- Each actual initializer contributes exactly its input and both directional chain values, even when their bytes coincide. -/
theorem candidates_length (reply : AuditReply) : (candidates reply).length = 3 := rfl

/-- The actual source initializer input is in the recorded candidate list. -/
theorem input_recorded (reply : AuditReply) : reply.1 ∈ candidates reply := by
  simp only [candidates, List.mem_cons, true_or]

/-- Both chains of the actual zero-state Beacon constructor are recorded before its first receive. -/
theorem chains_recorded (reply : AuditReply) :
    RawCtxSelectedQueryTrace.rootVector (kernel reply).refined.send_chain ∈ candidates reply ∧
    RawCtxSelectedQueryTrace.rootVector (kernel reply).refined.receive_chain ∈ candidates reply := by
  simp [candidates]

/-- The audited constructor is the same original supplied-response kernel and starts with the checked source positional invariant. -/
theorem positioned (crypto : Pqxdh.Crypto) (reply : AuditReply) :
    RawCtxPositionedOwner.Positioned crypto (kernel reply).refined.send_chain
      (kernel reply).refined.receive_chain (kernel reply) :=
  PqxdhInitialSuppliedPositions.beacon_positioned crypto _ reply.2

/-- Recording the private input adds no random or primitive call: its syntactic map projection has the original at-most32-byte root-cache bill. -/
theorem retained_uniform (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (previousRoot : RootOutput) (response : Response) (query : Request)
    (cache : RootOracle.QueryCache) :
    ((retained fixed selected previousRoot response query).run cache).IsTotalQueryBound 32 := by
  have bound := labelled_uniform_bound fixed selected response query cache
  rw [← retained_erase fixed selected previousRoot response query] at bound
  simpa only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using bound

end BeaconcryptCore.Computational.PqxdhInitialRootAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.native_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.retained_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.retained_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.candidates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.candidates_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.input_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.input_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.chains_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.chains_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.positioned

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootAudit.retained_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootAudit.retained_uniform
