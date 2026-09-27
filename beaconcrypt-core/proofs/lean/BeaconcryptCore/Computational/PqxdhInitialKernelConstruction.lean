import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
import BeaconcryptCore.Refinement.RatchetInitialization

/-!
The supplied initial64 response constructs the literal zero-state native kernel. The retained initializer's supported reply therefore gives exact directional origins under every fixed ratchet interpreter, including an already retained private KDF table. These are source construction facts; they assert neither chain independence nor distinct session origins.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialKernelConstruction
open PqxdhInitialRatchetComplementarity PqxdhInitialReplyErasure

private theorem new_fields (send receive : RatchetChain) (kernel : ConcreteRatchetKernel)
    (created : ConcreteRatchetKernel.new send receive = .ok kernel) :
    ConcreteRatchetKernel.new kernel.refined.send_chain kernel.refined.receive_chain = .ok kernel := by
  obtain ⟨actual, built, _, _, _, _, sending, receiving, _⟩ := concreteKernelNew_exact send receive
  have same : actual = kernel := RustM.ok.inj (built.symm.trans created)
  simpa only [← same, sending, receiving] using built

/-- Every successful supplied response returns exactly the source zero-state constructor at its literal two directional chains. -/
theorem supplied_new (role : Bool) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kernel : ConcreteRatchetKernel) (initialized : kernelOf role response = .ok kernel) :
    ConcreteRatchetKernel.new kernel.refined.send_chain kernel.refined.receive_chain = .ok kernel := by
  obtain ⟨left, right, hleft, hright, _, _⟩ := initialHalves_exact response.bytes
  cases role <;>
    simp only [kernelOf, PqxdhInitialResponseService.pending,
      pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition,
      pqxdh.split_initial_ratchet_kdf_output, hleft, hright,
      RatchetChain.from_bytes, beaconPending, serverPending, Bool.false_eq_true, ite_false, ite_true,
      bind_tc_ok] at initialized
  · exact new_fields _ _ kernel initialized
  · simp only [show (32#u8 : U8) ≠ 0#u8 by decide, ite_false, bind_tc_ok] at initialized
    exact new_fields _ _ kernel initialized

/-- The same literal source initializer is reachable under every fixed ratchet interpreter; no assumption about its response distribution is required. -/
theorem supplied_reachable {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (role : Bool) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (kernel : ConcreteRatchetKernel) (initialized : kernelOf role response = .ok kernel) :
    RoleReachable cr kernel.refined.send_chain kernel.refined.receive_chain kernel := by
  obtain ⟨actual, created, _, reachable⟩ := new_reachable cr kernel.refined.send_chain kernel.refined.receive_chain
  have same : actual = kernel := RustM.ok.inj (created.symm.trans (supplied_new role response kernel initialized))
  simpa only [same] using reachable

/-- The retained Beacon constructor is the supplied-response initializer with the same complete kernel, despite its private root audit. -/
theorem audited_supplied (reply : PqxdhInitialRootAudit.AuditReply) :
    kernelOf true reply.2 = .ok (PqxdhInitialRootAudit.kernel reply) := by
  change pqxdh.concrete.resume_initial_ratchet_kdf
    (beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) reply.2 = _
  rw [PqxdhBeaconPhase2Publication.normalInitial_exact,
    beacon_kernel_root_unused _ (PqxdhRootTableInitialization.rootArray reply.1)]
  rfl

/-- Every actual retained initializer reply contains the literal zero-state constructor and is reachable under the caller's fixed retained KDF interpretation. All original auxiliary state is preserved. -/
theorem retained_supported {A N AD PT CT : Type}
    (fixed : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (result : (PqxdhInitialParentObserverCompiler.InitialReply × (RawCtxSharedPrimitive.SharedState A × N)) ×
      PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (supported : result ∈ support ((PqxdhInitialNativeInitializer.initial fixed selected previousRoot response secrets state).run cache)) :
    ∃ reply : PqxdhInitialRootAudit.AuditReply,
      result.1.1 = (reply.1, some (PqxdhInitialRootAudit.kernel reply).refined) ∧ result.1.2 = state ∧
      ConcreteRatchetKernel.new (PqxdhInitialRootAudit.kernel reply).refined.send_chain
        (PqxdhInitialRootAudit.kernel reply).refined.receive_chain = .ok (PqxdhInitialRootAudit.kernel reply) ∧
      RoleReachable cr (PqxdhInitialRootAudit.kernel reply).refined.send_chain
        (PqxdhInitialRootAudit.kernel reply).refined.receive_chain (PqxdhInitialRootAudit.kernel reply) := by
  obtain ⟨reply, returned, unchanged, _, _⟩ :=
    PqxdhInitialNativeInitializer.initial_supported fixed selected previousRoot response secrets state cache result supported
  exact ⟨reply, returned, unchanged, supplied_new true reply.2 _ (audited_supplied reply),
    supplied_reachable cr true reply.2 _ (audited_supplied reply)⟩

end BeaconcryptCore.Computational.PqxdhInitialKernelConstruction

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.supplied_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.supplied_new

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.supplied_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.supplied_reachable

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.audited_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.audited_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.retained_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialKernelConstruction.retained_supported
