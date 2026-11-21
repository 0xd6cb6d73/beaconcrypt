import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection

/-! The same actual pending and builder receipt retains the pinned Server binding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding
open PqxdhServerAuthExperiment PqxdhServerAuthPhase1Projection PqxdhServerAuthEntryFactor
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Successful original commit preparation requires both fields of the supplied pending binding to equal the current Server binding. -/
theorem prepare_binding (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (current : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending current availability = ok (.Ok candidate)) :
    pending.server_binding = current := by
  have identifier : pending.server_binding.identity_key_id = current.identity_key_id := by
    by_contra different
    have rejected := BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
      state pending current availability (Or.inl different)
    rw [prepared] at rejected
    cases RustM.ok.inj rejected
  have publicKey : pending.server_binding.identity_public_key = current.identity_public_key := by
    by_contra different
    have rejected := BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
      state pending current availability (Or.inr different)
    rw [prepared] at rejected
    cases RustM.ok.inj rejected
  cases left : pending.server_binding
  cases right : current
  simpa only [left, right, pqxdh.ServerBinding.mk.injEq] using And.intro publicKey identifier

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.prepare_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.prepare_binding
