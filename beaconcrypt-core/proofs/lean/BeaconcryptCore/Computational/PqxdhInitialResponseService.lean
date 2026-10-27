import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment
import BeaconcryptCore.Computational.PqxdhInitialBuilderCut

/-!
One private initializer capability carries the exact extracted input and info and returns the complete64-byte response. Both roles use that same capability and retain their opposite extracted orientations. It is separate from real public HKDF and from private32-byte PQXDH root processing. The source interpreter returns the exact fixed HKDF value; the added interface does not sample or assume uniform material.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialResponseService
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhInitialRatchetComplementarity
open BeaconcryptCore.Refinement.PqxdhConcreteSession
variable {ι : Type} {base : OracleSpec ι} {Result : Type}

abbrev InitialSpec := SymmetricRatchetKdfRequest →ₒ pqxdh.concrete.InitialRatchetKdfResponse
abbrev Spec (base : OracleSpec ι) := base + InitialSpec

def original : QueryImpl base (OracleComp (Spec base)) := fun query => (Spec base).query (.inl query)
def initial : QueryImpl InitialSpec (OracleComp (Spec base)) := fun query => (Spec base).query (.inr query)

noncomputable def source (fixed : FixedHkdfSha512NoSaltSource) : QueryImpl (Spec base) (OracleComp base)
  | .inl query => base.query query
  | .inr request => pure (RawCtxSourceHkdf.initialResponse fixed.crypto request)

def pending (beacon : Bool) (root : RootOutput) : pqxdh.concrete.InitialRatchetKdfPending :=
  if beacon then beaconPending (PqxdhRootTableInitialization.rootArray root)
  else serverPending (PqxdhRootTableInitialization.rootArray root)

noncomputable def kernel (beacon : Bool) (root : RootOutput) : OracleComp (Spec base) (RustM ConcreteRatchetKernel) := do
  let response ← initial (pending beacon root).request
  pure (pqxdh.concrete.resume_initial_ratchet_kdf (pending beacon root) response)

/-- Adding the private initializer capability preserves each original callback and its entire original effect. -/
theorem source_original (fixed : FixedHkdfSha512NoSaltSource) : source fixed ∘ₛ (original (base := base)) = (fun query => liftM (base.query query)) := by
  funext query
  exact simulateQ_spec_query _ _

/-- The source response at the actual extracted request reconstructs the exact original role initializer, including its complete RustM result. -/
theorem kernel_source (fixed : FixedHkdfSha512NoSaltSource) (beacon : Bool) (root : RootOutput) :
    simulateQ (source (base := base) fixed) (kernel beacon root) =
      pure (PqxdhRootTableInitialization.initialKernelRun fixed beacon root) := by
  cases beacon <;> simp [kernel, initial, pending, source, OracleSpec.query,
    PqxdhRootTableInitialization.initialKernelRun, initializeServer_eq, initializeBeacon_eq]
  all_goals rfl

/-- Every original adaptive callback program is retained verbatim when the private initializer interface is interpreted by the actual source. -/
theorem original_program (fixed : FixedHkdfSha512NoSaltSource) (work : OracleComp base Result) :
    simulateQ (source fixed) (simulateQ original work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, original, ih]
      rfl

/-- The Server and Beacon request the identical input and label; orientation changes only the extracted reply projection. -/
theorem same_request (root : RootOutput) : (pending false root).request = (pending true root).request := rfl

/-- Each attempted extracted initializer consumes one complete64 response from the shared private capability. -/
theorem kernel_total (beacon : Bool) (root : RootOutput) :
    (kernel (base := base) beacon root).IsTotalQueryBound 1 := by
  exact (isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨by decide, fun _ => by trivial⟩

end BeaconcryptCore.Computational.PqxdhInitialResponseService

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseService.source_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseService.source_original

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseService.kernel_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseService.kernel_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseService.original_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseService.original_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseService.same_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseService.same_request

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialResponseService.kernel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialResponseService.kernel_total
