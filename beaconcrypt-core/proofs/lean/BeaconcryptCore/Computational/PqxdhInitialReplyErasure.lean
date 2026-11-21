import BeaconcryptCore.Computational.PqxdhInitialResponseCache

/-!
The actual extracted initializer consumes its root only to request a64-byte reply. Once that reply is supplied, both role constructors omit the root. The response-supplying interpreter preserves every unrelated callback. These source no-use statements are helpers for concrete Server and Beacon continuations; they do not yet establish a complete legal initializer observer or permit root-containing Ready/cache values as public context.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialReplyErasure
open PqxdhInitialResponseService PqxdhInitialRatchetComplementarity
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι Result : Type} {base : OracleSpec ι}

/-- For either actual role, every byte of the consumed initializer response determines the same full extracted kernel result regardless of the pending root field. -/
theorem kernel_root_unused (role : Bool) (left right : RootOutput)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    pqxdh.concrete.resume_initial_ratchet_kdf (pending role left) response =
      pqxdh.concrete.resume_initial_ratchet_kdf (pending role right) response := by
  cases role <;> rfl

/-- The normalized actual Beacon initializer has the same entire kernel for every root when its complete typed64-byte response is fixed. -/
theorem beacon_kernel_root_unused (left right : Std.Array Std.U8 32#usize)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    PqxdhBeaconPhase2Publication.normalInitial (beaconPending left) response =
      PqxdhBeaconPhase2Publication.normalInitial (beaconPending right) response := by
  have same : pqxdh.concrete.resume_initial_ratchet_kdf (beaconPending left) response =
      pqxdh.concrete.resume_initial_ratchet_kdf (beaconPending right) response := rfl
  simpa only [PqxdhBeaconPhase2Publication.normalInitial_exact, RustM.ok.injEq] using same

def supplied (response : pqxdh.concrete.InitialRatchetKdfResponse) : QueryImpl (Spec base) (OracleComp base)
  | .inl query => base.query query
  | .inr _ => pure response

def kernelOf (role : Bool) (response : pqxdh.concrete.InitialRatchetKdfResponse) : RustM ConcreteRatchetKernel :=
  pqxdh.concrete.resume_initial_ratchet_kdf (pending role (List.Vector.replicate 32 0)) response

/-- Supplying only a private initializer reply preserves every other original adaptive callback and all of its effects. -/
theorem original_program (response : pqxdh.concrete.InitialRatchetKdfResponse) (work : OracleComp base Result) :
    simulateQ (supplied response) (simulateQ original work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, original, ih]
      rfl

/-- The actual private initializer callback reconstructs a root-free complete role kernel from its response alone, without changing the callback position. -/
theorem kernel_supplied (response : pqxdh.concrete.InitialRatchetKdfResponse) (role : Bool) (root : RootOutput) :
    simulateQ (supplied (base := base) response) (kernel role root) = pure (kernelOf role response) := by
  simp [kernel, initial, supplied, OracleSpec.query, kernelOf,
    kernel_root_unused role root (List.Vector.replicate 32 0)]

end BeaconcryptCore.Computational.PqxdhInitialReplyErasure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReplyErasure.kernel_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReplyErasure.kernel_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReplyErasure.beacon_kernel_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReplyErasure.beacon_kernel_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReplyErasure.original_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReplyErasure.original_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReplyErasure.kernel_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReplyErasure.kernel_supplied
