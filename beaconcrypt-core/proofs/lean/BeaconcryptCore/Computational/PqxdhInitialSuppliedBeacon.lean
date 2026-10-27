import BeaconcryptCore.Computational.PqxdhInitialReplyErasure

/-!
The actual shared Beacon initializer is followed by the original application getter, optional raw receive, sequence-one and binding checks. Supplying its one64-byte response produces that same complete continuation without retaining the root. All raw callbacks and private poststate remain original. The root label/cache and target-only substitution are separate consumers of this concrete source no-use law.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon
open PqxdhInitialRatchetComplementarity PqxdhInitialReplyErasure PqxdhSecretInputKdf
open PqxdhBeaconPhase2Shared
variable {Response Shared Result : Type}

noncomputable def supplied (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    QueryImpl (TailSpec Response Shared) (OracleComp (TailSpec Response Shared))
  | .inr (.initial _) => pure response
  | query => (TailSpec Response Shared).query query

noncomputable def afterInitial (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    OracleComp (TailSpec Response Shared) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let kernel := PqxdhBeaconPhase2Publication.normalInitial
    (beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) response
  let raw ← (TailSpec Response Shared).query (.inr (.application pending.response))
  match raw with
  | none => pure none
  | some raw => do
      let result ← simulateQ rawLift (simulateQ RawCtxSourceOpen.nativeAdapter
        ((RawCtxWholeOwner.rawReceive decode raw).run (PqxdhBeaconPhase2Publication.localOwner (clearedMetadata pending.metadata) kernel)))
      pure (PqxdhBeaconPhase2Publication.afterOpening (clearedMetadata pending.metadata) result.2.owner.kernel result.1)

/-- Replacing only the initializer reply retains every original native raw callback and its complete returned value. -/
theorem raw_forward (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    supplied (Response := Response) (Shared := Shared) response ∘ₛ rawLift = rawLift := by
  funext query
  simp [QueryImpl.compose, rawLift, supplied, OracleSpec.query]

/-- The complete actual shared Beacon continuation after its supplied64 response omits the root and retains the original application, raw-opening, sequence-one, binding and staged-publication behavior. -/
theorem afterRoot_supplied (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (root : Std.Array Std.U8 32#usize) (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    simulateQ (supplied response) (afterRoot decode pending root) = afterInitial decode pending response := by
  unfold afterRoot afterInitial
  simp only [simulateQ_bind, simulateQ_spec_query, supplied, pure_bind]
  rw [beacon_kernel_root_unused root (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)) response]
  apply bind_congr
  intro raw
  cases raw with
  | none => rfl
  | some raw =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [← QueryImpl.simulateQ_compose (supplied response) rawLift, raw_forward]

/-- Interpreting the concrete root-free Beacon continuation preserves the entire shared state and arbitrary complete outside continuation, including optional rejection. -/
theorem afterRoot_complete {A Out : Type}
    (handler : QueryImpl (TailSpec Response Shared) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (root : Std.Array Std.U8 32#usize) (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (state : A) (next : Option PqxdhBeaconPhase2Publication.Staged × A → ProbComp Out) :
    ((simulateQ (handler ∘ₛ supplied response) (afterRoot decode pending root)).run state >>= next) =
      ((simulateQ handler (afterInitial decode pending response)).run state >>= next) := by
  rw [QueryImpl.simulateQ_compose, afterRoot_supplied]

end BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.raw_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.raw_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.afterRoot_supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.afterRoot_supplied

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.afterRoot_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon.afterRoot_complete
