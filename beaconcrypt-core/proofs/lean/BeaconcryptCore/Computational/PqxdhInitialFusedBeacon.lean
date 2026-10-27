import BeaconcryptCore.Computational.PqxdhInitialSuppliedBeacon

/-!
The actual adjacent private Beacon root and optional initializer callbacks are combined into a service returning only the optional complete64-byte response. Its executable continuation has no root-valued reply interface. The native interpreter performs the original root call, rejection, initializer and complete raw continuation in source order; this is an exact private-interface factorization, not a secrecy assumption.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFusedBeacon
open PqxdhBeaconPhase2Shared PqxdhInitialRatchetComplementarity PqxdhInitialReplyErasure
variable {Response Shared Result : Type}

abbrev DataSpec (Response : Type) := RawCtxSourceOpen.NativeSpec + (Response →ₒ Option PqxdhBeaconPhase2Preparation.Bytes)
abbrev Spec (Response Shared : Type) := DataSpec Response + (Secrets Shared →ₒ Option pqxdh.concrete.InitialRatchetKdfResponse)

def rawLift : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp (Spec Response Shared)) :=
  fun query => (Spec Response Shared).query (.inl (.inl query))

noncomputable def native : QueryImpl (Spec Response Shared) (OracleComp (TailSpec Response Shared))
  | .inl (.inl query) => (TailSpec Response Shared).query (.inl query)
  | .inl (.inr response) => (TailSpec Response Shared).query (.inr (.application response))
  | .inr secrets => do
      let root ← (TailSpec Response Shared).query (.inr (.root secrets))
      match root with
      | none => pure none
      | some root => some <$> (TailSpec Response Shared).query (.inr (.initial (beaconPending root).request))

noncomputable def afterInitial (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    OracleComp (Spec Response Shared) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let kernel := PqxdhBeaconPhase2Publication.normalInitial
    (beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) response
  let raw ← (Spec Response Shared).query (.inl (.inr pending.response))
  match raw with
  | none => pure none
  | some raw => do
      let result ← simulateQ rawLift (simulateQ RawCtxSourceOpen.nativeAdapter
        ((RawCtxWholeOwner.rawReceive decode raw).run (PqxdhBeaconPhase2Publication.localOwner (clearedMetadata pending.metadata) kernel)))
      pure (PqxdhBeaconPhase2Publication.afterOpening (clearedMetadata pending.metadata) result.2.owner.kernel result.1)

noncomputable def tail (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    OracleComp (Spec Response Shared) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let response ← (Spec Response Shared).query (.inr pending.root)
  match response with
  | none => pure none
  | some response => afterInitial decode pending response

/-- The root-free interface preserves every original native raw operation and its exact reply. -/
theorem raw_native : native (Response := Response) (Shared := Shared) ∘ₛ rawLift = PqxdhBeaconPhase2Shared.rawLift := by
  funext query
  simp [QueryImpl.compose, rawLift, native, PqxdhBeaconPhase2Shared.rawLift, OracleSpec.query]

/-- The fused interface's response-only continuation is exactly the concrete root-erased application and raw-opening tail. -/
theorem afterInitial_native (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    simulateQ native (afterInitial decode pending response) =
      PqxdhInitialSuppliedBeacon.afterInitial decode pending response := by
  unfold afterInitial PqxdhInitialSuppliedBeacon.afterInitial
  simp only [simulateQ_bind, simulateQ_spec_query, native]
  apply bind_congr
  intro raw
  cases raw with
  | none => rfl
  | some raw =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [← QueryImpl.simulateQ_compose native rawLift, raw_native]

/-- The actual initializer request stays in place, and its full remaining native continuation reads only the returned64-byte response. -/
theorem afterRoot_response (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (root : Std.Array Std.U8 32#usize) :
    PqxdhBeaconPhase2Shared.afterRoot decode pending root = (do
      let response ← (TailSpec Response Shared).query (.inr (.initial (beaconPending root).request))
      PqxdhInitialSuppliedBeacon.afterInitial decode pending response) := by
  unfold PqxdhBeaconPhase2Shared.afterRoot PqxdhInitialSuppliedBeacon.afterInitial
  apply bind_congr
  intro response
  rw [beacon_kernel_root_unused root (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)) response]
  rfl

/-- The fused response-only Beacon tail executes exactly the original root callback, optional rejection, initializer and complete receive/publication continuation in source order. -/
theorem tail_native (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    simulateQ native (tail decode pending) = PqxdhBeaconPhase2Shared.tail decode pending := by
  unfold tail PqxdhBeaconPhase2Shared.tail
  simp only [simulateQ_bind, simulateQ_spec_query, native, bind_assoc]
  apply bind_congr
  intro root
  cases root with
  | none => rfl
  | some root =>
      simp only [bind_map_left, afterInitial_native, afterRoot_response]
      rfl

end BeaconcryptCore.Computational.PqxdhInitialFusedBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.raw_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.afterInitial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.afterInitial_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.afterRoot_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.afterRoot_response

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.tail_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedBeacon.tail_native
