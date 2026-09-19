import BeaconcryptCore.Computational.PqxdhInitialGenericBeacon

/-!
The generic first Beacon receive is interpreted by the exact original native opening callbacks and optional64-byte initializer response. The complete fused source owner, including preparation and inactive phases, has the same output and entire native state under this interpretation. This is an operational source equation under any lawful ambient monad; mutable shared effects are not replaced by a fixed backend or a security premise.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared
variable {Kernel I D K X Response Shared : Type}

def nativeStaged (interpret : Kernel → ConcreteRatchetKernel)
    (staged : PqxdhInitialGenericBeacon.Staged Kernel) : PqxdhBeaconPhase2Publication.Staged :=
  ⟨staged.authenticated, staged.associatedData, interpret staged.kernel, staged.opened⟩

/-- Exact sequence-one and registration checks retain the same staged native fields. -/
theorem opening_native (interpret : Kernel → ConcreteRatchetKernel)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : Kernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    PqxdhBeaconPhase2Publication.afterOpening candidate (interpret kernel) reply =
      (PqxdhInitialGenericBeacon.afterOpening candidate kernel reply).map (nativeStaged interpret) := by
  cases reply with
  | none => rfl
  | some opened =>
      simp only [PqxdhBeaconPhase2Publication.afterOpening, PqxdhInitialGenericBeacon.afterOpening]
      split
      · rfl
      · split
        · split <;> simp_all only [Option.map_none, Option.map_some, nativeStaged]
        · rfl

/-- Abort and publication return the same plaintext and full concrete Beacon state. -/
theorem finish_native (interpret : Kernel → ConcreteRatchetKernel)
    (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K)
    (staged : Option (PqxdhInitialGenericBeacon.Staged Kernel)) :
    PqxdhBeaconPhase2Publication.finish control (nativeBeacon interpret state)
      (staged.map (nativeStaged interpret)) =
    Prod.map id (nativeBeacon interpret) (PqxdhInitialGenericBeacon.finish control state staged) := by
  cases staged with
  | none => rfl
  | some staged =>
      simp only [PqxdhBeaconPhase2Publication.finish, PqxdhInitialGenericBeacon.finish,
        Option.map_some, nativeStaged, nativeBeacon]
      split
      · rfl
      · split <;> rfl

section Effects
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

noncomputable def calls (raw : QueryImpl RawCtxSourceOpen.NativeSpec m) :
    RawCtxChainOwner.Calls ConcreteRatchetKernel m where
  receive kernel target context := simulateQ ((raw ∘ₛ RawCtxSourceOpen.nativeAdapter) ∘ₛ RawCtxWholeOwner.adapter)
    (RawCtxOwnerOracle.receive kernel target context)
  -- The first-receive owner has no send branch; this field is never executed.
  send kernel _ := pure (kernel, none)

noncomputable def initial (handler : QueryImpl (PqxdhInitialFusedBeacon.Spec Response Shared) m)
    (secrets : Secrets Shared) : m (Option ConcreteRatchetKernel) :=
  Option.map (PqxdhBeaconPhase2Publication.normalInitial
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)))) <$>
      handler (.inr secrets)

/-- The generic receive call is the complete original native receive interpreter, with all shared effects retained. -/
theorem raw_native (rawImpl : QueryImpl RawCtxSourceOpen.NativeSpec m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxChainOwner.State ConcreteRatchetKernel Unit) :
    simulateQ (rawImpl ∘ₛ RawCtxSourceOpen.nativeAdapter)
      ((RawCtxWholeOwner.rawReceive decode raw).run (RawCtxChainOwner.nativeState id state)) =
    Prod.map id (RawCtxChainOwner.nativeState id) <$>
      (RawCtxChainOwner.rawReceive (calls rawImpl) decode raw).run state := by
  apply RawCtxChainOwner.rawReceive_native
  intro entry target context
  change _ = id <$> _
  exact (id_map _).symm

/-- The original response getter and complete first receive coincide with the generic concrete-kernel continuation. -/
theorem afterInitial_native
    (handler : QueryImpl (PqxdhInitialFusedBeacon.Spec Response Shared) m)
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    simulateQ handler (PqxdhInitialFusedBeacon.afterInitial decode pending response) =
      Option.map (nativeStaged id) <$>
        PqxdhInitialGenericBeacon.afterInitial (calls (fun q => handler (.inl (.inl q))))
          (fun reply => handler (.inl (.inr reply))) decode pending
          (PqxdhBeaconPhase2Publication.normalInitial
            (PqxdhInitialRatchetComplementarity.beaconPending
              (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))) response) := by
  simp only [PqxdhInitialFusedBeacon.afterInitial, PqxdhInitialGenericBeacon.afterInitial,
    simulateQ_bind, simulateQ_spec_query, map_bind]
  apply bind_congr
  intro raw
  cases raw with
  | none => simp only [simulateQ_pure, map_pure, Option.map_none]
  | some raw =>
      dsimp only
      simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
      have forwarded : handler ∘ₛ PqxdhInitialFusedBeacon.rawLift =
          (fun q => handler (.inl (.inl q))) := by
        funext query
        simp [QueryImpl.compose, PqxdhInitialFusedBeacon.rawLift, OracleSpec.query]
      rw [← QueryImpl.simulateQ_compose handler PqxdhInitialFusedBeacon.rawLift, forwarded,
        ← QueryImpl.simulateQ_compose]
      have localState : ∀ kernel : ConcreteRatchetKernel,
          PqxdhBeaconPhase2Publication.localOwner (clearedMetadata pending.metadata) kernel =
          RawCtxChainOwner.nativeState id (PqxdhInitialGenericBeacon.localOwner (clearedMetadata pending.metadata) kernel) := fun _ => rfl
      rw [localState, raw_native]
      simp only [bind_map_left]
      apply bind_congr
      intro result
      exact congrArg pure (opening_native id _ _ _)

/-- The optional64 response is interpreted at the original private callback and the whole remaining native tail is unchanged. -/
theorem tail_native (handler : QueryImpl (PqxdhInitialFusedBeacon.Spec Response Shared) m)
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    simulateQ handler (PqxdhInitialFusedBeacon.tail decode pending) =
      Option.map (nativeStaged id) <$>
        PqxdhInitialGenericBeacon.tail (calls (fun q => handler (.inl (.inl q))))
          (fun reply => handler (.inl (.inr reply))) (initial handler) decode pending := by
  simp only [PqxdhInitialFusedBeacon.tail, PqxdhInitialGenericBeacon.tail, initial,
    simulateQ_bind, simulateQ_spec_query, bind_map_left, map_bind]
  apply bind_congr
  intro response
  cases response with
  | none => simp only [Option.map_none, simulateQ_pure, map_pure]
  | some response => exact afterInitial_native handler decode pending response

/-- The full fused native owner has exactly the generic concrete-kernel output and projected complete state for every phase and ambient interpreter. -/
theorem owner_native
    (handler : QueryImpl (PqxdhInitialFusedOwner.Spec I D K X Response Shared) m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : BeaconState ConcreteRatchetKernel I D K) :
    simulateQ handler (PqxdhInitialFusedOwner.owner decode raw (nativeBeacon id state)) =
      Prod.map id (nativeBeacon id) <$>
        PqxdhInitialGenericBeacon.owner (fun q => handler (.inl q))
          (calls (fun q => handler (.inr (.inl (.inl q)))))
          (fun reply => handler (.inr (.inl (.inr reply))))
          (initial (fun q => handler (.inr q))) decode raw state := by
  have preparation : handler ∘ₛ PqxdhInitialFusedOwner.preLift = (fun q => handler (.inl q)) := by
    funext query
    simp [QueryImpl.compose, PqxdhInitialFusedOwner.preLift, OracleSpec.query]
  have continuation : handler ∘ₛ PqxdhInitialFusedOwner.tailLift = (fun q => handler (.inr q)) := by
    funext query
    simp [QueryImpl.compose, PqxdhInitialFusedOwner.tailLift, OracleSpec.query]
  unfold PqxdhInitialFusedOwner.owner PqxdhInitialGenericBeacon.owner
  simp only [nativeBeacon]
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [mapPhase, simulateQ_bind, map_bind]
    rw [← QueryImpl.simulateQ_compose, preparation]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [simulateQ_pure, map_pure]; rfl
    | some prepared =>
      dsimp only
      simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
      rw [← QueryImpl.simulateQ_compose, continuation, tail_native]
      simp only [bind_map_left]
      apply bind_congr
      intro staged
      exact congrArg pure (finish_native id control state staged)
  all_goals simp only [mapPhase, simulateQ_pure, map_pure, Prod.map, nativeBeacon, phase, id_eq]

/-- Any private kernel representation satisfying the exact receive and initializer equations yields the full original fused owner, without a whole-owner correspondence premise. -/
theorem owner_mapped (interpret : Kernel → ConcreteRatchetKernel)
    (handler : QueryImpl (PqxdhInitialFusedOwner.Spec I D K X Response Shared) m)
    (kernelCalls : RawCtxChainOwner.Calls Kernel m)
    (receiveMap : ∀ entry target context,
      (calls (fun q => handler (.inr (.inl (.inl q))))).receive (interpret entry) target context =
        Prod.map interpret id <$> kernelCalls.receive entry target context)
    (initialImpl : Secrets Shared → m (Option Kernel))
    (initialMap : ∀ secrets, initial (fun q => handler (.inr q)) secrets = Option.map interpret <$> initialImpl secrets)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) :
    simulateQ handler (PqxdhInitialFusedOwner.owner decode raw (nativeBeacon interpret state)) =
      Prod.map id (nativeBeacon interpret) <$>
        PqxdhInitialGenericBeacon.owner (fun q => handler (.inl q)) kernelCalls
          (fun reply => handler (.inr (.inl (.inr reply)))) initialImpl decode raw state := by
  have projection : nativeBeacon id (mapBeacon interpret state) = nativeBeacon interpret state :=
    beacon_compose interpret id state
  rw [← projection, owner_native, PqxdhInitialGenericBeacon.owner_map interpret _ kernelCalls _ receiveMap _ initialImpl _ initialMap,
    Functor.map_map]
  apply congrArg (fun f => f <$> _)
  funext result
  exact congrArg (fun state => (result.1, state)) (beacon_compose interpret id result.2)

end Effects
end BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.opening_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.opening_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.finish_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.raw_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.afterInitial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.afterInitial_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.tail_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.tail_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.owner_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.owner_mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative.owner_mapped
