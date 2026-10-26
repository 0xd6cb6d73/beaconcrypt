import BeaconcryptCore.Computational.PqxdhInitialSelectedService

/-!
Lift actual shared primitive computations into the current Beacon's complete ambient state: shared primitive state, private identity state and the separate shared root cache. The lift preserves every source query, optional reply and state update while retaining the two unrelated state components. These are literal monadic program equations, not distributional replacements.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient
variable {A N C α β ι : Type} {spec : OracleSpec ι}
abbrev Base (A : Type) := StateT (RawCtxSharedPrimitive.SharedState A) ProbComp
abbrev Ambient (A N C : Type) := StateT (RawCtxSharedPrimitive.SharedState A × N) (StateT C ProbComp)

def lift (work : Base A α) : Ambient A N C α := fun state cache =>
  (fun result => ((result.1, (result.2, state.2)), cache)) <$> work state.1

/-- The complete ambient lift preserves pure replies and all three state components. -/
theorem lift_pure (value : α) : lift (pure value : Base A α) = (pure value : Ambient A N C α) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source callback sequencing and every intermediate shared state survive the full ambient lift. -/
theorem lift_bind (work : Base A α) (next : α → Base A β) :
    lift (work >>= next) = (lift work >>= fun value => lift (N := N) (C := C) (next value)) := by
  funext state cache
  change (fun result => ((result.1, (result.2, state.2)), cache)) <$>
      (work state.1 >>= fun first => next first.1 first.2) =
    (((fun result => ((result.1, (result.2, state.2)), cache)) <$> work state.1) >>=
      fun first => (fun result => ((result.1, (result.2, first.1.2.2)), first.2)) <$>
        next first.1.1 first.1.2.1)
  simp only [map_bind, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- The full ambient lift preserves reply maps without changing local work or any state component. -/
theorem lift_map (f : α → β) (work : Base A α) :
    lift (f <$> work) = f <$> lift (N := N) (C := C) work := by
  funext state cache
  change (fun result => ((result.1, (result.2, state.2)), cache)) <$>
      (f <$> work).run state.1 = ((f <$> lift (N := N) (C := C) work).run state).run cache
  rw [StateT.run_map, StateT.run_map, StateT.run_map]
  change (fun result => ((result.1, (result.2, state.2)), cache)) <$>
      ((fun result => (f result.1, result.2)) <$> work.run state.1) =
    (fun result => ((f result.1.1, result.1.2), result.2)) <$>
      ((fun result => ((result.1, (result.2, state.2)), cache)) <$> work.run state.1)
  simp only [Functor.map_map]

/-- An entire original adaptive oracle program commutes with the same full-state callback lift. -/
theorem simulate_lift (impl : QueryImpl spec (Base A)) (client : OracleComp spec α) :
    simulateQ (fun query => lift (N := N) (C := C) (impl query)) client = lift (simulateQ impl client) := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lift_bind, ih]

/-- Adapter composition commutes with the same full-state lift, so no source callback effects disappear at interface boundaries. -/
theorem compose_lift {κ : Type} {other : OracleSpec κ}
    (impl : QueryImpl spec (Base A)) (adapter : QueryImpl other (OracleComp spec)) :
    (fun query => lift (N := N) (C := C) (impl query)) ∘ₛ adapter =
      (fun query => lift ((impl ∘ₛ adapter) query)) := by
  funext query
  exact simulate_lift impl (adapter query)

def liftCalls {Kernel : Type} (calls : RawCtxChainOwner.Calls Kernel (Base A)) :
    RawCtxChainOwner.Calls Kernel (Ambient A N C) where
  receive kernel target context := lift (calls.receive kernel target context)
  send kernel context := lift (calls.send kernel context)

/-- The actual native receive interpreter keeps all original shared effects when run inside the current Beacon's extra state and root cache. -/
theorem receive_lift (raw : QueryImpl RawCtxSourceOpen.NativeSpec (Base A))
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (sequence : Aeneas.Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (PqxdhInitialGenericBeaconNative.calls (fun query => lift (N := N) (C := C) (raw query))).receive kernel sequence context =
      lift ((PqxdhInitialGenericBeaconNative.calls raw).receive kernel sequence context) := by
  simp only [PqxdhInitialGenericBeaconNative.calls, compose_lift, simulate_lift]

/-- The concrete retained-parent receive equation holds inside the complete current ambient state, including its private identity and shared root cache. -/
theorem selected_receive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (entry : RawCtxSelectedParentEntry.Entry) (target : PqxdhSecretInputKdf.RootOutput)
    (kernel : RawCtxSelectedChain.Kernel) (sequence : Aeneas.Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (PqxdhInitialGenericBeaconNative.calls (fun query => lift (N := N) (C := C)
      (PqxdhInitialSelectedBeacon.raw (A := A) source writer prior entry target query))).receive
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) sequence context =
      Prod.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) id <$>
        (liftCalls (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target))).receive kernel sequence context := by
  rw [receive_lift, PqxdhInitialSelectedBeacon.selected_receive, lift_map]
  rfl

end BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.lift_map
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.simulate_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.simulate_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.compose_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.compose_lift
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.receive_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.receive_lift
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.selected_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.selected_receive
