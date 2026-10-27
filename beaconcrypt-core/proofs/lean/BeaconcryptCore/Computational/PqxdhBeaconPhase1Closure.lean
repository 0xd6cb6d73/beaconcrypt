import BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization
import BeaconcryptCore.Computational.PqxdhLivePhase1State
import BeaconcryptCore.Computational.PqxdhLivePhase1Bundle

/-!
The actual native Phase1 helper calls cannot reopen an established or aborted Beacon. The explicit new-one-time helper still executes its original generator before rejecting; its complete effects and random-query cost remain present. Bundle generation rejects a terminal phase before any generator, signature or writer call. These source lifetime facts do not identify distinct owners or assume distinct key bytes.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure
open RawCtxGenericRoleStorage PqxdhBeaconSingleInitialization
variable {Kernel I D K : Type}

def NativeClosed (state : RawCtxBeaconLifecycle.State I D K) : Prop :=
  Closed (fromBeacon id state)

/-- Terminal registration state is independent of the private ratchet representation, with no inverse or injectivity premise. -/
theorem native_iff (interpret : Kernel → ConcreteRatchetKernel) (state : BeaconState Kernel I D K) :
    NativeClosed (nativeBeacon interpret state) ↔ Closed state := by
  cases phase : state.beacon.phase <;> simp only [NativeClosed, Closed, fromBeacon, nativeBeacon, mapPhase, phase]

/-- Every optional generated pair is discarded by the actual helper when its same owner is already terminal. -/
theorem newCoins_closed (generated : Option D) (state : RawCtxBeaconLifecycle.State I D K)
    (closed : NativeClosed state) : PqxdhLivePhase1State.newCoins generated state = (none, state) := by
  cases phase : state.beacon.phase <;> simp_all only [NativeClosed, Closed, fromBeacon, mapPhase]
  all_goals cases generated <;> simp only [PqxdhLivePhase1State.newCoins, phase]

/-- Terminal rejection does not remove the source helper's generator call or any of its private effects. -/
theorem newOneTime_closed (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) :
    PqxdhLivePhase1State.newOneTime state = (do
      let _ ← (PqxdhLivePhase1State.GenerateSpec D).query ()
      pure (none, state)) := by
  unfold PqxdhLivePhase1State.newOneTime
  apply bind_congr
  intro generated
  rw [newCoins_closed generated state closed]

/-- The rejected helper retains the generator's actual complete auxiliary poststate, including failure and randomness. -/
theorem newOneTime_source {A : Type}
    (generate : QueryImpl (PqxdhLivePhase1State.GenerateSpec D) (StateT A ProbComp))
    (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) (before : A) :
    (simulateQ generate (PqxdhLivePhase1State.newOneTime state)).run before =
      (fun result => ((none, state), result.2)) <$> (generate ()).run before := by
  rw [newOneTime_closed state closed]
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]

/-- An inactive helper spends the complete original generator bill; its unchanged owner does not make the actual work free. -/
theorem newOneTime_uniform {A : Type}
    (generate : QueryImpl (PqxdhLivePhase1State.GenerateSpec D) (StateT A ProbComp))
    (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) (before : A) (qGenerate : Nat) :
    ((simulateQ generate (PqxdhLivePhase1State.newOneTime state)).run before).IsTotalQueryBound qGenerate ↔
      ((generate ()).run before).IsTotalQueryBound qGenerate := by
  rw [newOneTime_source generate state closed before]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

/-- Deleting one-time material on a terminal owner preserves the entire original owner. -/
theorem deleteOneTime_closed (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) :
    PqxdhLivePhase1State.deleteOneTime state = state := by
  cases phase : state.beacon.phase <;> simp_all only [NativeClosed, Closed, fromBeacon, mapPhase]
  all_goals simp only [PqxdhLivePhase1State.deleteOneTime, phase]

/-- KEM deletion cannot reopen an established or aborted registration. -/
theorem deleteKem_closed (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) :
    PqxdhLivePhase1State.deleteKem state = state := by
  cases phase : state.beacon.phase <;> simp_all only [NativeClosed, Closed, fromBeacon, mapPhase]
  all_goals simp only [PqxdhLivePhase1State.deleteKem, phase]

/-- The actual Phase1 bundle call rejects a terminal owner before all generation, signing and writing. -/
theorem bundle_closed (projection : PqxdhLivePhase1Bundle.Public I D K)
    (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) :
    PqxdhLivePhase1Bundle.bundle projection state = pure (none, state) := by
  cases phase : state.beacon.phase <;> simp_all only [NativeClosed, Closed, fromBeacon, mapPhase]
  all_goals simp only [PqxdhLivePhase1Bundle.bundle, phase]

/-- Inactive bundle rejection makes zero generator, signing and writer requests at the actual service interface. -/
theorem bundle_bound (projection : PqxdhLivePhase1Bundle.Public I D K)
    (state : RawCtxBeaconLifecycle.State I D K) (closed : NativeClosed state) :
    (PqxdhLivePhase1Bundle.bundle projection state).IsTotalQueryBound 0 := by
  rw [bundle_closed projection state closed]
  trivial

end BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.native_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.native_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newCoins_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newCoins_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_source

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.newOneTime_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.deleteOneTime_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.deleteOneTime_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.deleteKem_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.deleteKem_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.bundle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.bundle_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase1Closure.bundle_bound
